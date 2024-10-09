#include "autarky.h"
#include "backtrack.h"
#include "decide.h"
#include "internal.h"
#include "logging.h"
#include "print.h"
#include "rephase.h"
#include "report.h"
#include "terminate.h"
#include "walk.h"

#include <inttypes.h>
#include <string.h>
#include <math.h>

void
kissat_reset_best_assigned (kissat * solver)
{
  if (!solver->best_assigned)
    return;
  kissat_extremely_verbose (solver,
			    "resetting best assigned trail height %u to 0",
			    solver->best_assigned);
  solver->best_assigned = 0;
}

void
kissat_reset_target_assigned (kissat * solver)
{
  if (!solver->target_assigned)
    return;
  kissat_extremely_verbose (solver,
			    "resetting target assigned trail height %u to 0",
			    solver->target_assigned);
  solver->target_assigned = 0;
}

bool
kissat_rephasing (kissat * solver)
{
  if (!solver->enabled.rephase)
    return false;
  if (!solver->stable)
    return false;
  return CONFLICTS > solver->limits.rephase.conflicts;
}

static char
rephase_best (kissat * solver)
{
  const value *const best = solver->phases.best;
  const value *const end_of_best = best + VARS;
  value const *b;

  value *const saved = solver->phases.saved;
  value *s;

  value tmp;

  for (s = saved, b = best; b != end_of_best; s++, b++)
    if ((tmp = *b))
      *s = tmp;

  INC (rephased_best);

  return 'B';
}

static char
rephase_conflict (kissat * solver)
{
  const value *const conflict = solver->phases.conflict;
  const value *const end_of_conflict = conflict + VARS;
  value const *b;

  value *const saved = solver->phases.saved;
  value *s;

  value tmp;

  for (s = saved, b = conflict; b != end_of_conflict; s++, b++)
    if ((tmp = *b))
      *s = tmp;

  INC (rephased_conflict);

  return 'C';
}

static char
rephase_flipped (kissat * solver)
{
  assert (GET_OPTION (rephaseflipped));
  const value initial_phase = INITIAL_PHASE;
  for (all_phases (saved, p))
    *p *= -1;
  INC (rephased_flipped);
  return 'F';
}

static char
rephase_original (kissat * solver)
{
  assert (GET_OPTION (rephaseoriginal));
  const value initial_phase = INITIAL_PHASE;
  for (all_phases (saved, p))
    *p = initial_phase;
  INC (rephased_original);
  return 'O';
}

static char
rephase_inverted (kissat * solver)
{
  assert (GET_OPTION (rephaseinverted));
  const value inverted_initial_phase = -INITIAL_PHASE;
  for (all_phases (saved, p))
    *p = inverted_initial_phase;
  INC (rephased_inverted);
  return 'I';
}

static char
rephase_walking (kissat * solver)
{
  assert (GET_OPTION (rephasewalking));
  assert (kissat_walking (solver));
  STOP (rephase);
  kissat_walk (solver);
  START (rephase);
  INC (rephased_walking);
  return 'W';
}

static char
reset_phases (kissat * solver)
{
  uint64_t count = solver->rephased.count++;

  const bool inverted = GET_OPTION (rephaseinverted);
  const bool original = GET_OPTION (rephaseoriginal);
  const bool best = GET_OPTION (rephasebest);
  const bool walking = GET_OPTION (rephasewalking) && kissat_walking (solver);

  uint64_t prefix = inverted + original;
  prefix *= GET_OPTION (rephaseprefix);

  char (*functions[6]) (kissat *);
  uint64_t candidates = 0;

#define PUSH1(NAME) \
  if (NAME) \
    { \
      assert (candidates < sizeof functions / sizeof *functions); \
      functions[candidates++] = rephase_ ## NAME; \
    }

#define PUSH3(NAME) \
  if (NAME) \
    { \
      PUSH1 (best); \
      PUSH1 (walking); \
      PUSH1 (NAME); \
    }

  if (count < prefix)
    {
      PUSH1 (original);
      PUSH1 (inverted);
    }
  else
    {
      PUSH3 (original);
      PUSH3 (inverted);
      count -= prefix;
    }

  if (!candidates)
    {
      PUSH1 (best);
      PUSH1 (walking);
    }

  char type;

  // Since 'enabled.rephase' is true one of the rephase methods is enabled.
  // However 'rephasewalking' could be the only one and the derived 'walking'
  // depends also on the size of the formula, i.e., 'kissat_walking' could
  // return 'false'.  As a consequence there is no candidate if only the
  // 'rephasewalking' is true but the formula is too big.
  //
  if (candidates)
    {
      const uint64_t select = count % candidates;
      type = functions[select] (solver);
    }
  else
    type = rephase_best (solver);

#ifndef QUIET
  char const *type_as_string = 0;
  switch (type)
    {
#define REPHASE(NAME, TYPE, INDEX) \
      case TYPE: \
        type_as_string = #NAME; \
	break;
      REPHASES
#undef REPHASE
    }
  assert (type_as_string);
  kissat_phase (solver, "rephase", GET (rephased),
		"%s phases in %s search mode",
		type_as_string, solver->stable ? "stable" : "focused");
#endif
  kissat_extremely_verbose (solver, "remembering last rephase type '%c' at "
			    "%s conflicts", type, FORMAT_COUNT (CONFLICTS));
  solver->rephased.last = type;
  LOG ("copying saved phases as target phases");
  memcpy (solver->phases.target, solver->phases.saved, VARS);
  UPDATE_CONFLICT_LIMIT (rephase, rephased, NLOGNLOGNLOGN, false);
  kissat_reset_target_assigned (solver);
  if (type == 'B')
    kissat_reset_best_assigned (solver);
  return type;
}

/*static char
reset_phases_mab (kissat * solver)
{
    uint64_t count = solver->rephased.count++;

    const bool inverted = GET_OPTION (rephaseinverted);
    const bool original = GET_OPTION (rephaseoriginal);
    const bool best = GET_OPTION (rephasebest);
    const bool walking = GET_OPTION (rephasewalking) && kissat_walking (solver);
    const bool available[4] = {best, original, inverted, walking};
    char (*functions[6]) (kissat *);
    uint64_t candidates = 0;
    uint64_t tail = 0;

#define PUSH1(NAME) \
    { \
      assert (tail < sizeof functions / sizeof *functions); \
      functions[tail++] = rephase_ ## NAME; \
      if (NAME)  {  \
        candidates++;   \
      }   \
    }

    PUSH1(best)
    PUSH1(original)
    PUSH1(inverted)
    PUSH1(walking)

    char type_idx[4] = "BOIW";
    int last = 0;
    for (int i = 0; i < 4; ++i) {
        if (solver->rephased.last == type_idx[i]) {
            last = i;
            break;
        }
    }
    solver->mab_reward[last] += !solver->mab_chosen_tot ? 0 : log2(solver->mab_decisions) / solver->mab_chosen_tot;
    for (all_variables (idx)) solver->mab_chosen[idx] = 0;
    solver->mab_chosen_tot = 0;
    solver->mab_decisions = 0;

    char type;
    unsigned curr_chosen = 0;
    if (!candidates) {
        curr_chosen = 0;
    } else if (count < candidates) {
        for (int i = 0; i < 4; ++i) {
            if (available[i] && !solver->mab_select[i]) {
                curr_chosen = i;
                break;
            }
        }
    } else {
        double ucb[4];
        for (unsigned i = 0; i < solver->mab_num_arms; i++) {
            if (!available[i]) continue;
            ucb[i] = solver->mab_reward[i] / solver->mab_select[i] +
                     sqrt(solver->mabc * log(count + 1) / solver->mab_select[i]);
            if (i != 0 && ucb[i] > ucb[curr_chosen]) curr_chosen = i;
        }
    }
    type = functions[curr_chosen](solver);
    solver->mab_select[curr_chosen]++;

#ifndef QUIET
    char const *type_as_string = 0;
    switch (type)
    {
#define REPHASE(NAME, TYPE, INDEX) \
      case TYPE: \
        type_as_string = #NAME; \
	break;
        REPHASES
#undef REPHASE
    }
    assert (type_as_string);
    kissat_phase (solver, "rephase", GET (rephased),
                  "%s phases in %s search mode",
                  type_as_string, solver->stable ? "stable" : "focused");
#endif
    kissat_extremely_verbose (solver, "remembering last rephase type '%c' at "
                                      "%s conflicts", type, FORMAT_COUNT (CONFLICTS));
    solver->rephased.last = type;
    LOG ("copying saved phases as target phases");
    memcpy (solver->phases.target, solver->phases.saved, VARS);
    UPDATE_CONFLICT_LIMIT (rephase, rephased, NLOGNLOGNLOGN, false);
    kissat_reset_target_assigned (solver);
    if (type == 'B')
        kissat_reset_best_assigned (solver);
    return type;
}
*/

static char
reset_phases_mab (kissat * solver)
{
  uint64_t count = solver->rephased.count++;

  const bool inverted = GET_OPTION (rephaseinverted);
  const bool original = GET_OPTION (rephaseoriginal);
  const bool best = GET_OPTION (rephasebest);
  const bool walking = GET_OPTION (rephasewalking) && kissat_walking (solver);
  const bool conflict = GET_OPTION (rephaseconflict);
  const bool flipped = GET_OPTION (rephaseflipped);

  uint64_t prefix = inverted + original;
  prefix *= GET_OPTION (rephaseprefix);

  char (*functions[12]) (kissat *);
  uint64_t candidates = 0;

#define PUSH1(NAME) \
  if (NAME) \
    { \
      assert (candidates < sizeof functions / sizeof *functions); \
      functions[candidates++] = rephase_ ## NAME; \
    }
    
#define PUSH3(NAME) \
  if (NAME) \
    { \
      PUSH1 (best); \
      PUSH1 (walking); \
      PUSH1 (NAME); \
    }

  if (count < prefix)
    {
      PUSH1 (original);
      PUSH1 (inverted);
     // kissat_phase (solver, "rephase", GET (rephased), "count < prefix; %lu count; %lu candidates;", count, candidates);
    }
  else
    {
      PUSH3 (original);
      PUSH3 (inverted);
      PUSH3 (conflict);
      PUSH3 (flipped);
     // kissat_phase (solver, "rephase", GET (rephased), "count >= prefix; %lu count; %lu candidates;", count, candidates);
    }

  if (!candidates)
    {
      PUSH1 (best);
      PUSH1 (walking);
     // kissat_phase (solver, "rephase", GET (rephased), "candidates == 0; %lu count; %lu candidates;", count, candidates);
    }

  char type;
  uint64_t select = 0;
  unsigned last_arm = 0;
  unsigned last_index = solver->rephased.last_index;
  //bool in_mab = candidates > 2 && (last_index == 2 || last_index == 5 || last_index == 8 || last_index == 12|| last_index == 16 || last_index == 20); 
  bool in_mab = candidates > 2 && (last_index == 2 || last_index == 5 || last_index == 8 || last_index == 11); 
  if (count <= 2) 
    {
      for (all_variables (idx)) solver->mab_chosen[idx] = 0;
      solver->mab_chosen_tot = 0;
      solver->mab_decisions = 0;
      //for (unsigned i = 0; i < solver->mab_num_arms; i++) solver->mab_select[i] = 1;
     // for (unsigned i = 0; i < solver->mab_num_arms; i++) printf("count: %lu; solver->mab_select[%u]: %u", count, i, solver->mab_select[i]); 
    }
  else if (in_mab)
    {
      last_arm = last_index / 3;
      solver->mab_reward[last_arm] += !solver->mab_chosen_tot ? 0 : log2(solver->mab_decisions) / solver->mab_chosen_tot;
      //kissat_phase (solver, "rephase", GET (rephased), "%lu count; %lu candidates; %u last_arm", count, candidates, last_arm);
      for (all_variables (idx)) solver->mab_chosen[idx] = 0;
      solver->mab_chosen_tot = 0;
      solver->mab_decisions = 0;
    }
  
  if (candidates && count < 14)
    {
      select = count >= 2 ? (count - 2) : count;
      if(count == 2 ||  count == 5 || count == 8 || count == 11) solver->mab_select[(count - 2) / 3] = 1;         
    }
  else if (!in_mab)
    {
      select = last_index + 1;
    }
  else 
    { 
      unsigned mab_count = 0;
      for (unsigned i = 0; i < solver->mab_num_arms; i++) mab_count +=  solver->mab_select[i];
      double ucb[4];
      int arm = 0;
      for (unsigned i = 0; i < solver->mab_num_arms; i++)
        {
          ucb[i] = solver->mab_reward[i] / solver->mab_select[i] + sqrt(solver->mabc * log(mab_count + 1) / solver->mab_select[i]);
          if (i != 0 && ucb[i] > ucb[arm]) arm = i;
        }
      select = 3 * arm;  
      solver->mab_select[arm]++;
      //kissat_phase (solver, "rephase", GET (rephased), "MAB: %lu count; %lu candidates; %u last_arm; %lu select", count, candidates, last_arm, select);     
    }
  kissat_phase (solver, "rephase", GET (rephased), "%lu count; %lu candidates; %lu select", count, candidates, select);   
  type = functions[select] (solver);
  solver->rephased.last_index = select;
  //for (unsigned i = 0; i < solver->mab_num_arms; i++) printf("count: %lu; solver->mab_select[%u]: %u", count, i, solver->mab_select[i]);

  //for (unsigned i = 0; i < solver->mab_num_arms; i++) kissat_phase (solver, "rephase", GET (rephased), "solver->mab_select[%u]:%u", i, solver->mab_select[i]);
  
#ifndef QUIET
  char const *type_as_string = 0;
  switch (type)
    {
#define REPHASE(NAME, TYPE, INDEX) \
      case TYPE: \
        type_as_string = #NAME; \
  break;
      REPHASES
#undef REPHASE
    }
  assert (type_as_string);
  kissat_phase (solver, "rephase", GET (rephased),
    "%s phases in %s search mode",
    type_as_string, solver->stable ? "stable" : "focused");
#endif
  kissat_extremely_verbose (solver, "remembering last rephase type '%c' at "
          "%s conflicts", type, FORMAT_COUNT (CONFLICTS));
  solver->rephased.last = type;
  LOG ("copying saved phases as target phases");
  memcpy (solver->phases.target, solver->phases.saved, VARS);
  UPDATE_CONFLICT_LIMIT (rephase, rephased, LINEAR, false);
  kissat_reset_target_assigned (solver);
  if (type == 'B')
    kissat_reset_best_assigned (solver);
  return type;
}

void
kissat_rephase (kissat * solver)
{
  kissat_backtrack_propagate_and_flush_trail (solver);
  assert (!solver->inconsistent);
  kissat_autarky (solver, 'a');
  if (TERMINATED (rephase_terminated_1))
    return;
  START (rephase);
  INC (rephased);
#ifndef QUIET
  const char type =
#endif
    solver->mab ? reset_phases_mab(solver) : reset_phases (solver);
  REPORT (0, type);
  STOP (rephase);
  if (TERMINATED (rephase_terminated_2))
    return;
  kissat_autarky (solver, 'z');
}
