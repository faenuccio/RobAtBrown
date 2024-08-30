import Lean.Elab
import Mathlib.Tactic
import Mathlib.Topology.Basic
-- import LoVe.LoVelib
-- import


/- # LoVe Homework 8 (10 bonus points): Metaprogramming

**This homework is optional!** You do not need to submit anything.
If you do, it will be counted for bonus points.

This homework mainly builds on the 10th lab.
If you are interested in getting a quick feel for metaprogramming,
we strongly recommend the lab *instead* of this homework.

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.

This homework is not autograded.

-/

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Question 1 (10 points): A `safe` Tactic

You will develop a tactic that applies all safe introduction and elimination
rules for the connectives and quantifiers exhaustively. A rule is said to be
__safe__ if, given a provable goal, it always gives rise to provable subgoals.
In addition, we will require that safe rules do not introduce metavariables
(since these can easily be instantiated accidentally with the wrong terms).

You will proceed in three steps.

1.1 (4 points). Using a macro, develop a `safe_intros` tactic that repeatedly
applies the introduction rules for `True`, `∧`, and `↔` and that invokes
`intro _` for `→`/`∀`. The tactic generalizes `intro_and` from the lab. -/

  macro "safe_intros" : tactic =>
  `(tactic| ( repeat'
                first
                | constructor
                | intro _
              ))


theorem abcd (a b c d : Prop) :
  a → ¬ b ∧ (c ↔ d) := by
  safe_intros
  repeat' sorry

    -- ·
    /- The proof state should be roughly as follows:

        case left
        a b c d : Prop
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        a b c d : Prop
        a_1 : a
        a_2 : c
        ⊢ d

        case right.mpr
        a b c d : Prop
        a_1 : a
        a_2 : d
        ⊢ c -/

/- 1.2 (4 points). Develop a `safe_cases` tactic that performs case
distinctions on `False`, `∧` (`And`), and `∃` (`Exists`). The tactic generalizes
`cases_and` from the exercise.

Hints:

* The last argument of `Expr.isAppOfArity` is the number of arguments expected
  by the logical symbol. For example, the arity of `∧` is 2.

* The "or" connective on `Bool` is called `||`. -/

#check @False
#check @And
#check @Exists

partial def safeCases : TacticM Unit :=
  withMainContext
    (do
      let lctx ← getLCtx
      for lh in lctx do
      if  Expr.isAppOfArity (LocalDecl.type lh) ``And 2 ||
          Expr.isAppOfArity (LocalDecl.type lh) ``Exists 2 ||
          Expr.isAppOfArity (LocalDecl.type lh) ``False 0
            then
        (liftMetaTactic (fun goal ↦
          do
          let subgoals ← MVarId.cases goal lh.fvarId
          let subgoalsList := subgoals.toList
          pure (List.map (fun subgoal ↦
              InductionSubgoal.mvarId (CasesSubgoal.toInductionSubgoal subgoal))
            subgoalsList)))
        safeCases
        return)

elab "safe_cases" : tactic =>
  safeCases

theorem abcdef (a b c d e f : Prop) (P : ℕ → Prop)
    (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
    (hex : ∃x, P x) :
  False :=
  by
    safe_cases
  /- The proof state should be roughly as follows:

      case intro.intro.intro
      a b c d e f : Prop
      P : ℕ → Prop
      hneg : ¬a
      hor : c ∨ d
      himp : b → e
      hiff : e ↔ f
      left : a
      w : ℕ
      h : P w
      left_1 : b
      right : c
      ⊢ False -/
    sorry

/- 1.3 (2 points). Implement a `safe` tactic that first invokes `safe_intros`
on all goals, then `safe_cases` on all emerging subgoals, before it tries
`assumption` on all emerging subsubgoals. -/

macro "safe" : tactic =>
  `(tactic | (
              safe_intros
              safe_cases
              all_goals try assumption ))

theorem abcdef_abcd (a b c d e f : Prop) (P : ℕ → Prop)
    (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
    (hex : ∃x, P x) :
  a → ¬ b ∧ (c ↔ d) :=
  by
    safe
    /- The proof state should be roughly as follows:

        case left.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : b
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ False

        case right.mp.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : c
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ d -/
    repeat' sorry


partial def discretizeAux : TacticM Unit :=
  withMainContext
    (do
      let lctx ← getLCtx
      for lh in lctx do
      if ! LocalContext.contains lctx lh.fvarId then
      let decl : LocalDecl := mkLetDeclEx 0 lh.fvarId `due (toExpr 2) (toExpr 2)
      let LocalContext := LocalContext.modifyLocalDecl lctx lh.fvarId id

      -- for lh in lctx do
      -- if  Expr.isAppOfArity (LocalDecl.type lh) ``And 2 ||
      --     Expr.isAppOfArity (LocalDecl.type lh) ``Exists 2 ||
      --     Expr.isAppOfArity (LocalDecl.type lh) ``False 0
      --       then
      --   (liftMetaTactic (fun goal ↦
      --     do
      --     let subgoals ← MVarId.cases goal lh.fvarId
      --     let subgoalsList := subgoals.toList
      --     pure (List.map (fun subgoal ↦
      --         InductionSubgoal.mvarId (CasesSubgoal.toInductionSubgoal subgoal))
      --       subgoalsList)))
      --   safeCases
        return)

elab "add_two" : tactic =>
  safeCases

partial def Count : TacticM Unit :=
  withMainContext
  (do
    let lctx ← getLCtx
    let n := lctx.decls.toList.length
    do logInfo m!"{n}")

elab "count" : tactic => Count


#print Expr
partial def ExtrApp : TacticM Unit :=
  withMainContext
  (do
    let lctx ← getLCtx
    let mut xs : (List String) := []
    for lh in lctx do
      if lh.type.isForall then xs := "yes" :: xs
      else xs := "no" :: xs
    do logInfo m!"{xs}"
    return)
      -- if target == (Continuous `lh.fvarId) then do logInfo m!"{lh}")

elab "exists_app" : tactic => ExtrApp

-- example (X Y : Type) [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y]
--   (f : X → Y) : Continuous f := by
example (X Y : Type) (f : X → Y) /- (y : Y) (h : ∀ x : X, f x = y) -/ : true := by
  count
  exists_app
  -- let g := (ContinuousMap.equivFnOfDiscrete X Y).symm.1 f
  -- exact g.2
  -- add_two
  -- count

def motive := λ n ↦ (Fin n → ℕ)
#check (motive : ℕ → Type)
def foo := λ n ↦ (λ _ ↦ n : motive n)
#check foo



end LoVe
