/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteTraceFormulaConventions.FiniteTraceGlobalOperatorPerfect
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperCompactificationCoincidence

/-! # The global operator of a finite-coefficient correspondence

Source: latest blueprint, sec-trace-formula/sk-d-operator/def-trf-global-operator.md,
the five-arrow display and clauses (1)--(4), with the general finite-ring convention
of Wei Yang #1412 and #1423 (blueprint: def-trf-global-operator).

The ordinary leg is proper. Both comparisons are the specified compact-support
composition comparisons. The final arrow is the specified constructible counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- A compact-support functor does not change when its compactification is only
transported along an equality of the compactified morphism (`Compactification.copy`).
Used to identify the composition target R(a_X c)_! with the given Ra_{C!}.
Source: latest blueprint def-trf-global-operator, clauses (2) and (3)
(blueprint: def-trf-global-operator).

Proof: substitute the equality `h`; then `d.copy rfl` is `d` by definition, so the two
functors agree by reflexivity. -/
theorem finiteTrfLowerShriekCopy (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (d : Compactification f) (h : f' = f) :
    rightDerivedLowerShriekOfCompactification Λ (d.copy h) =
      rightDerivedLowerShriekOfCompactification Λ d := by
  subst f'
  cases d
  rfl

/-- The triangle of a correspondence leg over the structure map of its target: the leg
followed by the structure map of the target is the structure map of the source.
Stated via `Over.w` so that no definitional `≫ 𝟙` reduction of scheme morphisms is needed.
Source: latest blueprint def-trf-global-operator, clauses (2) and (3)
(blueprint: def-trf-global-operator).

Proof: substitute `hp`; the claim is then the commutativity `g.left ≫ X.hom = C.hom` of
the morphism `g` in `Over B`, which is `Over.w g`. -/
theorem finiteTrfSepFinCompLeft {B : Scheme.{u}} {C X : Over B} (g : C ⟶ X)
    {p : X.left ⟶ B} (hp : p = X.hom) :
    g.left ≫ p = C.hom := by
  subst p
  exact Over.w g

/- The proper-coincidence family of `properCompactificationCoincidence`, chosen once as a
kernel constant: `finiteTrfProperCoincidence := fun params ↦
Exists.choose (properCompactificationCoincidence params)`. It is added directly, with the
choice predicate taken literally from the theorem's statement, exactly as for
`compCompositionWitnesses`: the ordinary definition elaborator abstracts the nested proofs
of that predicate into auxiliary lemmas, and re-identifying them with the theorem's
statement exceeds the kernel's budget. -/
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let thm := ``AlgebraicGeometry.ProEtale.CondensedRing.properCompactificationCoincidence
  let name := `WeilConjectures.finiteTrfProperCoincidence
  let info ← getConstInfo thm
  let lvls := info.levelParams.map Level.param
  let (type, value) ← forallTelescope info.type fun xs body => do
    let .app (.app (.const ``Exists [lv]) α) p := body
      | throwError "unexpected statement of {thm}"
    let h := mkAppN (.const thm lvls) xs
    let v := mkApp3 (.const ``Exists.choose [lv]) α p h
    return (← mkForallFVars xs α, ← mkLambdaFVars xs v)
  addDecl <| .defnDecl
    { name := name
      levelParams := info.levelParams
      type := type
      value := value
      hints := .opaque
      safety := .safe }
  modifyEnv fun env => addNoncomputable env name
  addDocStringCore name "The specified proper-coincidence family: `Exists.choose` of \
    `properCompactificationCoincidence`, i.e. the comparison of the compact-support functor \
    of any compactification of a proper morphism with its ordinary direct image.\n\
    Source: latest blueprint def-trf-global-operator, clause (2) \
    (blueprint: def-trf-global-operator)."

set_option maxHeartbeats 2000000 in
end WeilConjectures
