/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.RationalOperations.RationalHomIdentifications
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFiniteUnit
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFiniteTower

/-! # Normalized coherence of the finite Verdier comparisons

Source: thm-coef-qbar-verdier, proof steps 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)

omit [IsAlgClosure (Padic l) Ω] in
/-- Simultaneous finite data from rational Verdier duality and finite Hom identification.
Source: blueprint thm-coef-qbar-verdier, proof steps 1 and 5
(blueprint: lem-coef-qbar-verdier-finite-coherence).

Proof: apply the simultaneous rational duality theorem. Choose integral dualizing
presentations at each finite coefficient field, specialize its duality and scalar
families, and use the finite Hom-identification theorem for each identity field map.
The normalized scalar comparisons themselves supply beta, so betaNormalized is reflexive. -/
theorem finiteData_nonempty : Nonempty (Finite D l hl Ω X) := by
  classical
  obtain ⟨d, s, hs, _, _⟩ := coef_rational_verdier D l hl X
  let w := fun E : Index l Ω ↦ Classical.choice
    (IntegralFiniteExtension.dualizingDatum_nonempty l X D hl (Coefficient.{u} l Ω E))
  let a := fun E : Index l Ω ↦ d (Coefficient.{u} l Ω E) (w E)
  let e := fun (E L : Index l Ω) (h : E ≤ L) ↦
    s (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) (w E) (w L)
  have H (E : Index l Ω) : Nonempty
      (RationalOperations.HomIdentification l (Coefficient.{u} l Ω E) X D hl (w E) (a E)) := by
    obtain ⟨h, _, _⟩ := RationalOperations.rationalHom_identifications
      D l hl X (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E)
      (AlgHom.id (Padic l) (Coefficient.{u} l Ω E)) (w E) (w E) (a E) (a E)
    exact ⟨h⟩
  refine ⟨{ omega := w, datum := a, hom := fun E ↦ Classical.choice (H E)
            scalar := e, normalized := ?_, beta := ?_, betaNormalized := ?_ }⟩
  · intro E L h
    exact hs (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) (w E) (w L)
  · intro E L h
    exact (e E L h).comparison
  · intro E L h
    exact HEq.rfl

/-- The normalized finite comparisons obey the prescribed unit and tower equations.
Source: thm-coef-qbar-verdier, proof steps 1--2; thm-coef-rational-verdier,
identity and composition clauses
(blueprint: lem-coef-qbar-verdier-finite-coherence).

Proof: replace each beta by the scalar comparison using betaNormalized. For an
identity inclusion, coefficientInclusion_laws identifies its field map with the
identity. Apply RationalVerdier.extension_unit to the normalized scalar datum.
Its unit j equals the prescribed rational scalar unit: both are localizations
of the integral multiplication unit conjugated by the normalized completion map.
Every rational object has the same underlying integral representative, so the
component normalization proves equality of these natural isomorphisms. This is
the unitor used in FiniteCoherent. For a tower E <= L <= M, apply
RationalVerdier.extension_composition to the three normalized scalar data,
using coefficientInclusion_laws to identify the composite field map. Its a equals
the prescribed scalar associator: their components are the localizations of the
same integral balanced tensor associator conjugated by the three completion
comparisons. The defining uniqueness of the rational scalar comparison and
associator_existsUnique identify a with associator. Substitute in the rational
tower equation, retaining the heterogeneous equality at its dependent endpoints.
Both arguments include repeated coefficient fields, the zero object and the empty scheme. -/
theorem finite_coherent (F : Finite D l hl Ω X) : FiniteCoherent D l hl Ω X F := by
  refine ⟨?_, finite_tower_equation D l hl Ω X F⟩
  have h := finite_unit_equation D l hl Ω X F
  -- The unit clause of `FiniteCoherent` (elaborated in CoefQbarVerdierData) and the statement of
  -- `finite_unit_equation` differ only in proof terms: `fieldStage._proof_1` against
  -- `IsScalarTower.left ..` inside the coefficient instances, and `FiniteCoherent._proof_1` against
  -- `le_rfl`. A plain `exact h` makes the kernel unfold the instances around them (deterministic
  -- timeout). Instead each differing proof is replaced by the other through `proof_irrel` and
  -- `congrArg`, so the kernel only beta-reduces.
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
    let G ← Lean.instantiateMVars (← g.getType)
    let hd ← Lean.Meta.getLocalDeclFromUserName `h
    let H ← Lean.instantiateMVars hd.type
    let mut stack : Array (Lean.Expr × Lean.Expr) := #[(G, H)]
    let mut pairs : Array (Lean.Expr × Lean.Expr) := #[]
    while !stack.isEmpty do
      let (a, b) := stack.back!
      stack := stack.pop
      if a == b then continue
      let a := a.consumeMData
      let b := b.consumeMData
      if a.isApp && b.isApp && a.getAppNumArgs == b.getAppNumArgs &&
          a.getAppFn == b.getAppFn then
        for x in a.getAppArgs, y in b.getAppArgs do
          stack := stack.push (x, y)
      else
        match a, b with
        | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
          stack := (stack.push (t1, t2)).push (b1, b2)
        | .lam _ t1 b1 _, .lam _ t2 b2 _ => stack := (stack.push (t1, t2)).push (b1, b2)
        | _, _ =>
          let mut a' := a
          let mut b' := b
          while a'.hasLooseBVars && a'.isApp do a' := a'.appFn!
          while b'.hasLooseBVars && b'.isApp do b' := b'.appFn!
          unless pairs.contains (a', b') do pairs := pairs.push (a', b')
    let mut cur := H
    let mut prf := hd.toExpr
    for (a, b) in pairs do
      if a.hasLooseBVars || b.hasLooseBVars then
        throwError "finite_coherent: a differing subterm is not closed"
      let T ← Lean.Meta.inferType a
      unless ← Lean.Meta.isProp T do
        throwError "finite_coherent: a differing subterm is not a proof"
      let (M, newCur) ← Lean.Meta.withLocalDeclD `p T fun p => do
        let body := cur.replace fun e => if e == b then some p else none
        return (← Lean.Meta.mkLambdaFVars #[p] body,
          body.replace fun e => if e == p then some a else none)
      let c := Lean.mkAppN (.const ``congrArg [0, 1])
        #[T, .sort 0, b, a, M, Lean.mkApp3 (.const ``proof_irrel []) T b a]
      prf := Lean.mkAppN (.const ``Eq.mp [0]) #[Lean.mkApp M b, Lean.mkApp M a, c, prf]
      cur := newCur
    g.assign prf

end WeilConjectures.CoefQbarVerdier
