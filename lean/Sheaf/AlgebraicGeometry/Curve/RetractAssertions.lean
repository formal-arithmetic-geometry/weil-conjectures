/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

/-!
# The eight curve assertions pass to retracts

Source: Stacks Project, Etale Cohomology, Section 03SB, proof of Lemma 03SD,
first paragraph (blueprint: lem-weil-pbc-curve-assertions-retract).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The eight curve assertions pass from a torsion abelian sheaf `H` to `P.F` when
`a ≫ b` is invertible and the conditional coefficient hypotheses pass from `P.F` to `H`.
The local `E` is the same coefficient equivalence used in finite_pushforward_assertions;
it views abelian groups as modules over `ULift ℤ`, adding no coefficient structure.
Source: Stacks Project, Section 03SB, proof of Lemma 03SD, first paragraph
(blueprint: lem-weil-pbc-curve-assertions-retract).

Proof (the node's eight steps):
1. Put `c = a ≫ b` and `r = b ≫ inv c`. Then `a ≫ r = 𝟙 P.F`, so `P.F` is a retract of `H`.
2. Cohomology and inverse image preserve this retraction. Functoriality follows by lifting
maps to the fixed K-injective resolutions and composing the lifts
(lem-weil-pbc-cohomology-pullback-functorial, def-weil-pbc-etale-cohomology,
lem-weil-pbc-functor-preserves-retract, def-weil-pbc-inverse-image).
3. Naturality of cohomology pullback for `a` and `r` makes the pullback for `P.F` a retract
of that for `H` in the arrow category (def-weil-pbc-cohomology-pullback and
lem-weil-pbc-cohomology-pullback-functorial).
4. C1 and C2 descend since a retract of zero is zero
(lem-weil-pbc-retract-of-zero-object). For C3 the primary hypothesis passes to `H`.
5. For C4 and C5 constructibility, and for C4 prime-to-characteristic torsion, pass to `H`.
The cohomology section is injective, so its source is finite if its target is finite.
6. For C6 and C7 use the arrow retraction of step 3 for the field-extension projection.
If its map for `H` is `rho_H`, the inverse for `P.F` is `beta ∘ rho_H⁻¹ ∘ alpha'`.
The two naturality squares and the retraction identities verify both inverse identities.
The prime-to-characteristic hypothesis needed for C6 passes to `H`.
7. For C8, given a class `y` on the open with coefficients in `P.F`, lift `alpha'(y)`
using surjectivity for `H`, then apply `beta` to the lift. Naturality and `beta' alpha' = id`
show that its restriction is `y` (def-weil-pbc-C8, def-weil-pbc-cohomology-pullback,
lem-weil-pbc-cohomology-pullback-functorial).
8. These give all eight assertions and hence their conjunction
(def-weil-pbc-eight-curve-assertions). -/
theorem IsCurve.assertions_of_isIso_comp {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k)
    (H : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : P.C.IsTorsionAbelianSheaf H) (a : P.F ⟶ H) (b : H ⟶ P.F)
    [IsIso (a ≫ b)]
    (hconstructible : P.IsConstructible →
      (⟨P.C, P.toSpec, P.isCurve, H, hH⟩ : CurveCoefficientPair k).IsConstructible) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let G' := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let H' := (sheafCompose P.C.smallEtaleTopology E).obj H
    (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G' →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) H') →
    (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
      Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) G' p →
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) H' p) →
    IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec H' →
      IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G' := by
  sorry

end AlgebraicGeometry
