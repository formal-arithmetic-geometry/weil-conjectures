/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.ZetaSeries

/-! Orbit and lift-count block for local Frobenius conjugacy.
(blueprint: lem-trf-local-frobenius-conjugacy) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
variable (F : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of F.k₀)))
  [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
/-- Geometric lifts of a closed point form the normalized finite Frobenius orbit.
Source: proof steps 1--2 of the local Frobenius conjugacy blueprint.
(blueprint: lem-trf-local-frobenius-conjugacy-orbit)

Proof: identify lifts with residue-field embeddings by the Spec-point dictionary and
pullback universal property. The residue field is a finite separable extension of
positive degree d. Fixing one embedding identifies all others with its cyclic Galois
group, whose generator is q-power Frobenius. The two pullback projections identify
this generator with the displayed normalized orbit. Its order d gives injectivity
on Fin d, exhaustivity, and d-periodicity. If d divides m, the image of every embedding
lies in the q^m-power fixed subfield. Factor the embedding uniquely through that
subfield to obtain the extension point; the relative Frobenius affine formula then
fixes its geometric lift. The uniqueness follows from injectivity of subfield inclusion.
-/
theorem local_frobenius_conjugacy_orbit
    (x : Y₀.left) (_hx : IsClosed ({x} : Set Y₀.left))
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (_hz : IsLocalFrobeniusLift F Y₀ x z) :
    ∃ (hd : 1 ≤ Y₀.hom.degreeOver x),
      (∀ i : ℕ, IsLocalFrobeniusLift F Y₀ x (localFrobeniusOrbit F Y₀ z i)) ∧
      Function.Injective
        (fun i : Fin (Y₀.hom.degreeOver x) ↦ localFrobeniusOrbit F Y₀ z i.val) ∧
      (∀ w : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left,
        IsLocalFrobeniusLift F Y₀ x w →
        ∃ i : Fin (Y₀.hom.degreeOver x), localFrobeniusOrbit F Y₀ z i.val = w) ∧
      (∀ i : ℕ, localFrobeniusOrbit F Y₀ z (i + Y₀.hom.degreeOver x) =
        localFrobeniusOrbit F Y₀ z i) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        ∃! y : F.extensionPoints Y₀ m hm,
          extensionPointGeometry F Y₀ m hm y = localFrobeniusOrbit F Y₀ z i) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        (localFrobeniusOrbit F Y₀ z i) ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ m =
          localFrobeniusOrbit F Y₀ z i) := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
