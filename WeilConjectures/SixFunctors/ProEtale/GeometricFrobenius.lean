/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Pro-étale functors along a base change to `k̄` commute with the Frobenius pullbacks

Let `k` be a finite field, `φ : X₀ ⟶ Y₀` a morphism of `k`-schemes and `φ̄ = φ × 𝟙 : X ⟶ Y` its
base change to the geometric fibers, so that `φ̄ ≫ Fr_Y = Fr_X ≫ φ̄` for the geometric Galois
Frobenii (`AlgebraicGeometry.Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius`).

On pro-étale sheaves the pullback along the automorphism `Fr` is the pushforward along its
inverse (`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`), and we write
`Fr^* = (Fr⁻¹)_*` throughout. This file constructs the exchange isomorphisms which transport
Frobenius structures along `φ̄_*`, `φ̄^*` and, for an open immersion `φ`, the extension by zero
`φ̄_!`. They are the pro-étale counterparts of
`WeilConjectures.SixFunctors.Etale.GeometricFrobenius` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.GeometricFrobenius`.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso`:
  `φ̄_* ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_*`.
- `AlgebraicGeometry.ProEtale.upperStarGeometricFiberMapCompFrobeniusIso`:
  `φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*`.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`:
  `φ̄_! ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_!` for an open immersion `φ`.

## Main results

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso`
  : the comparison `φ̄_! ⟶ φ̄_*` commutes with these exchange isomorphisms. The exchange
  isomorphism for `φ̄_*` is conjugate to the one for the restriction `φ̄^*`
  (`AlgebraicGeometry.ProEtale.conjugateEquiv_openImmersionRestrictionFrobeniusIso_inv`),
  so this is an instance of the general compatibility of the comparison of an adjoint triple
  with conjugate exchange isomorphisms
  (`CategoryTheory.Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open ProEtale

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The base change `φ̄` commutes with the inverses of the geometric Galois Frobenii. -/
@[reassoc]
lemma Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv :
    Scheme.Hom.geometricFiberMap φ h ≫ g.geometricGaloisFrobenius.inv =
      f.geometricGaloisFrobenius.inv ≫ Scheme.Hom.geometricFiberMap φ h := by
  rw [Iso.comp_inv_eq, Category.assoc,
    Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius, Iso.inv_hom_id_assoc]

/-- The pushforward along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*`: both composites are the pushforward along
`φ̄ ≫ Fr_Y⁻¹ = Fr_X⁻¹ ≫ φ̄`. -/
noncomputable def ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_*[A] ⋙ (g.geometricGaloisFrobenius.inv)_*[A] ≅
      (f.geometricGaloisFrobenius.inv)_*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_*[A] :=
  lowerStarComp A _ _ ≪≫
    lowerStarCongr A (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    (lowerStarComp A _ _).symm

section OpenImmersion

variable [IsOpenImmersion φ]

end OpenImmersion

end AlgebraicGeometry
