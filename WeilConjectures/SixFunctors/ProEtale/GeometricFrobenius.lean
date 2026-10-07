/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

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
  : the comparison `φ̄_! ⟶ φ̄_*` commutes with these exchange isomorphisms (stated with `sorry`).
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

/-- The pullback along the base change `φ̄` commutes with the Frobenius pullbacks
`Fr^* = (Fr⁻¹)_*`: identifying `(Fr⁻¹)_*` with `Fr^*`, both composites are the pullback along
`Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`. -/
noncomputable def ProEtale.upperStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)^*[A] ⋙ (f.geometricGaloisFrobenius.inv)_*[A] ≅
      (g.geometricGaloisFrobenius.inv)_*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)^*[A] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv A f.geometricGaloisFrobenius).symm ≪≫
    (upperStarComp A _ _).symm ≪≫
    upperStarCongr A (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm ≪≫
    upperStarComp A _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv A g.geometricGaloisFrobenius) _

section OpenImmersion

variable [IsOpenImmersion φ]

/-- The restriction along the base change `φ̄` of an open immersion commutes with the
pushforwards along the Frobenii: `(Fr_Y)_* ⋙ φ̄^* ≅ φ̄^* ⋙ (Fr_X)_*`, the right adjoints of the
two sides of `ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtale.openImmersionRestrictionGeometricFiberMapCompFrobeniusIso :
    (g.geometricGaloisFrobenius.hom)_*[A] ⋙
        ProEtale.openImmersionRestriction A (Scheme.Hom.geometricFiberMap φ h) ≅
      ProEtale.openImmersionRestriction A (Scheme.Hom.geometricFiberMap φ h) ⋙
        (f.geometricGaloisFrobenius.hom)_*[A] :=
  Functor.isoWhiskerRight (upperStarIsoLowerStarInv A g.geometricGaloisFrobenius.symm).symm _ ≪≫
    Functor.isoWhiskerLeft _ (upperStarIsoOpenImmersionRestriction A _).symm ≪≫
    (upperStarComp A _ _).symm ≪≫
    upperStarCongr A
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    upperStarComp A _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction A _) _ ≪≫
    Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv A f.geometricGaloisFrobenius.symm)

/-- The extension by zero along the base change `φ̄` of an open immersion `φ` of `k`-schemes
commutes with the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`: the two composites
`φ̄_! ⋙ (Fr_Y⁻¹)_*` and `(Fr_X⁻¹)_* ⋙ φ̄_!` are left adjoint to the two sides of
`ProEtale.openImmersionRestrictionGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_!open[A] ⋙ (g.geometricGaloisFrobenius.inv)_*[A] ≅
      (f.geometricGaloisFrobenius.inv)_*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_!open[A] :=
  (conjugateIsoEquiv
      ((lowerStarEquivalence A f.geometricGaloisFrobenius).symm.toAdjunction.comp
        (openImmersionLowerShriekAdjunction A _))
      ((openImmersionLowerShriekAdjunction A _).comp
        (lowerStarEquivalence A g.geometricGaloisFrobenius).symm.toAdjunction)).symm
    (openImmersionRestrictionGeometricFiberMapCompFrobeniusIso A φ h).symm

/-- The comparison `φ̄_! ⟶ φ̄_*` commutes with the Frobenius exchange isomorphisms
`ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso` (`e_!`) and
`ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso` (`e_*`): the square

```
                  Fr_Y^* (can)
  Fr_Y^* ∘ φ̄_! ────────────────▶ Fr_Y^* ∘ φ̄_*
       │                              │
   e_! │                              │ e_*
       ▼                              ▼
  φ̄_! ∘ Fr_X^* ────────────────▶ φ̄_* ∘ Fr_X^*
                  can Fr_X^*
```

commutes, where `can` is `AlgebraicGeometry.ProEtale.openImmersionLowerShriekToLowerStar`. Both
composites are adjoint, under `φ̄_! ⊣ φ̄^*`, to the inverse of the counit of `φ̄^* ⊣ φ̄_*`
transported along the Frobenii. -/
lemma ProEtale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso :
    Functor.whiskerRight
        (ProEtale.openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h))
        (g.geometricGaloisFrobenius.inv)_*[A] ≫
      (ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso A φ h).hom =
    (ProEtale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso A φ h).hom ≫
      Functor.whiskerLeft (f.geometricGaloisFrobenius.inv)_*[A]
        (ProEtale.openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h)) :=
  sorry

end OpenImmersion

end AlgebraicGeometry
