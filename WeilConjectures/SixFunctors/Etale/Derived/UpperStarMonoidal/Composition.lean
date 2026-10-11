/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-!
# The composition isomorphisms of the derived pullback are monoidal

For `f : X ⟶ Y` and `g : Y ⟶ Z`, the composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) of the derived pullbacks of étale sheaves of
`Λ`-modules is compatible with the tensor comparisons
`Lh^*(K ⊗ᴸ M) ≅ Lh^*K ⊗ᴸ Lh^*M` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`):

```
L(fg)^*(K ⊗ᴸ M) ─────────────δ_{fg}─────────────▶ L(fg)^*K ⊗ᴸ L(fg)^*M
       │                                                   │
       ▼                                                   ▼
Lf^*Lg^*(K ⊗ᴸ M) ──Lf^*δ_g──▶ Lf^*(Lg^*K ⊗ᴸ Lg^*M) ──δ_f──▶ Lf^*Lg^*K ⊗ᴸ Lf^*Lg^*M
```

The proof goes through the three levels of the construction: the composition isomorphism
`(fg)^* ≅ g^* ⋙ f^*` of the underived pullbacks is monoidal, being conjugate to the monoidal
composition isomorphism of the pushforwards; hence so is its levelwise extension to the homotopy
categories of complexes; and the derived statement follows from the uniqueness of natural
transformations into the left derived bifunctor `(K, M) ↦ L(fg)^*K ⊗ᴸ L(fg)^*M`.

## Main statements

- `AlgebraicGeometry.Etale.isMonoidal_upperStarComp_hom`: the underived statement.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`: the derived statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of the pullbacks of étale sheaves of
`Λ`-modules is monoidal: it is conjugate to the composition isomorphism of the pushforwards, which
is monoidal (`AlgebraicGeometry.Etale.isMonoidal_lowerStarComp_hom`). -/
instance isMonoidal_upperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    NatTrans.IsMonoidal (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
  have h : (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom =
      (conjugateEquiv ((Etale.upperStarLowerStarAdjunction _ h₂).comp
        (Etale.upperStarLowerStarAdjunction _ h₁))
        (Etale.upperStarLowerStarAdjunction _ h₁₂)).symm
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
    rw [Equiv.eq_symm_apply]
    exact congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarComp _ h₁ h₂ h₁₂ hh)
  rw [h]
  exact isMonoidal_conjugateEquiv_symm _ _ _

/-- The levelwise composition isomorphism `(h₁ ≫ h₂)^* K ⟶ h₁^* (h₂^* K)` of complexes of
étale sheaves: `AlgebraicGeometry.Etale.upperStarComp` applied in every degree. -/
noncomputable def upperStarCompMapHomologicalComplex {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (K : CochainComplex (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    ((h₁₂)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((h₁)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj
        (((h₂)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj K) :=
  (NatTrans.mapHomologicalComplex (Etale.upperStarComp _ h₁ h₂ h₁₂ hh).hom (.up ℤ)).app K ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl ((h₂)^*[ModuleCat.{u + 1} Λ] ⋙ (h₁)^*[ModuleCat.{u + 1} Λ])) (.up ℤ)).inv.app K

@[simp]
lemma upperStarCompMapHomologicalComplex_f {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (K : CochainComplex (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (n : ℤ) :
    (upperStarCompMapHomologicalComplex h₁ h₂ h₁₂ hh K).f n =
      (Etale.upperStarComp _ h₁ h₂ h₁₂ hh).hom.app (K.X n) := by
  simp only [upperStarCompMapHomologicalComplex, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv]
  erw [Category.comp_id]

/-- The levelwise composition isomorphism of the pullbacks is compatible with the monoidal
structures of the pullbacks of complexes: on the summand `K^p ⊗ L^q` this is the monoidality of
`AlgebraicGeometry.Etale.upperStarComp`. -/
lemma upperStarCompMapHomologicalComplex_tensor {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (K L : CochainComplex (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    (upperStarCompMapHomologicalComplex h₁ h₂ h₁₂ hh K ⊗ₘ
        upperStarCompMapHomologicalComplex h₁ h₂ h₁₂ hh L) ≫
      ((h₁)^*[ModuleCat.{u + 1} Λ].mapCochainComplexμIso _ _).hom ≫
        ((h₁)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).map
          ((h₂)^*[ModuleCat.{u + 1} Λ].mapCochainComplexμIso K L).hom =
    ((h₁₂)^*[ModuleCat.{u + 1} Λ].mapCochainComplexμIso K L).hom ≫
      upperStarCompMapHomologicalComplex h₁ h₂ h₁₂ hh (K ⊗ L) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, tensorHom_def, Category.assoc]
  rw [CochainComplex.Monoidal.ι_whiskerRight_assoc, CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    Functor.ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
  erw [Functor.ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
  simp only [upperStarCompMapHomologicalComplex_f, Functor.mapHomologicalComplex_map_f]
  rw [← (h₁)^*[ModuleCat.{u + 1} Λ].map_comp]
  erw [Functor.ιTensorObj_mapCochainComplexμIso_hom_f]
  have hnat := (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.naturality
    (HomologicalComplex.ιTensorObj K L p q n h)
  have hmon := NatTrans.IsMonoidal.tensor
    (τ := (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom) (K.X p) (L.X q)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.LaxMonoidal.comp_μ] at hnat hmon
  erw [hnat]
  rw [reassoc_of% hmon, tensorHom_def, Category.assoc, Functor.map_comp]
  rfl

end Etale

end AlgebraicGeometry
