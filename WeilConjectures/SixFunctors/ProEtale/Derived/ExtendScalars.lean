/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!
# Derived extension of scalars on the pro-étale site

Let `S` be an algebra over a commutative ring `R`. Derived scalar extension
`K ↦ K ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` is the total left derived functor of the
extension of scalars `F ↦ S ⊗_R F` of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.derivedExtendScalars`). It is computed on K-flat complexes:
restricted back to `R`, the extension of scalars is the tensor product with the constant sheaf
`S_X`, so it sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. It is left
adjoint to the restriction of scalars `D(X_proét, S) ⥤ D(X_proét, R)`
(`AlgebraicGeometry.ProEtale.derivedExtendRestrictScalarsAdj`).

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedExtendScalars`: the derived scalar extension
  `- ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` (blueprint `def-weil-derived-tensor`).
- `AlgebraicGeometry.ProEtale.derivedRestrictScalars`: restriction of scalars
  `D(X_proét, S) ⥤ D(X_proét, R)`.
- `AlgebraicGeometry.ProEtale.derivedExtendRestrictScalarsAdj`: the adjunction between them.
- `AlgebraicGeometry.ProEtale.derivedRestrictScalarsLeftDerivedUpperStarIso`: restriction of
  scalars commutes with the derived pullback.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsMap`: the base change map
  `(Lf^* K) ⊗ᴸ_R S ⟶ Lf^*(K ⊗ᴸ_R S)`, the mate of the previous isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomologicalComplex

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section

variable (X : Scheme.{u})

instance : (Sheaf.restrictScalars (ProEt.topology X) (algebraMap R S)).PreservesHomology where

instance : (Sheaf.extendScalars (ProEt.topology X) R S).PreservesKFlatQuasiIso where
  quasiIso_map {K L} hK hL f _ := by
    let J := ProEt.topology X
    let c := (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R S)
    have : MorphismProperty.localizerMorphismKFlat
        (quasiIso (Sheaf J (ModuleCat.{u + 1} R)) (.up ℤ)) |>.HasLeftResolutions := fun Y ↦ by
      obtain ⟨P, π, hπ, -, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat Y
      exact ⟨{ X₁ := ⟨P, hP⟩, w := π, hw := (mem_quasiIso_iff _).2 hπ }⟩
    -- restricted back to `R`, the extension of scalars of `f` is `f ⊗ S_X`, a
    -- quasi-isomorphism since `K` and `L` are K-flat
    have h₁ : quasiIso _ (.up ℤ) (f ▷ (single _ (.up ℤ) 0).obj c) :=
      (quasiIso _ (.up ℤ)).whiskerRight_of_kFlat f ((mem_quasiIso_iff _).2 inferInstance) hK hL _
    have h₂ : QuasiIso (((tensorRight c).mapHomologicalComplex (.up ℤ)).map f) :=
      (mem_quasiIso_iff _).1 (((quasiIso _ (.up ℤ)).arrow_mk_iso_iff
        (Arrow.isoOfNatIso (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
          (curriedTensor _) c) f)).1 h₁)
    have h₃ : QuasiIso (((Sheaf.extendScalars J R S ⋙ Sheaf.restrictScalars J
        (algebraMap R S)).mapHomologicalComplex (.up ℤ)).map f) :=
      (mem_quasiIso_iff _).1 (((quasiIso _ (.up ℤ)).arrow_mk_iso_iff
        (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex
          (Sheaf.extendScalarsCompRestrictScalarsIso J R S) (.up ℤ)) f)).2
        ((mem_quasiIso_iff _).2 h₂))
    rw [← quasiIso_map_iff_of_preservesHomology _ (Sheaf.restrictScalars J (algebraMap R S))]
    exact h₃

/-- **Derived scalar extension** `K ↦ K ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` along an
algebra map `R → S`: the total left derived functor of the extension of scalars of pro-étale
sheaves, computed on K-flat complexes (blueprint `def-weil-derived-tensor`). -/
noncomputable def derivedExtendScalars :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :=
  (Sheaf.extendScalars (ProEt.topology X) R S).leftDerivedFunctor

/-- Restriction of scalars `D(X_proét, S) ⥤ D(X_proét, R)` along an algebra map `R → S`,
induced by the exact restriction of scalars of pro-étale sheaves. -/
noncomputable abbrev derivedRestrictScalars :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :=
  (Sheaf.restrictScalars (ProEt.topology X) (algebraMap R S)).mapDerivedCategory

/-- Derived scalar extension is left adjoint to restriction of scalars. -/
noncomputable def derivedExtendRestrictScalarsAdj :
    derivedExtendScalars R S X ⊣ derivedRestrictScalars R S X :=
  (Sheaf.extendRestrictScalarsAdj (ProEt.topology X) R S).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars (ProEt.topology X)
      (algebraMap R S)).rightDerivedFunctorIsoMapDerivedCategory

end

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pushforward `f_*` commutes with coextension of scalars, both being computed
objectwise. -/
noncomputable def lowerStarCompCoextendScalarsIso :
    (f)_*[ModuleCat.{u + 1} R] ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} (algebraMap R S)) ≅
      sheafCompose (ProEt.topology X)
          (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} (algebraMap R S)) ⋙
        (f)_*[ModuleCat.{u + 1} S] :=
  Iso.refl _

/-- The pullback `f^*` commutes with restriction of scalars: `Res_X ∘ f^* ≅ f^* ∘ Res_Y`, the
conjugate of `lowerStarCompCoextendScalarsIso` under `f^* ⊣ f_*` and `Res ⊣ Coext`. -/
noncomputable def upperStarCompRestrictScalarsIso :
    (f)^*[ModuleCat.{u + 1} S] ⋙ Sheaf.restrictScalars (ProEt.topology X) (algebraMap R S) ≅
      Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S) ⋙ (f)^*[ModuleCat.{u + 1} R] :=
  (conjugateIsoEquiv
    ((Sheaf.restrictCoextendScalarsAdj _ _).comp (upperStarLowerStarAdjunction _ f))
    ((upperStarLowerStarAdjunction _ f).comp (Sheaf.restrictCoextendScalarsAdj _ _))).symm
    (lowerStarCompCoextendScalarsIso R S f)

/-- Restriction of scalars commutes with the derived pullback:
`Lf^* ∘ Res_Y ≅ Res_X ∘ Lf^*` on `D(Y_proét, S)`. -/
noncomputable def derivedRestrictScalarsLeftDerivedUpperStarIso :
    derivedRestrictScalars R S Y ⋙ L((f)^*[ModuleCat.{u + 1} R]) ≅
      L((f)^*[ModuleCat.{u + 1} S]) ⋙ derivedRestrictScalars R S X :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarCompRestrictScalarsIso R S f).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ f).symm _

/-- The base change map `(Lf^* K) ⊗ᴸ_R S ⟶ Lf^*(K ⊗ᴸ_R S)` of derived scalar extension along the
derived pullback: the mate of `derivedRestrictScalarsLeftDerivedUpperStarIso` under the
adjunctions `- ⊗ᴸ_R S ⊣ Res` on `X` and on `Y`. -/
noncomputable def leftDerivedUpperStarExtendScalarsMap :
    L((f)^*[ModuleCat.{u + 1} R]) ⋙ derivedExtendScalars R S X ⟶
      derivedExtendScalars R S Y ⋙ L((f)^*[ModuleCat.{u + 1} S]) :=
  (mateEquiv (derivedExtendRestrictScalarsAdj R S Y) (derivedExtendRestrictScalarsAdj R S X)).symm
    (derivedRestrictScalarsLeftDerivedUpperStarIso R S f).hom

end Pullback

end AlgebraicGeometry.ProEtale
