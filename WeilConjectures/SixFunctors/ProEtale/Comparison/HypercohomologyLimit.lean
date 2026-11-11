/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.Comparison.InjectiveAcyclic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.SectionsFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Hypercohomology of pro-étale affines

Let `K ∈ D⁺(X_ét, Λ)` and let `U = lim Uᵢ` be a cofiltered limit of affine étale `X`-schemes.
Then `RΓ(U_proét, (ν_X^* K)|_U) ≅ colimᵢ RΓ((Uᵢ)_ét, K|_{Uᵢ})`
(blueprint `corollary-cohomology-pro-etale-affine--1`). Since colimits are not intrinsic in a
derived category, we state this degreewise: for every `q`, the canonical maps
`Hᵠ((Uᵢ)_ét, K|_{Uᵢ}) ⟶ Hᵠ(U_proét, (ν_X^* K)|_U)` are compatible with the transition maps and
induce a bijection from the filtered colimit
(`AlgebraicGeometry.ProEtale.proEtaleAffineHypercohomologyMap_isColimit`).

## Main definitions

- `AlgebraicGeometry.Etale.hypercohomologyPullback`: the derived pullback
  `Hᵠ(Z_ét, M) ⟶ Hᵠ(Y_ét, g^* M)` along a morphism of schemes `g : Y ⟶ Z`, for any complex `M`.
- `AlgebraicGeometry.Etale.hypercohomologyRestrictOver`: for a morphism `f : Y ⟶ Z` of schemes
  over `S` and `K ∈ D(S_ét)`, the restriction `Hᵠ(Z_ét, K|_Z) ⟶ Hᵠ(Y_ét, K|_Y)`.
- `AlgebraicGeometry.ProEtale.comparisonHypercohomologyIso`: for `M ∈ D⁺(Y_ét)`, the comparison
  isomorphism `Hᵠ(Y_ét, M) ≅ Hᵠ(Y_proét, ν^* M)`, induced by the (invertible) unit of the
  bounded below derived comparison adjunction.
- `AlgebraicGeometry.ProEtale.proEtaleAffineHypercohomologyMap`: the canonical map
  `Hᵠ(V_ét, K|_V) ⟶ Hᵠ(U_proét, (ν_X^* K)|_U)` for a morphism `U ⟶ V` of schemes over `X`.

## Main results

- `AlgebraicGeometry.Etale.hypercohomologyRestrictOver_isColimit_of_isLimit`: continuity of
  étale hypercohomology of bounded below complexes along cofiltered limits with affine
  transition maps [Stacks, Tag 0GIT].
- `AlgebraicGeometry.ProEtale.proEtaleAffineHypercohomologyMap_isColimit`: the clause.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The derived pullback `Hᵠ(Z_ét, M) ⟶ Hᵠ(Y_ét, g^* M)` on étale hypercohomology along a
morphism of schemes `g : Y ⟶ Z`: the derived global sections of the unit `M ⟶ Rg_* g^* M` of
the derived adjunction, followed by the Leray isomorphism `RΓ(Z, Rg_* -) ≅ RΓ(Y, -)`. -/
noncomputable def hypercohomologyPullback {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A)) (q : ℤ) :
    (cohomology A Z q).obj M ⟶
      (cohomology A Y q).obj ((upperStar A g).mapDerivedCategory.obj M) :=
  (DerivedCategory.homologyFunctor A q).map
    ((rightDerivedGlobalSections A Z).map
        ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app M) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A g).hom.app
        ((upperStar A g).mapDerivedCategory.obj M))

/-- For a morphism `f : Y ⟶ Z` of schemes over `S` and `K ∈ D(S_ét)`, the restriction map
`Hᵠ(Z_ét, K|_Z) ⟶ Hᵠ(Y_ét, K|_Y)`: the derived pullback along `f` followed by the
identification `f^* (K|_Z) ≅ K|_Y`. -/
noncomputable def hypercohomologyRestrictOver {S Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ pZ = pY) (K : DerivedCategory (Sheaf S.smallEtaleTopology A))
    (q : ℤ) :
    (cohomology A Z q).obj ((upperStar A pZ).mapDerivedCategory.obj K) ⟶
      (cohomology A Y q).obj ((upperStar A pY).mapDerivedCategory.obj K) :=
  hypercohomologyPullback A f _ q ≫ (cohomology A Y q).map
    ((Functor.mapDerivedCategoryNatIso (upperStarComp A f pZ pY hf.symm) ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar A pZ) (upperStar A f)).symm).inv.app K)

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Continuity of étale hypercohomology** [Stacks, Tag 0GIT]. Let `(Uᵢ)` be a cofiltered
system of quasi-compact quasi-separated schemes over `S` with affine transition maps and limit
`U`, and let `K ∈ D⁺(S_ét, Λ)`. Then, in every degree `q`, the restriction maps
`Hᵠ((Uᵢ)_ét, K|_{Uᵢ}) ⟶ Hᵠ(U_ét, K|_U)` are compatible with the transition maps and induce a
bijection `colimᵢ Hᵠ((Uᵢ)_ét, K|_{Uᵢ}) ≅ Hᵠ(U_ét, K|_U)`: every class on `U` comes from a stage,
and a class at a stage vanishing on `U` vanishes at a later stage. -/
theorem hypercohomologyRestrictOver_isColimit_of_isLimit {S : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℤ) :
    (∀ {i j : I} (g : j ⟶ i) (y : (cohomology (ModuleCat.{u + 1} Λ) (D.obj i).left q).obj
        ((upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
      (hypercohomologyRestrictOver _ c.pt.hom (D.obj j).hom (c.π.app j).left (Over.w _)
          K.obj q).hom
        ((hypercohomologyRestrictOver _ (D.obj j).hom (D.obj i).hom (D.map g).left
          (Over.w _) K.obj q).hom y) =
      (hypercohomologyRestrictOver _ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _)
          K.obj q).hom y) ∧
    (∀ x : (cohomology (ModuleCat.{u + 1} Λ) c.pt.left q).obj
        ((upperStar _ c.pt.hom).mapDerivedCategory.obj K.obj),
      ∃ (i : I) (y : (cohomology (ModuleCat.{u + 1} Λ) (D.obj i).left q).obj
          ((upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
        (hypercohomologyRestrictOver _ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _)
          K.obj q).hom y = x) ∧
    (∀ (i : I) (y : (cohomology (ModuleCat.{u + 1} Λ) (D.obj i).left q).obj
        ((upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
      (hypercohomologyRestrictOver _ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _)
          K.obj q).hom y = 0 →
        ∃ (j : I) (g : j ⟶ i),
          (hypercohomologyRestrictOver _ (D.obj j).hom (D.obj i).hom (D.map g).left
            (Over.w _) K.obj q).hom y = 0) := by
  sorry

end Etale

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The comparison isomorphism `Hᵠ(Y_ét, M) ≅ Hᵠ(Y_proét, ν^* M)` for a bounded below complex
`M` of étale sheaves: the derived global sections of the unit `M ⟶ Rν_* ν^* M` of the bounded
below derived comparison adjunction, which is invertible since the unit of `ν^* ⊣ ν_*` is and
`ν^*` sends injectives to `ν_*`-acyclic sheaves, followed by `RΓ(Y_ét, Rν_* -) ≅
RΓ(Y_proét, -)`. -/
noncomputable def comparisonHypercohomologyIso (Y : Scheme.{u})
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) (q : ℤ) :
    (Etale.cohomology A Y q).obj M.obj ≅
      (DerivedCategory.homologyFunctor A q).obj
        ((rightDerivedGlobalSections A Y).obj
          ((comparisonUpperStar A Y).mapDerivedCategory.obj M.obj)) := by
  let L := comparisonUpperStar A Y
  let R := comparisonLowerStar A Y
  let adj := comparisonAdjunction A Y
  have := isIso_comparisonAdjunction_unit A Y
  have := adj.isIso_derivedPlus_unit_app_of_rightAcyclic (fun _ _ ↦ inferInstance)
    (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective A Y I) M
  exact (DerivedCategory.homologyFunctor A q).mapIso
    ((Etale.rightDerivedGlobalSections A Y).mapIso
        ((DerivedCategory.Plus.ι.mapIso (asIso (adj.derivedPlus.unit.app M))) ≪≫
          R.rightDerivedFunctorPlusCompatibility.app (L.mapDerivedCategoryPlus.obj M)) ≪≫
      (comparisonLowerStarCompRightDerivedGlobalSectionsIso A Y).app
        (L.mapDerivedCategoryPlus.obj M).obj ≪≫
      (rightDerivedGlobalSections A Y).mapIso (L.mapDerivedCategoryPlusCompatibility.app M))

/-- The isomorphism `ν_U^* (K|_U) ≅ (ν_X^* K)|_U` on derived categories, for a morphism of
schemes `p : U ⟶ X`, induced by `comparisonUpperStarCompUpperStarIso`. -/
noncomputable def mapDerivedComparisonUpperStarCompUpperStarIso {U X : Scheme.{u}}
    (p : U ⟶ X) :
    (comparisonUpperStar A X).mapDerivedCategory ⋙ (ProEtale.upperStar A p).mapDerivedCategory ≅
      (Etale.upperStar A p).mapDerivedCategory ⋙ (comparisonUpperStar A U).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso A p) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- For a morphism `f : U ⟶ V` of schemes over `X` and `K ∈ D⁺(X_ét)`, the canonical map
`Hᵠ(V_ét, K|_V) ⟶ Hᵠ(U_proét, (ν_X^* K)|_U)`: étale restriction to `U`, followed by the
comparison isomorphism on `U` and the identification `ν_U^* (K|_U) ≅ (ν_X^* K)|_U`. -/
noncomputable def proEtaleAffineHypercohomologyMap {X U V : Scheme.{u}} (pU : U ⟶ X)
    (pV : V ⟶ X) (f : U ⟶ V) (hf : f ≫ pV = pU)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (q : ℤ) :
    (Etale.cohomology A V q).obj ((Etale.upperStar A pV).mapDerivedCategory.obj K.obj) ⟶
      (DerivedCategory.homologyFunctor A q).obj ((rightDerivedGlobalSections A U).obj
        ((ProEtale.upperStar A pU).mapDerivedCategory.obj
          ((comparisonUpperStar A X).mapDerivedCategory.obj K.obj))) :=
  Etale.hypercohomologyRestrictOver A pU pV f hf K.obj q ≫
    (comparisonHypercohomologyIso A U
      ((Etale.upperStar A pU).mapDerivedCategoryPlus.obj K) q).hom ≫
    (DerivedCategory.homologyFunctor A q).map ((rightDerivedGlobalSections A U).map
      ((mapDerivedComparisonUpperStarCompUpperStarIso A pU).inv.app K.obj))

/-- The isomorphism `Hᵠ(U_ét, K|_U) ≅ Hᵠ(U_proét, (ν_X^* K)|_U)` through which
`proEtaleAffineHypercohomologyMap` factors. -/
noncomputable def proEtaleAffineHypercohomologyIso {X U : Scheme.{u}} (pU : U ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (q : ℤ) :
    (Etale.cohomology A U q).obj ((Etale.upperStar A pU).mapDerivedCategory.obj K.obj) ≅
      (DerivedCategory.homologyFunctor A q).obj ((rightDerivedGlobalSections A U).obj
        ((ProEtale.upperStar A pU).mapDerivedCategory.obj
          ((comparisonUpperStar A X).mapDerivedCategory.obj K.obj))) :=
  comparisonHypercohomologyIso A U ((Etale.upperStar A pU).mapDerivedCategoryPlus.obj K) q ≪≫
    (DerivedCategory.homologyFunctor A q).mapIso ((rightDerivedGlobalSections A U).mapIso
      ((mapDerivedComparisonUpperStarCompUpperStarIso A pU).symm.app K.obj))

/-- The canonical map is the étale restriction followed by `proEtaleAffineHypercohomologyIso`. -/
lemma proEtaleAffineHypercohomologyMap_eq {X U V : Scheme.{u}} (pU : U ⟶ X)
    (pV : V ⟶ X) (f : U ⟶ V) (hf : f ≫ pV = pU)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (q : ℤ) :
    proEtaleAffineHypercohomologyMap A pU pV f hf K q =
      Etale.hypercohomologyRestrictOver A pU pV f hf K.obj q ≫
        (proEtaleAffineHypercohomologyIso A pU K q).hom :=
  rfl

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Cohomology of a pro-étale affine** (blueprint `corollary-cohomology-pro-etale-affine--1`).
Let `K ∈ D⁺(X_ét, Λ)` and let `U = lim Uᵢ` be a cofiltered limit of affine étale `X`-schemes
`Uᵢ` (a pro-étale affine). Then `RΓ(U_proét, (ν_X^* K)|_U) ≅ colimᵢ RΓ((Uᵢ)_ét, K|_{Uᵢ})`,
in the following degreewise form: for every `q`, the canonical maps
`Hᵠ((Uᵢ)_ét, K|_{Uᵢ}) ⟶ Hᵠ(U_proét, (ν_X^* K)|_U)` (`proEtaleAffineHypercohomologyMap`) are
compatible with the étale restriction maps between the stages, every class on `U` comes from
some stage, and a class at a stage vanishing on `U` vanishes at a later stage; that is, they
induce an isomorphism from the filtered colimit.

Proof: the canonical map is the étale restriction to `U` followed by the comparison isomorphism
`Hᵠ(U_ét, K|_U) ≅ Hᵠ(U_proét, ν_U^* (K|_U))` (the bounded below comparison theorem) and
`ν_U^* (K|_U) ≅ (ν_X^* K)|_U`; conclude by continuity of étale hypercohomology
(`AlgebraicGeometry.Etale.hypercohomologyRestrictOver_isColimit_of_isLimit`, [Stacks, Tag
0GIT]). -/
theorem proEtaleAffineHypercohomologyMap_isColimit {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over X)
    [∀ i, IsAffine (D.obj i).left] [∀ i, Etale (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c)) (q : ℤ) :
    (∀ {i j : I} (g : j ⟶ i)
      (y : (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i).left q).obj
        ((Etale.upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
      (proEtaleAffineHypercohomologyMap _ c.pt.hom (D.obj j).hom (c.π.app j).left (Over.w _)
          K q).hom
        ((Etale.hypercohomologyRestrictOver _ (D.obj j).hom (D.obj i).hom (D.map g).left
          (Over.w _) K.obj q).hom y) =
      (proEtaleAffineHypercohomologyMap _ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _)
          K q).hom y) ∧
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((rightDerivedGlobalSections _ c.pt.left).obj
          ((ProEtale.upperStar _ c.pt.hom).mapDerivedCategory.obj
            ((comparisonUpperStar _ X).mapDerivedCategory.obj K.obj))),
      ∃ (i : I) (y : (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i).left q).obj
          ((Etale.upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
        (proEtaleAffineHypercohomologyMap _ c.pt.hom (D.obj i).hom (c.π.app i).left
          (Over.w _) K q).hom y = x) ∧
    (∀ (i : I) (y : (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i).left q).obj
        ((Etale.upperStar _ (D.obj i).hom).mapDerivedCategory.obj K.obj)),
      (proEtaleAffineHypercohomologyMap _ c.pt.hom (D.obj i).hom (c.π.app i).left
          (Over.w _) K q).hom y = 0 →
        ∃ (j : I) (g : j ⟶ i),
          (Etale.hypercohomologyRestrictOver _ (D.obj j).hom (D.obj i).hom (D.map g).left
            (Over.w _) K.obj q).hom y = 0) := by
  have {i j : I} (g : i ⟶ j) : IsAffineHom (D.map g).left := inferInstance
  obtain ⟨h₁, h₂, h₃⟩ := Etale.hypercohomologyRestrictOver_isColimit_of_isLimit K D c hc q
  set T := proEtaleAffineHypercohomologyIso (ModuleCat.{u + 1} Λ) c.pt.hom K q
  refine ⟨fun g y ↦ ?_, fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · simp only [proEtaleAffineHypercohomologyMap_eq, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [h₁ g y]
  · obtain ⟨i, y, hy⟩ := h₂ (T.inv.hom x)
    refine ⟨i, y, ?_⟩
    simp only [proEtaleAffineHypercohomologyMap_eq, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hy]
    exact T.inv_hom_id_apply x
  · refine h₃ i y ?_
    simp only [proEtaleAffineHypercohomologyMap_eq, ModuleCat.hom_comp,
      LinearMap.comp_apply] at hy
    have h := congrArg T.inv.hom hy
    rwa [Iso.hom_inv_id_apply, map_zero] at h

end ProEtale

end AlgebraicGeometry

end
