/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# Gluing sheaves of étale origin along an open–closed decomposition

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. A
pro-étale sheaf of `Λ`-modules `F` on `X` sits in the short exact sequence
`0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0`, the restrictions `j^*` and `i^*` jointly detecting zero
objects. Since the sheaves of étale origin are stable under `j_!`, under `i_*` and under
extensions (the latter by the full faithfulness of `ν^*` on bounded below complexes), `F` is of
étale origin as soon as `j^* F` and `i^* F` are
(`AlgebraicGeometry.ProEtale.essImage_comparisonUpperStar_of_isCompl`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

section Extension

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The sheaves of étale origin are closed under extensions: the extension class of
`0 → F₁ → F₂ → F₃ → 0` lies in `Hom(ν^* G₃, ν^* G₁[1]) ≅ Hom(G₃, G₁[1])` by the full
faithfulness of `ν^*` on bounded below complexes
(`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`). -/
theorem essImage_comparisonUpperStar_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (h₁ : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage S.X₁)
    (h₃ : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage S.X₃) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage S.X₂ := by
  obtain ⟨G₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨G₃, ⟨e₃⟩⟩ := h₃
  let F := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let α₁ : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj G₁) ≅
      (DerivedCategory.singleFunctor _ 0).obj S.X₁ :=
    (F.mapDerivedCategorySingleFunctor 0).app G₁ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₁
  let α₃ : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj G₃) ≅
      (DerivedCategory.singleFunctor _ 0).obj S.X₃ :=
    (F.mapDerivedCategorySingleFunctor 0).app G₃ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₃
  have hplus : DerivedCategory.TStructure.t.plus
      (((DerivedCategory.singleFunctor _ 0).obj G₁)⟦(1 : ℤ)⟧) :=
    ⟨-1, DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1)⟩
  obtain ⟨δ, hδ : F.mapDerivedCategory.map δ = _⟩ :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hplus).2
      (α₃.hom ≫ hS.singleTriangle.mor₃ ≫ α₁.inv⟦(1 : ℤ)⟧' ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app _)
  obtain ⟨C, f, g, hT⟩ := Pretriangulated.distinguished_cocone_triangle₂ δ
  have hcomm : (F.mapDerivedCategory.map δ ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _) ≫ α₁.hom⟦(1 : ℤ)⟧' =
      α₃.hom ≫ hS.singleTriangle.mor₃ := by
    rw [hδ]
    simp [← Functor.map_comp]
  let e₂ := Pretriangulated.Triangle.π₂.mapIso (Pretriangulated.isoTriangleOfIso₁₃ _ _
    (F.mapDerivedCategory.map_distinguished _ hT) hS.singleTriangle_distinguished α₁ α₃ hcomm)
  have hC (n : ℤ) (hn : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((DerivedCategory.singleFunctor _ 0).obj S.X₂))) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj C) :=
    F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (hn.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e₂))
  have : C.IsGE 0 := (DerivedCategory.isGE_iff C 0).2 fun i hi ↦
    hC i (DerivedCategory.isZero_of_isGE _ 0 i hi)
  have : C.IsLE 0 := (DerivedCategory.isLE_iff C 0).2 fun i hi ↦
    hC i (DerivedCategory.isZero_of_isLE _ 0 i hi)
  obtain ⟨E, ⟨eE⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C 0
  exact ⟨E, ⟨(DerivedCategory.singleFunctor _ 0).preimageIso
    (((F.mapDerivedCategorySingleFunctor 0).app E).symm ≪≫
      F.mapDerivedCategory.mapIso eE.symm ≪≫ e₂)⟩⟩

end Extension

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {A} in
/-- The sheaves of étale origin are stable under extension by zero along an open immersion. -/
lemma essImage_comparisonUpperStar_openImmersionLowerShriek {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {F : Sheaf (Scheme.ProEt.topology U) A}
    (hF : (comparisonUpperStar A U).essImage F) :
    (comparisonUpperStar A X).essImage ((j)_!open[A].obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(Etale.openImmersionLowerShriek A j).obj G,
    ⟨(openImmersionLowerShriekComparisonUpperStarIso A j).app G ≪≫ (j)_!open[A].mapIso e⟩⟩

section OpenClosed

variable {Λ : Type (u + 1)} [CommRing Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- **Gluing along an open–closed decomposition.** Let `i : Z ⟶ X` be a closed immersion with
quasi-compact open complement `j : U ⟶ X`. A pro-étale sheaf of `Λ`-modules on `X` is of étale
origin as soon as its restrictions to `U` and to `Z` are. -/
theorem essImage_comparisonUpperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hj : (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).essImage
      ((j)^*[ModuleCat.{u + 1} Λ].obj F))
    (hi : (comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).essImage
      ((i)^*[ModuleCat.{u + 1} Λ].obj F)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage F := by
  let A := ModuleCat.{u + 1} Λ
  let R := ProEtale.openImmersionRestriction A j
  let eR : (j)^*[A] ≅ R := upperStarIsoOpenImmersionRestriction A j
  let c := (ProEtale.openImmersionLowerShriekAdjunction A j).counit.app F
  have hRc : IsIso (R.map c) := inferInstance
  have hjc : IsIso ((j)^*[A].map c) := (NatIso.isIso_map_iff eR c).2 hRc
  have hic : IsZero ((i)^*[A].obj ((j)_!open[A].obj (R.obj F))) :=
    ProEtale.isZero_upperStar_openImmersionLowerShriek A j i
      (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) _
  -- `c` is a monomorphism
  have : Mono c := by
    refine Preadditive.mono_of_isZero_kernel' _ (kernelIsKernel _) ?_
    refine isZero_of_isZero_upperStar_of_isCompl i j hij _ ?_ ?_
    · exact (IsZero.of_mono (kernel.ι ((i)^*[A].map c)) hic).of_iso
        (PreservesKernel.iso (i)^*[A] c)
    · exact IsZero.of_iso (isZero_kernel_of_mono ((j)^*[A].map c))
        (PreservesKernel.iso (j)^*[A] c)
  -- the cokernel `Q` of `c` vanishes on `U`, and is `i_* i^* F`
  have hQj : IsZero ((j)^*[A].obj (cokernel c)) :=
    IsZero.of_iso (isZero_cokernel_of_epi ((j)^*[A].map c)) (PreservesCokernel.iso (j)^*[A] c)
  have hf0 : (i)^*[A].map c = 0 := hic.eq_of_src _ _
  let eQ : (i)^*[A].obj (cokernel c) ≅ (i)^*[A].obj F :=
    PreservesCokernel.iso (i)^*[A] c ≪≫ cokernelIsoOfEq hf0 ≪≫ cokernelZeroIsoTarget
  have := isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i j hij _ hQj
  have hQ : (comparisonUpperStar A X).essImage (cokernel c) :=
    essImage_comparisonUpperStar_of_iso
      ((i)_*[A].mapIso eQ.symm ≪≫
        (asIso ((upperStarLowerStarAdjunction A i).unit.app (cokernel c))).symm)
      (essImage_comparisonUpperStar_lowerStar i hi)
  have hS : (ShortComplex.mk c (cokernel.π c) (cokernel.condition c)).ShortExact :=
    { exact := ShortComplex.exact_cokernel c }
  exact essImage_comparisonUpperStar_of_shortExact hS
    (essImage_comparisonUpperStar_openImmersionLowerShriek j
      (essImage_comparisonUpperStar_of_iso (eR.app F) hj)) hQ

end OpenClosed

end AlgebraicGeometry.ProEtale
