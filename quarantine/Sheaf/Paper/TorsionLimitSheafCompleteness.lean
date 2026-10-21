/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.TorsionCompletionDefinitions
import Sheaf.CategoryTheory.RingedSiteCompleteElementsLocal
import Sheaf.CategoryTheory.ScalarLocalizationRegularColimit
import Sheaf.Paper.TorsionCompletionIdealPowers
import Sheaf.Paper.ProEtaleMultiplicationDifferenceCriterion
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # Completeness of limits of power-torsion pro-etale sheaves

Source: Stacks Project, Tags 099P and 099Q (1), (4), (5)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness).

We use the existing coefficient-sized small model of the unchanged small pro-etale site.
It is equivalent via AsSmall.down to X.ProEt; its topology is the induced topology.
Thus this changes sizes only, not objects, covers, slices, or coefficient sheaves up to
canonical equivalence. Local completeness is the existing slice internal-Hom definition.
The extended ideal is constructed as the kernel of the constant quotient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] torsionCompletionQuotient torsionCompletionQuotientOne
  torsionCompletionQuotientMap torsionCompletionIdeal torsionCompletionIdealInclusion

private theorem isIso_on_limit {B : Type u} [Category.{v} B]
    {D : Type*} [Category* D] (F : D ⥤ B) [HasLimit F]
    (P : B ⥤ B) [PreservesLimit F P] (δ : P ⟶ P)
    (hδ : ∀ d, IsIso (δ.app (F.obj d))) : IsIso (δ.app (limit F)) := by
  let α := Functor.whiskerLeft F δ
  have (d : D) : IsIso (α.app d) := hδ d
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let hc := isLimitOfPreserves P (limit.isLimit F)
  let e := IsLimit.conePointsIsoOfNatIso hc hc (asIso α)
  have he : δ.app (limit F) = e.hom := by
    apply hc.hom_ext
    intro d
    change δ.app (limit F) ≫ P.map (limit.π F d) = _
    rw [← δ.naturality]
    exact (IsLimit.conePointsIsoOfNatIso_hom_comp hc hc (asIso α) d).symm
  rw [he]
  infer_instance

private theorem isoLocus_of_iso {B : Type*} [Category* B] (P : B ⥤ B)
    (δ : P ⟶ P) {M N : B} (e : M ≅ N) (h : IsIso (δ.app N)) :
    IsIso (δ.app M) := by
  have := h
  have he : δ.app M = P.map e.hom ≫ δ.app N ≫ P.map e.inv := by
    rw [← Category.assoc, δ.naturality, Category.assoc, ← P.map_comp,
      e.hom_inv_id, P.map_id, Category.comp_id]
  rw [he]
  infer_instance

private theorem isoLocus_five {B : Type*} [Category* B] [Abelian B]
    (P : B ⥤ B) [P.Additive] [P.PreservesHomology] (δ : P ⟶ P)
    {F₁ F₂ F₃ F₄ F₅ : B}
    (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (c : F₃ ⟶ F₄) (d : F₄ ⟶ F₅)
    (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0)
    (h₁ : (ShortComplex.mk a b hab).Exact)
    (h₂ : (ShortComplex.mk b c hbc).Exact)
    (h₃ : (ShortComplex.mk c d hcd).Exact)
    (hF₁ : IsIso (δ.app F₁)) (hF₂ : IsIso (δ.app F₂))
    (hF₄ : IsIso (δ.app F₄)) (hF₅ : IsIso (δ.app F₅)) :
    IsIso (δ.app F₃) := by
  have := hF₁
  have := hF₂
  have := hF₄
  have := hF₅
  let R := ComposableArrows.mk₄ (P.map a) (P.map b) (P.map c) (P.map d)
  have hR : R.Exact := by
    apply (ComposableArrows.exact_iff_δ₀ R).mpr
    refine ⟨(h₁.map P).exact_toComposableArrows, ?_⟩
    apply (ComposableArrows.exact_iff_δ₀ R.δ₀).mpr
    exact ⟨(h₂.map P).exact_toComposableArrows, (h₃.map P).exact_toComposableArrows⟩
  let α : R ⟶ R := ComposableArrows.homMk₄
    (δ.app F₁) (δ.app F₂) (δ.app F₃) (δ.app F₄) (δ.app F₅)
    (δ.naturality a) (δ.naturality b) (δ.naturality c) (δ.naturality d)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR α
    (by dsimp [α]; infer_instance) (by dsimp [α]; infer_instance)
    (by dsimp [α]; infer_instance) (by dsimp [α]; infer_instance)

private theorem difference_iso_of_nilpotent {B : Type*} [Category* B]
    [Preadditive B] {M : B} [HasProduct (fun _ : ℕ ↦ M)]
    (a : End M) (ha : IsNilpotent a) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ M) (fun _ ↦ a)) := by
  let s : End (∏ᶜ fun _ : ℕ ↦ M) := towerProductShift (K := fun _ : ℕ ↦ M) (fun _ ↦ a)
  have hs (r j : ℕ) : (s ^ r) ≫ Pi.π (fun _ : ℕ ↦ M) j =
      Pi.π (fun _ : ℕ ↦ M) (j + r) ≫ a ^ r := by
    induction r generalizing j with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, End.mul_def, Category.assoc, ih, ← Category.assoc]
      simp only [s, towerProductShift, Pi.lift_π]
      rw [Category.assoc, ← End.mul_def, ← pow_succ]
      simp only [Nat.add_assoc]
  obtain ⟨e, he⟩ := ha
  have hnil : IsNilpotent s := by
    refine ⟨e, Pi.hom_ext _ _ fun j ↦ ?_⟩
    rw [hs, he, comp_zero, zero_comp]
  exact (isUnit_iff_isIso (1 - s)).mp hnil.isUnit_one_sub

private def endPower {B : Type*} [Category* B] {M : B} (a : End M) (n : ℕ) :
    End M := a ^ n

private theorem sectionMultiplication_pow {C : Type*} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat) (U : C)
    (f : O.obj.obj (op U))
    (M : SheafOfModules ((localCoefficientRings O).over U))
    (n : ℕ) (V : (Over U)ᵒᵖ) (x : M.val.obj V) :
    ((endPower (localSectionMultiplication O U f M) n).val.app V) x =
      (O.obj.map V.unop.hom.op f) ^ n • x := by
  induction n generalizing x with
  | zero => change x = _; simp
  | succ n ih =>
    change ((endPower (localSectionMultiplication O U f M) n).val.app V)
      ((localSectionMultiplication O U f M).val.app V x) = _
    rw [ih]
    change (O.obj.map V.unop.hom.op f) ^ n • ((O.obj.map V.unop.hom.op f) • x) = _
    rw [smul_smul, pow_succ]

private theorem torsion_difference_iso (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (U : coefficientProEtaleSiteModel.{t, u} X)
    (F : SheafOfModules.{max u (t + 1)} ((torsionCompletionModuleRing X A).over U))
    (n : ℕ)
    (hF : IsAnnihilatedByModuleIdeal ((torsionCompletionModuleRing X A).over U)
      ((torsionCompletionIdeal X (I ^ n)).over U)
      ((torsionCompletionIdealInclusion X (I ^ n)).over U) F)
    (f : (torsionCompletionRing X A).obj.obj (op U))
    (hf : ∃ y : (torsionCompletionIdeal X I).val.obj (op U),
      (torsionCompletionIdealInclusion X I).val.app (op U) y = f) :
    IsIso ((multiplicationDifference (torsionCompletionRing X A) U f).app F) := by
  apply difference_iso_of_nilpotent
  refine ⟨n, ?_⟩
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((endPower (localSectionMultiplication (torsionCompletionRing X A) U f F)
    n).val.app V).hom x = 0
  rw [sectionMultiplication_pow]
  obtain ⟨y, hy⟩ := torsionCompletionIdeal_section_pow X I V.unop.left
    ((torsionCompletionRing X A).obj.map V.unop.hom.op f) (by
      obtain ⟨y, rfl⟩ := hf
      refine ⟨(torsionCompletionIdeal X I).val.map V.unop.hom.op y, ?_⟩
      exact (PresheafOfModules.naturality_apply
        (torsionCompletionIdealInclusion X I).val V.unop.hom.op y)) n
  change _ = 0
  rw [← hy]
  exact hF V.unop y x

private theorem completeSheaf_iff_difference (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) (F : TorsionCompletionModules X A) :
    IsTorsionCompletionCompleteSheaf X I F ↔
      ∀ (U : coefficientProEtaleSiteModel.{t, u} X)
        (f : (torsionCompletionRing X A).obj.obj (op U)),
        (∃ y : (torsionCompletionIdeal X I).val.obj (op U),
          (torsionCompletionIdealInclusion X I).val.app (op U) y = f) →
        IsIso ((multiplicationDifference (torsionCompletionRing X A) U f).app (F.over U)) := by
  let O := torsionCompletionRing X A
  let := HasDerivedCategory.standard (TorsionCompletionModules X A)
  let (U : coefficientProEtaleSiteModel.{t, u} X) :=
    HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
      ((torsionCompletionModuleRing X A).over U))
  have he (U : coefficientProEtaleSiteModel.{t, u} X) :
      (ringedDerivedRestriction O U).obj
          ((torsionCompletionLocalization X A).obj
            ((HomologicalComplex.single _ (.up ℤ) 0).obj F)) ≅
        (DerivedCategory.singleFunctor _ 0).obj (F.over U) :=
    (ringedDerivedRestriction O U).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F).symm ≪≫
      (Functor.mapDerivedCategorySingleFunctor
        (SheafOfModules.overFunctor (torsionCompletionModuleRing X A) U) 0).app F
  constructor
  · intro h U f hf
    apply (proEtale_multiplicationDifference_criterion X O U f).2.1 F |>.mp
    exact (h U f hf).of_iso
      ((derivedInternalHom _ (O.over U)).mapIso ((Iso.refl _).prod (he U))).symm
  · intro h U f hf
    have hz := (proEtale_multiplicationDifference_criterion X O U f).2.1 F |>.mpr
      (h U f hf)
    exact hz.of_iso
      ((derivedInternalHom _ (O.over U)).mapIso ((Iso.refl _).prod (he U)))

private theorem completeSheaf_of_powerTorsion (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) (F : TorsionCompletionModules X A) (n : ℕ)
    (hF : IsAnnihilatedByModuleIdeal (torsionCompletionModuleRing X A)
      (torsionCompletionIdeal X (I ^ n)) (torsionCompletionIdealInclusion X (I ^ n)) F) :
    IsTorsionCompletionCompleteSheaf X I F := by
  apply (completeSheaf_iff_difference X I F).mpr
  intro U f hf
  apply torsion_difference_iso X I U (F.over U) n
  · intro V y x
    exact hF V.left y x
  · exact hf

private theorem sectionLocalizationIso {C : Type*} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat) (U : C)
    (f : O.obj.obj (op U)) :
    Nonempty (ringedSiteSectionLocalization (localCoefficientRings O) U f ≅
      ringedSectionLocalization (O.over U) (ringedSliceSection O U f)) := by
  obtain ⟨c, ⟨hc⟩, e, _⟩ :=
    scalarLocalization_regularColimit (O.over U) (ringedSliceSection O U f)
  exact ⟨(colimit.isoColimitCocone ⟨c, hc⟩) ≪≫ e⟩

private theorem completeElement_iff_difference (X : Scheme.{t}) {A : Type u}
    [CommRing A] (F : TorsionCompletionModules X A)
    (U : coefficientProEtaleSiteModel.{t, u} X)
    (f : (torsionCompletionRing X A).obj.obj (op U)) :
    let := HasDerivedCategory.standard (TorsionCompletionModules X A)
    let (V : coefficientProEtaleSiteModel.{t, u} X) :=
      HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
        ((torsionCompletionModuleRing X A).over V))
    IsRingedSiteCompleteElement (coefficientProEtaleModelTopology.{t, u} X)
      (torsionCompletionRing X A)
      ((torsionCompletionLocalization X A).obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj F)) U f ↔
      IsIso ((multiplicationDifference (torsionCompletionRing X A) U f).app (F.over U)) := by
  dsimp only
  let O := torsionCompletionRing X A
  let R := torsionCompletionModuleRing X A
  let := HasDerivedCategory.standard (TorsionCompletionModules X A)
  let (V : coefficientProEtaleSiteModel.{t, u} X) :=
    HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over V))
  let K := (torsionCompletionLocalization X A).obj
    ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
  let T := SheafOfModules.overFunctor R U
  let eK : ringedSiteDerivedRestriction R U K ≅
      (DerivedCategory.singleFunctor _ 0).obj (F.over U) :=
    (T.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
      T.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K) ≪≫
      (T.mapDerivedCategorySingleFunctor 0).app F
  let eL := (DerivedCategory.singleFunctor _ 0).mapIso (sectionLocalizationIso O U f).some
  let eH := (derivedInternalHom
    ((coefficientProEtaleModelTopology.{t, u} X).over U) (O.over U)).mapIso
      (eL.symm.op.prod eK)
  constructor
  · intro h
    apply ((proEtale_multiplicationDifference_criterion X O U f).2.1 F).mp
    exact h.of_iso eH.symm
  · intro h
    have hz := ((proEtale_multiplicationDifference_criterion X O U f).2.1
      F).mpr h
    exact hz.of_iso eH

private theorem completeSheaf_of_localTorsionLimit (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) (F : TorsionCompletionModules X A)
    (hF : IsLocallyPowerTorsionLimit X I F) :
    IsTorsionCompletionCompleteSheaf X I F := by
  let O := torsionCompletionRing X A
  let R := torsionCompletionModuleRing X A
  let := HasDerivedCategory.standard (TorsionCompletionModules X A)
  let (V : coefficientProEtaleSiteModel.{t, u} X) :=
    HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over V))
  let K := (torsionCompletionLocalization X A).obj
    ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
  apply (completeSheaf_iff_difference X I F).mpr
  intro U f hf
  apply (completeElement_iff_difference X F U f).mp
  obtain ⟨S, hS, hlocal⟩ := hF U
  apply (ringedSite_completeElements_locality
    (coefficientProEtaleModelTopology.{t, u} X) O K).2 U S hS f
  intro V a ha
  apply (completeElement_iff_difference X F V (O.obj.map a.op f)).mpr
  obtain ⟨G, g, hG, ⟨e⟩⟩ := hlocal V a ha
  let P := countablePower (SheafOfModules.{max u (t + 1)} (R.over V))
  let δ := multiplicationDifference O V (O.obj.map a.op f)
  apply isoLocus_of_iso P δ e
  apply isIso_on_limit (Functor.ofOpSequence g) P δ
  intro n
  apply torsion_difference_iso X I V (G n.unop) (n.unop + 1) (hG n.unop)
  obtain ⟨y, rfl⟩ := hf
  refine ⟨(torsionCompletionIdeal X I).val.map a.op y, ?_⟩
  exact (PresheafOfModules.naturality_apply
    (torsionCompletionIdealInclusion X I).val a.op y)

private theorem completeComplex_of_completeTerms (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) (K : CochainComplex (TorsionCompletionModules X A) ℤ)
    (hK : ∀ i, IsTorsionCompletionCompleteSheaf X I (K.X i)) :
    IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj K) := by
  let O := torsionCompletionRing X A
  let R := torsionCompletionModuleRing X A
  let := HasDerivedCategory.standard (TorsionCompletionModules X A)
  let (V : coefficientProEtaleSiteModel.{t, u} X) :=
    HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over V))
  intro U f hf
  let T := SheafOfModules.overFunctor R U
  let e := T.mapDerivedCategoryFactors.app K
  have hz := (proEtale_multiplicationDifference_criterion X O U f).2.2
    K (fun i ↦
      (completeSheaf_iff_difference X I (K.X i)).mp (hK i) U f hf)
  exact hz.of_iso ((derivedInternalHom
    ((coefficientProEtaleModelTopology.{t, u} X).over U) (O.over U)).mapIso
      ((Iso.refl _).prod e))

private theorem completeSheaf_five (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) {F₁ F₂ F₃ F₄ F₅ : TorsionCompletionModules X A}
    (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (c : F₃ ⟶ F₄) (d : F₄ ⟶ F₅)
    (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0)
    (h₁ : (ShortComplex.mk a b hab).Exact)
    (h₂ : (ShortComplex.mk b c hbc).Exact)
    (h₃ : (ShortComplex.mk c d hcd).Exact)
    (hF₁ : IsTorsionCompletionCompleteSheaf X I F₁)
    (hF₂ : IsTorsionCompletionCompleteSheaf X I F₂)
    (hF₄ : IsTorsionCompletionCompleteSheaf X I F₄)
    (hF₅ : IsTorsionCompletionCompleteSheaf X I F₅) :
    IsTorsionCompletionCompleteSheaf X I F₃ := by
  apply (completeSheaf_iff_difference X I F₃).mpr
  intro U f hf
  let T := SheafOfModules.overFunctor (torsionCompletionModuleRing X A) U
  let P := countablePower (SheafOfModules.{max u (t + 1)}
    ((torsionCompletionModuleRing X A).over U))
  have : P.PreservesHomology :=
    (proEtale_multiplicationDifference_criterion X (torsionCompletionRing X A) U f).1
  exact isoLocus_five P (multiplicationDifference (torsionCompletionRing X A) U f)
    (T.map a) (T.map b) (T.map c) (T.map d)
    (by simp [← T.map_comp, hab]) (by simp [← T.map_comp, hbc])
    (by simp [← T.map_comp, hcd]) (h₁.map T) (h₂.map T) (h₃.map T)
    ((completeSheaf_iff_difference X I F₁).mp hF₁ U f hf)
    ((completeSheaf_iff_difference X I F₂).mp hF₂ U f hf)
    ((completeSheaf_iff_difference X I F₄).mp hF₄ U f hf)
    ((completeSheaf_iff_difference X I F₅).mp hF₅ U f hf)

private theorem completeSheaf_limit (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (F : ℕ → TorsionCompletionModules X A)
    (f : ∀ n : ℕ, F (n + 1) ⟶ F n)
    (hF : ∀ n, IsTorsionCompletionCompleteSheaf X I (F n)) :
    IsTorsionCompletionCompleteSheaf X I (limit (Functor.ofOpSequence f)) := by
  apply (completeSheaf_iff_difference X I _).mpr
  intro U s hs
  let T := SheafOfModules.overFunctor (torsionCompletionModuleRing X A) U
  have : T.IsRightAdjoint :=
    (SheafOfModules.localizedSystemAdjunction (torsionCompletionRing X A) U).isRightAdjoint
  let P := countablePower (SheafOfModules.{max u (t + 1)}
    ((torsionCompletionModuleRing X A).over U))
  let δ := multiplicationDifference (torsionCompletionRing X A) U s
  have he := preservesLimitIso T (Functor.ofOpSequence f)
  apply isoLocus_of_iso P δ he
  apply isIso_on_limit (Functor.ofOpSequence f ⋙ T) P δ
  intro n
  exact (completeSheaf_iff_difference X I (F n.unop)).mp (hF n.unop) U s hs

/-- Complete sheaves are a weak Serre class, are closed under ordinary countable inverse
limits, include all power-torsion sheaves, and therefore include locally power-torsion
limits and bounded complexes of these sheaves.
Source: Stacks Tags 099P and 099Q (1), (4), (5)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness).

Proof:
1. On every slice use weakly-etale localization and exact restriction. Exact countable
products represent derived products (lem-weil-proetale-countable-products-exact and
lem-weil-derived-limit-products-core). The local Hom/tower criterion identifies
completeness of F[0] with invertibility of Delta_f on its countable product, where
Delta_f(x)_j = x_j - f x_(j+1). This tests all local ideal sections.
2. Apply exact products to the five-term exact sequence. The four outside Delta maps
are invertible. Injectivity of the middle map follows by lifting into the second term
and correcting by a lift from the first; surjectivity follows by lifting the inverse
image in the fourth term and correcting the error from the second term. Local lifts
and their unique inverses glue. This gives the weak Serre assertion.
3. Products and restriction are sectionwise. Exchange the two compatible-family
conditions for products and inverse limits. The inverses of Delta at each level commute
with every transition, since Delta does. They give an inverse on the ordinary limit,
without surjective transitions or exactness of inverse limits.
4. If I^n F = 0, the shift s_f satisfies s_f^n = 0 on every slice for f in the ideal.
The finite sum 1+s_f+...+s_f^(n-1) inverts 1-s_f. Thus power-torsion sheaves are complete.
5. Delta and its cone commute with slice restriction. Local inverses glue, or equivalently
vanishing of the cone cohomology is local. Apply steps 3 and 4 to every local tower.
6. For the bounded complex, Delta is a chain isomorphism term by term by step 5.
Its inverse commutes with the differentials by linearity. Its cone is contractible,
with h(b,a) = (0,Delta^(-1)b). The product representation and local Hom/tower criterion
then give the required derived internal-Hom vanishing. -/
theorem torsionLimitSheaf_completeness (X : Scheme.{t}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (_hI : I.FG) :
    (∀ (F₁ F₂ F₃ F₄ F₅ : TorsionCompletionModules X A)
      (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (c : F₃ ⟶ F₄) (d : F₄ ⟶ F₅)
      (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0),
      (ShortComplex.mk a b hab).Exact → (ShortComplex.mk b c hbc).Exact →
      (ShortComplex.mk c d hcd).Exact →
      IsTorsionCompletionCompleteSheaf X I F₁ → IsTorsionCompletionCompleteSheaf X I F₂ →
      IsTorsionCompletionCompleteSheaf X I F₄ → IsTorsionCompletionCompleteSheaf X I F₅ →
      IsTorsionCompletionCompleteSheaf X I F₃) ∧
    (∀ (F : ℕ → TorsionCompletionModules X A) (f : ∀ n : ℕ, F (n + 1) ⟶ F n),
      (∀ n : ℕ, IsTorsionCompletionCompleteSheaf X I (F n)) →
      IsTorsionCompletionCompleteSheaf X I (limit (Functor.ofOpSequence f))) ∧
    (∀ (F : TorsionCompletionModules X A) (n : ℕ), 1 ≤ n →
      IsAnnihilatedByModuleIdeal (torsionCompletionModuleRing X A)
        (torsionCompletionIdeal X (I ^ n)) (torsionCompletionIdealInclusion X (I ^ n)) F →
      IsTorsionCompletionCompleteSheaf X I F) ∧
    (∀ F : TorsionCompletionModules X A, IsLocallyPowerTorsionLimit X I F →
      IsTorsionCompletionCompleteSheaf X I F) ∧
    (∀ K : CochainComplex (TorsionCompletionModules X A) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) →
      (∀ i : ℤ, IsLocallyPowerTorsionLimit X I (K.X i)) →
      IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj K)) := by
  refine ⟨?_, completeSheaf_limit X I, ?_, completeSheaf_of_localTorsionLimit X I, ?_⟩
  · intro F₁ F₂ F₃ F₄ F₅ a b c d hab hbc hcd h₁ h₂ h₃ hF₁ hF₂ hF₄ hF₅
    exact completeSheaf_five X I a b c d hab hbc hcd h₁ h₂ h₃ hF₁ hF₂ hF₄ hF₅
  · intro F n _hn hF
    exact completeSheaf_of_powerTorsion X I F n hF
  · intro K _hbounded hK
    exact completeComplex_of_completeTerms X I K
      (fun i ↦ completeSheaf_of_localTorsionLimit X I (K.X i) (hK i))

end AlgebraicGeometry.Scheme
