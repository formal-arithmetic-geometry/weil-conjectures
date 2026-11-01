/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

/-! # Transfer of finite-coefficient adjunctions

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
node det-sp-et-proet-adjunction-transfer (blueprint: det-sp-et-proet-adjunction-transfer).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.AdjunctionTransfer

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The recorded finite-value etale constructibility intersected with finite Tor amplitude.
Source: blueprint det-sp-et-proet-adjunction-transfer, definition of Dctf
(blueprint: det-sp-et-proet-adjunction-transfer). -/
abbrev etaleProperty (T : Scheme.{u}) :=
  Etale.DerivedCategory.isBoundedConstructible A T ⊓
    _root_.DerivedCategory.finiteTorAmplitude (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The bounded etale objects included in the bounded-below derived category.
The lower bound is read directly from the recorded constructibility predicate.
Source: blueprint det-sp-et-proet-adjunction-transfer, bounded inputs in proof step 1
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def etaleToPlus (T : Scheme.{u}) :
    (etaleProperty A T).FullSubcategory ⥤
      _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ObjectProperty.ιOfLE (fun K hK ↦ by
    obtain ⟨a, b, _hab, h⟩ := hK.1.2
    exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ h i (Or.inl hi))⟩)

/-- The finite-coefficient pro-etale convention is etale bounded constructible origin,
intersected with the actual pro-etale Tor test against every degree-zero module sheaf.
Source: blueprint det-sp-et-proet-adjunction-transfer and def-weil-pbc-proetale-modules
(blueprint: det-sp-et-proet-adjunction-transfer). -/
abbrev proEtaleProperty (T : Scheme.{u}) :=
  (Etale.DerivedCategory.isBoundedConstructible A T).map
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⊓
    _root_.DerivedCategory.finiteTorAmplitude
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- Restrict the specified termwise inverse image, retaining its objects and maps.
Source: blueprint det-sp-et-proet-adjunction-transfer, comparison equivalences
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def comparison (T : Scheme.{u})
    (h : ∀ K, etaleProperty A T K → proEtaleProperty A T
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)) :
    (etaleProperty A T).FullSubcategory ⥤ (proEtaleProperty A T).FullSubcategory :=
  (proEtaleProperty A T).lift
    ((etaleProperty A T).ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory)
    (fun K ↦ h K.obj K.property)

/-- The ordinary etale compactification composite, restricted to Dctf.
Source: blueprint det-sp-et-proet-adjunction-transfer, chosen compactification
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def etaleLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, etaleProperty A X K → etaleProperty A Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (etaleProperty A X).FullSubcategory ⥤ (etaleProperty A Y).FullSubcategory :=
  (etaleProperty A Y).lift ((etaleProperty A X).ι ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun K ↦ h K.obj K.property)

/-- Inclusion of the generators in their recorded localizing closure.
Source: blueprint det-sp-et-proet-adjunction-transfer, Brown restriction
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def toLocalizing (T : Scheme.{u}) :
    (proEtaleProperty A T).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A T)).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hgen ↦ hgen K hK)

/-- The compactification functor on the same localizing closures.
Source: blueprint det-sp-et-proet-adjunction-transfer, Brown adjunction
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def localizingLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, CategoryTheory.localizingClosure (proEtaleProperty A X) K →
      CategoryTheory.localizingClosure (proEtaleProperty A Y)
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory :=
  (CategoryTheory.localizingClosure (proEtaleProperty A Y)).lift
    ((CategoryTheory.localizingClosure (proEtaleProperty A X)).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun K ↦ h K.obj K.property)

/-- Orthogonality to every shifted generator detects zero in its localizing closure.
The left orthogonal of the right orthogonal of the shift closure is localizing,
contains the generators, and hence contains the object being tested. -/
private theorem isZero_of_generator_vanishing
    {C : Type u} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (K : C) (hK : localizingClosure P K)
    (hz : ∀ M, P M → ∀ n : ℤ, ∀ g : M⟦n⟧ ⟶ K, g = 0) : IsZero K := by
  let B := (P.shiftClosure ℤ).rightOrthogonal
  let R := B.leftOrthogonal
  have hR : IsLocalizingSubcategory R := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I F hF hgen
    let _ := hF
    change R (colimit F)
    intro Z g hZ
    apply colimit.hom_ext
    intro i
    rw [comp_zero]
    exact hgen i.as (colimit.ι F i ≫ g) hZ
  have hPR : P ≤ R := by
    intro M hM N g hN
    exact hN g (P.le_shiftClosure _ hM)
  have hBK : B K := by
    intro M g hM
    obtain ⟨L, n, e, hL⟩ := hM
    apply (cancel_epi e.inv).1
    simpa using hz L hL n (e.inv ≫ g)
  exact (IsZero.iff_id_eq_zero K).2 (hK R hR hPR (𝟙 K) hBK)

/-- A map between objects of the localizing closure is an isomorphism when every
shifted generator sees a bijection. Its cone lies in the closure and is orthogonal
to the shifted generators by the exact Hom sequence. -/
private theorem isIso_of_generator_bijective
    {C : Type u} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) {H Y : C} (c : H ⟶ Y)
    (hH : localizingClosure P H) (hY : localizingClosure P Y)
    (hbij : ∀ (M : C), P M → ∀ m : ℤ,
      Function.Bijective (fun a : M⟦m⟧ ⟶ H ↦ a ≫ c)) : IsIso c := by
  have hbijshift (M : C) (hM : P M) (m n : ℤ) :
      Function.Injective (fun a : M⟦m⟧ ⟶ H⟦n⟧ ↦ a ≫ c⟦n⟧') := by
    let K := M⟦m⟧
    let adj := (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction
    let e : M⟦m + -n⟧ ≅ K⟦-n⟧ := (shiftFunctorAdd C m (-n)).app M
    have hinj (a b : K⟦-n⟧ ⟶ H) (hab : a ≫ c = b ≫ c) : a = b := by
      apply (cancel_epi e.hom).mp
      apply (hbij M hM (m + -n)).1
      simpa only [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hab
    intro a b hab
    apply (adj.homEquiv K H).symm.injective
    apply hinj
    have hh := congrArg (adj.homEquiv K Y).symm hab
    change (adj.homEquiv K Y).symm
      (a ≫ (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map c) =
      (adj.homEquiv K Y).symm
        (b ≫ (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map c) at hh
    rw [adj.homEquiv_naturality_right_symm,
      adj.homEquiv_naturality_right_symm] at hh
    exact hh
  obtain ⟨D, d, δ, hd⟩ := Pretriangulated.distinguished_cocone_triangle c
  have hD : localizingClosure P D := by
    intro Q hQ hPQ
    let _ := hQ.1
    let _ := hQ.2.1
    exact Q.ext_of_isTriangulatedClosed₃ _ hd (hH Q hQ hPQ) (hY Q hQ hPQ)
  have hz : IsZero D := isZero_of_generator_vanishing P D hD (by
    intro M hM m a
    have hδ : a ≫ δ = 0 := by
      apply hbijshift M hM m 1
      have hzero := Pretriangulated.comp_distTriang_mor_zero₃₁ _ hd
      change δ ≫ c⟦(1 : ℤ)⟧' = 0 at hzero
      simp only [Category.assoc, hzero, comp_zero, zero_comp]
    obtain ⟨b, hb⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hd a hδ
    obtain ⟨b', hb'⟩ := (hbij M hM m).2 b
    have hcd : c ≫ d = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hd
    change a = b ≫ d at hb
    rw [hb, ← hb', Category.assoc, hcd, comp_zero])
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hd).mp hz

/-- Compare the two adjoints by transposing the small counit under the large
adjunction. Naturality identifies composition with this map with the composite
of the two Hom equivalences. Shifted generators therefore detect an isomorphism. -/
private theorem rightAdjoint_preserves_generators
    {C : Type u} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type u} [Category D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsStableUnderShift ℤ] [P.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) (hF : ∀ M, P M → Q (F.obj M))
    (hLoc : ∀ M, localizingClosure P M → localizingClosure Q (F.obj M))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adSmall : Q.lift (P.ι ⋙ F) (fun M ↦ hF M.obj M.property) ⊣ G)
    (J : (localizingClosure Q).FullSubcategory ⥤ (localizingClosure P).FullSubcategory)
    (adBig : (localizingClosure Q).lift ((localizingClosure P).ι ⋙ F)
      (fun M ↦ hLoc M.obj M.property) ⊣ J)
    (N : Q.FullSubcategory) :
    P (J.obj ((ObjectProperty.ιOfLE
      (fun M hM _R _hR hgen ↦ hgen M hM)).obj N)).obj := by
  let iP : P.FullSubcategory ⥤ (localizingClosure P).FullSubcategory :=
    ObjectProperty.ιOfLE (fun M hM _R _hR hgen ↦ hgen M hM)
  let iQ : Q.FullSubcategory ⥤ (localizingClosure Q).FullSubcategory :=
    ObjectProperty.ιOfLE (fun M hM _R _hR hgen ↦ hgen M hM)
  let V := G.obj N
  let α : (iP.obj V) ⟶ J.obj (iQ.obj N) :=
    adBig.homEquiv _ _ (iQ.map (adSmall.counit.app N))
  have hi : IsIso α.hom := isIso_of_generator_bijective P α.hom (iP.obj V).property
    (J.obj (iQ.obj N)).property (by
      intro K hK n
      let M : P.FullSubcategory := ⟨K⟦n⟧, P.le_shift n K hK⟩
      let e : (K⟦n⟧ ⟶ V.obj) ≃ (K⟦n⟧ ⟶ (J.obj (iQ.obj N)).obj) :=
        (P.fullyFaithfulι.homEquiv (X := M) (Y := V)).symm |>.trans
          ((adSmall.homEquiv M N).symm |>.trans
            ((ObjectProperty.fullyFaithfulιOfLE _).homEquiv |>.trans
              (adBig.homEquiv (iP.obj M) (iQ.obj N) |>.trans
                ((localizingClosure P).fullyFaithfulι.homEquiv))))
      have he (g : K⟦n⟧ ⟶ V.obj) : e g = g ≫ α.hom := by
        change (adBig.homEquiv (iP.obj M) (iQ.obj N) (iQ.map
          ((adSmall.homEquiv M N).symm (ObjectProperty.homMk g)))).hom = _
        rw [Adjunction.homEquiv_counit]
        exact congrArg (fun f ↦ f.hom)
          (adBig.homEquiv_naturality_left (iP.map (ObjectProperty.homMk (X := M) (Y := V) g))
            (iQ.map (adSmall.counit.app N)))
      have heq : (fun g : K⟦n⟧ ⟶ V.obj ↦ g ≫ α.hom) = e :=
        funext (fun g ↦ (he g).symm)
      change Function.Bijective (fun g : K⟦n⟧ ⟶ V.obj ↦ g ≫ α.hom)
      rw [heq]
      exact e.bijective)
  let _ := hi
  exact P.prop_of_iso (asIso α.hom) V.property

private theorem boundedConstructible_iff (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨(DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1
      ⟨a, b, ?_, ?_⟩, fun i ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (Or.inl hi))
    · exact (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (Or.inr hi))
  · intro h
    obtain ⟨a, b, ha, hb⟩ :=
      (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 h.1
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (h.2 i),
      min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi

end AlgebraicGeometry.ProEtale.AdjunctionTransfer
