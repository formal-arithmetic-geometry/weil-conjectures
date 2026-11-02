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

/-- The same chosen compactification in the ordinary pro-etale coefficient presentation.
Source: blueprint det-sp-et-proet-adjunction-transfer, Rf_!
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def proEtaleLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, proEtaleProperty A X K → proEtaleProperty A Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (proEtaleProperty A X).FullSubcategory ⥤ (proEtaleProperty A Y).FullSubcategory :=
  (proEtaleProperty A Y).lift ((proEtaleProperty A X).ι ⋙
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
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

/-- Restrict a Brown right adjoint without changing its ambient objects or morphisms.
Source: blueprint det-sp-et-proet-adjunction-transfer, final conclusion
(blueprint: det-sp-et-proet-adjunction-transfer). -/
def brownRestriction {X Y : Scheme.{u}}
    (J : (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory)
    (h : ∀ N : (proEtaleProperty A Y).FullSubcategory,
      proEtaleProperty A X ((J.obj ((toLocalizing A Y).obj N)).obj)) :
    (proEtaleProperty A Y).FullSubcategory ⥤ (proEtaleProperty A X).FullSubcategory :=
  (proEtaleProperty A X).lift
    (toLocalizing A Y ⋙ J ⋙ (CategoryTheory.localizingClosure (proEtaleProperty A X)).ι) h

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

private theorem proEtaleProperty_iff (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    ProEtale.AdjunctionTransfer.proEtaleProperty A T K ↔
      ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨⟨L, hL, e⟩, hTor⟩
    exact ⟨⟨L, (boundedConstructible_iff A T L).1 hL, e⟩, hTor⟩
  · rintro ⟨⟨L, hL, e⟩, hTor⟩
    exact ⟨⟨L, (boundedConstructible_iff A T L).2 hL, e⟩, hTor⟩

private theorem proEtaleProperty_stableUnderShift
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (ProEtale.AdjunctionTransfer.proEtaleProperty A T).IsStableUnderShift ℤ := by
  refine ⟨fun n ↦ ⟨fun K hK ↦ ?_⟩⟩
  exact (proEtaleProperty_iff A T _).2
    (ProEtale.DerivedCategory.constructibleFiniteTor.shift ((proEtaleProperty_iff A T K).1 hK) n)

/-- Transfer an adjunction across the specified comparison equivalences and comparison iso.
The construction retains the quasi-inverse and actual counit, and restricts any Brown
adjunction to the generator subcategories with its unique counit-preserving comparison.
Source: blueprint det-sp-et-proet-adjunction-transfer, categorical proof paragraphs 1--3
(blueprint: det-sp-et-proet-adjunction-transfer). -/
theorem etaleProEtaleAdjunctionTransferOfComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hX : ∀ K, etaleProperty A X K → proEtaleProperty A X
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
    (hY : ∀ K, etaleProperty A Y K → proEtaleProperty A Y
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K))
    (eX : (etaleProperty A X).FullSubcategory ≌ (proEtaleProperty A X).FullSubcategory)
    (eY : (etaleProperty A Y).FullSubcategory ≌ (proEtaleProperty A Y).FullSubcategory)
    (_heX : eX.functor = comparison A X hX) (_heY : eY.functor = comparison A Y hY)
    (hEt : ∀ K, etaleProperty A X K → etaleProperty A Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
    (hPro : ∀ K, proEtaleProperty A X K → proEtaleProperty A Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
    (cf : etaleLowerShriek A c hEt ⋙ eY.functor ≅
      eX.functor ⋙ proEtaleLowerShriek A c hPro)
    (G : (etaleProperty A Y).FullSubcategory ⥤ (etaleProperty A X).FullSubcategory)
    (adjEt : etaleLowerShriek A c hEt ⊣ G) :
    ∃ adjPro : proEtaleLowerShriek A c hPro ⊣ (eY.inverse ⋙ G ⋙ eX.functor),
      (∀ N : (etaleProperty A Y).FullSubcategory,
        (adjPro.counit.app (eY.functor.obj N)) =
          (proEtaleLowerShriek A c hPro).map
              (eX.functor.map (G.map (eY.unitIso.inv.app N))) ≫
            cf.inv.app (G.obj N) ≫ eY.functor.map (adjEt.counit.app N)) ∧
      (∀ (hLoc : ∀ K, CategoryTheory.localizingClosure (proEtaleProperty A X) K →
          CategoryTheory.localizingClosure (proEtaleProperty A Y)
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
        (J : (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory ⥤
          (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory)
        (adjBrown : localizingLowerShriek A c hLoc ⊣ J),
        ∃ hJ : ∀ N : (proEtaleProperty A Y).FullSubcategory,
            proEtaleProperty A X ((J.obj ((toLocalizing A Y).obj N)).obj),
          ∃! γ : (eY.inverse ⋙ G ⋙ eX.functor) ≅ brownRestriction A J hJ,
            ∀ N : (proEtaleProperty A Y).FullSubcategory,
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
                  ((γ.hom.app N).hom) ≫
                (adjBrown.counit.app ((toLocalizing A Y).obj N)).hom =
              (adjPro.counit.app N).hom) := by
  classical
  let e := eX
  let ac : (etaleLowerShriek A c hEt) ⋙ eY.functor ⊣ eY.inverse ⋙ G :=
    adjEt.comp eY.toAdjunction
  let j : e.inverse ⋙ ((etaleLowerShriek A c hEt) ⋙ eY.functor) ≅
      proEtaleLowerShriek A c hPro :=
    Functor.isoWhiskerLeft e.inverse cf ≪≫
      (Functor.associator e.inverse e.functor (proEtaleLowerShriek A c hPro)).symm ≪≫
      Functor.isoWhiskerRight e.counitIso (proEtaleLowerShriek A c hPro) ≪≫
      Functor.leftUnitor (proEtaleLowerShriek A c hPro)
  let adjPro : proEtaleLowerShriek A c hPro ⊣
      eY.inverse ⋙ G ⋙ eX.functor :=
    (e.symm.toAdjunction.comp ac).ofNatIsoLeft j
  refine ⟨adjPro, ?_, ?_⟩
  · intro N
    rw [Adjunction.ofNatIsoLeft_counit]
    change j.inv.app (eX.functor.obj (G.obj (eY.inverse.obj (eY.functor.obj N)))) ≫
      (e.symm.toAdjunction.comp ac).counit.app (eY.functor.obj N) = _
    rw [Adjunction.comp_counit_app]
    change j.inv.app _ ≫
      ((etaleLowerShriek A c hEt) ⋙ eY.functor).map (e.unitIso.inv.app _) ≫
      ac.counit.app (eY.functor.obj N) = _
    dsimp [j]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    change (proEtaleLowerShriek A c hPro).map (e.counitIso.inv.app _) ≫
      cf.inv.app _ ≫ ((etaleLowerShriek A c hEt) ⋙ eY.functor).map
        (e.unitIso.inv.app _) ≫ ac.counit.app _ = _
    rw [← cf.inv.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc]
    simp only [e, Equivalence.counitIso_functor_comp, Functor.id_obj]
    rw [(proEtaleLowerShriek A c hPro).map_id, Category.id_comp]
    dsimp [ac]
    rw [Adjunction.comp_counit_app]
    change cf.inv.app _ ≫ eY.functor.map (adjEt.counit.app _) ≫
      eY.counitIso.hom.app (eY.functor.obj N) = _
    rw [eY.counit_app_functor]
    rw [← eY.functor.map_comp]
    have hn := adjEt.counit.naturality (eY.unitIso.inv.app N)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    erw [← hn]
    rw [eY.functor.map_comp]
    erw [← cf.inv.naturality_assoc]
    rfl
  · intro hLoc J adjBrown
    have hJ : ∀ N : (proEtaleProperty A Y).FullSubcategory,
        proEtaleProperty A X ((J.obj ((toLocalizing A Y).obj N)).obj) := by
      have : (proEtaleProperty A X).IsStableUnderShift ℤ := proEtaleProperty_stableUnderShift A X
      exact rightAdjoint_preserves_generators (proEtaleProperty A X) (proEtaleProperty A Y)
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
        hPro hLoc (eY.inverse ⋙ G ⋙ eX.functor) adjPro J adjBrown
    let commL : toLocalizing A X ⋙ localizingLowerShriek A c hLoc ≅
        proEtaleLowerShriek A c hPro ⋙ toLocalizing A Y := Iso.refl _
    let commR : toLocalizing A Y ⋙ J ≅ brownRestriction A J hJ ⋙ toLocalizing A X :=
      Iso.refl _
    let adjSmall : proEtaleLowerShriek A c hPro ⊣ brownRestriction A J hJ :=
      adjBrown.restrictFullyFaithful
        (ObjectProperty.fullyFaithfulιOfLE _)
        (ObjectProperty.fullyFaithfulιOfLE _) commL commR
    have hc (N : (proEtaleProperty A Y).FullSubcategory) :
        (adjSmall.counit.app N).hom =
          (adjBrown.counit.app ((toLocalizing A Y).obj N)).hom := by
      have hh := adjBrown.map_restrictFullyFaithful_counit_app
        (ObjectProperty.fullyFaithfulιOfLE _)
        (ObjectProperty.fullyFaithfulιOfLE _) commL commR N
      change (toLocalizing A Y).map (adjSmall.counit.app N) =
        𝟙 _ ≫ (localizingLowerShriek A c hLoc).map (𝟙 _) ≫
          adjBrown.counit.app ((toLocalizing A Y).obj N) at hh
      rw [(localizingLowerShriek A c hLoc).map_id] at hh
      simp only [Category.id_comp] at hh
      exact congrArg (fun g ↦ g.hom) hh
    refine ⟨hJ, adjPro.rightAdjointUniq adjSmall, ?_, ?_⟩
    · intro N
      rw [← hc]
      exact congrArg (fun g ↦ g.hom)
        (adjPro.rightAdjointUniq_hom_app_counit adjSmall N)
    · intro γ hγ
      apply Iso.ext
      apply NatTrans.ext
      funext N
      apply (adjSmall.homEquiv _ _).symm.injective
      rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
      apply (proEtaleProperty A Y).ι.map_injective
      change (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((γ.hom.app N).hom) ≫ (adjSmall.counit.app N).hom = _
      rw [hc]
      exact hγ N

end AlgebraicGeometry.ProEtale.AdjunctionTransfer
