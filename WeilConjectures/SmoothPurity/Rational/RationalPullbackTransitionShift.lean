/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
import WeilConjectures.SmoothPurity.Sf.SfFrameworkThetaShiftCompatibility
import WeilConjectures.FourierTransform.CompletedScalarShift
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackCompletionNormalization
import all WeilConjectures.SmoothPurity.Sf.SfRationalScalarExactOfIntegral
import WeilConjectures.CategoryTheory.RoosShift.RoosCommShift
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelConstruction
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Scalar compatibility of normalized pullback shifts

Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph.
(blueprint: lem-sf-rational-pullback-transition-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback

/-- Shift compatibility of a natural transformation can be checked after precomposition
with a shift-compatible functor that is surjective on objects. -/
theorem natTrans_commShift_of_whiskerLeft
    {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift D ℤ]
    (Q : C ⥤ C') [Q.CommShift ℤ] {F G : C' ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (hQ : ∀ X, ∃ Y, Q.obj Y = X)
    (h : NatTrans.CommShift (Functor.whiskerLeft Q τ) ℤ) : NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  ext X
  obtain ⟨Y, rfl⟩ := hQ X
  have hY := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ) n Y
  simp only [Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
    Category.assoc] at hY
  rw [← τ.naturality_assoc] at hY
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact (cancel_epi _).1 hY

/-- Shift compatibility of a natural transformation can be checked after precomposition
with an essentially surjective shift-compatible functor. -/
theorem natTrans_commShift_of_whiskerLeft_essSurj
    {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift D ℤ]
    (Q : C ⥤ C') [Q.CommShift ℤ] {F G : C' ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (hQ : ∀ X, ∃ Y, Nonempty (Q.obj Y ≅ X))
    (h : NatTrans.CommShift (Functor.whiskerLeft Q τ) ℤ) : NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  ext X
  obtain ⟨Y, ⟨e⟩⟩ := hQ X
  have hY := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ) n Y
  simp only [Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
    Category.assoc] at hY
  rw [← τ.naturality_assoc] at hY
  have hY' := (cancel_epi _).1 hY
  have hF := (F.commShiftIso n).hom.naturality e.hom
  have hG := (G.commShiftIso n).hom.naturality e.hom
  simp only [Functor.comp_map] at hF hG
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_epi (F.map (e.hom⟦n⟧')), reassoc_of% hF, ← Functor.map_comp,
    τ.naturality, Functor.map_comp, reassoc_of% hY', ← hG, τ.naturality_assoc]

/-- Conjugating a morphism by transport isomorphisms, two of them images of transports
under functors, does not change it up to heterogeneous equality. -/
theorem map_eqToHom_conj_heq {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    (F : C ⥤ D) (G : C' ⥤ D) {a b : C} {e e' : C'} {x y : D} (p : a = b)
    (q : F.obj b = x) (g : x ⟶ y) (r : y = G.obj e) (s : e = e') :
    HEq (F.map (eqToHom p) ≫ eqToHom q ≫ g ≫ eqToHom r ≫ G.map (eqToHom s)) g := by
  cases p
  cases s
  cases q
  cases r
  simp

/-- The identity-component comparison between a functor on a localized category and
an integral model whose objects and morphisms it reproduces. -/
def localizedEqToIso {C D C' D' : Type*} [Category* C] [Category* D] [Category* C']
    [Category* D'] (Q : C ⥤ C') (Q' : D ⥤ D') (T : C ⥤ D) (F : C' ⥤ D')
    (hF : ∀ X, F.obj (Q.obj X) = Q'.obj (T.obj X))
    (hm : ∀ {X Y : C} (f : X ⟶ Y), HEq (F.map (Q.map f)) (Q'.map (T.map f))) :
    Q ⋙ F ≅ T ⋙ Q' :=
  NatIso.ofComponents (fun X ↦ eqToIso (hF X)) (fun {X Y} f ↦ by
    simp only [Functor.comp_map, eqToIso.hom]
    exact eq_of_heq ((comp_eqToHom_heq _ _).trans
      ((hm f).trans (eqToHom_comp_heq _ _).symm)))

/-- The identity-component comparison commutes with shifts once the degree-one shift
of the localized functor is the localization of the integral one. -/
theorem localizedEqToIso_commShift {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ]
    [HasShift D' ℤ] (Q : C ⥤ C') (Q' : D ⥤ D') (T : C ⥤ D) (F : C' ⥤ D')
    [Q.CommShift ℤ] [Q'.CommShift ℤ] [T.CommShift ℤ] [F.CommShift ℤ]
    (hF : ∀ X, F.obj (Q.obj X) = Q'.obj (T.obj X))
    (hm : ∀ {X Y : C} (f : X ⟶ Y), HEq (F.map (Q.map f)) (Q'.map (T.map f)))
    (hQ : ∀ X, Q.obj (X⟦(1 : ℤ)⟧) = (Q.obj X)⟦(1 : ℤ)⟧)
    (hQ' : ∀ X, Q'.obj (X⟦(1 : ℤ)⟧) = (Q'.obj X)⟦(1 : ℤ)⟧)
    (nQ : ∀ X, HEq ((Q.commShiftIso (1 : ℤ)).hom.app X) (𝟙 (Q.obj (X⟦(1 : ℤ)⟧))))
    (nQ' : ∀ X, HEq ((Q'.commShiftIso (1 : ℤ)).hom.app X) (𝟙 (Q'.obj (X⟦(1 : ℤ)⟧))))
    (nF : ∀ X, HEq ((F.commShiftIso (1 : ℤ)).hom.app (Q.obj X))
      (Q'.map ((T.commShiftIso (1 : ℤ)).hom.app X))) :
    NatTrans.CommShift (localizedEqToIso Q Q' T F hF hm).hom ℤ :=
  commShift_of_one _
    (localized_comparison_core Q Q' T F hF _ (fun _ ↦ rfl) hQ hQ' nQ nQ' nF)

/-- The rationalization of a shift-compatible integral functor: the identity-component
comparison with a rational functor normalized at shift one commutes with all shifts. -/
theorem rationalLocalizedEqToIso_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (E' : Type u) [Field E'] [Algebra ℚ_[l] E'] [FiniteDimensional ℚ_[l] E']
    (W W' : Scheme.{u})
    (T : sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E' W')
    (F : sfRationalConstructibleCategory l E W ⥤ sfRationalConstructibleCategory l E' W')
    [T.CommShift ℤ] [F.CommShift ℤ]
    (hF : ∀ X, F.obj ((sfRationalConstructibleLocalization l E W).obj X) =
      (sfRationalConstructibleLocalization l E' W').obj (T.obj X))
    (hm : ∀ {X Y} (f : X ⟶ Y), HEq (F.map ((sfRationalConstructibleLocalization l E W).map f))
      ((sfRationalConstructibleLocalization l E' W').map (T.map f)))
    (nF : ∀ X, HEq ((F.commShiftIso (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l E W).obj X))
      ((sfRationalConstructibleLocalization l E' W').map
        ((T.commShiftIso (1 : ℤ)).hom.app X))) :
    NatTrans.CommShift (localizedEqToIso (sfRationalConstructibleLocalization l E W)
      (sfRationalConstructibleLocalization l E' W') T F hF hm).hom ℤ :=
  localizedEqToIso_commShift _ _ T F hF hm
    (fun X ↦ (Functor.congr_obj (sfRationalTriangulationDatum l E W).choose_spec.choose_spec.1
      ((sfRationalConstructibleLocalization l E W).obj X)).symm)
    (fun X ↦ (Functor.congr_obj (sfRationalTriangulationDatum l E' W').choose_spec.choose_spec.1
      ((sfRationalConstructibleLocalization l E' W').obj X)).symm)
    ((sfRationalTriangulationDatum l E W).choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.1)
    ((sfRationalTriangulationDatum l E' W').choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.1)
    nF

/-- Every rational constructible object is the localization of its integral model. -/
theorem sfRationalConstructibleLocalization_obj_surjective (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (K : sfRationalConstructibleCategory l E W) :
    ∃ J, (sfRationalConstructibleLocalization l E W).obj J = K :=
  ⟨K.obj, rfl⟩

/-- An equality of functors transports a shift structure so that its identity comparison
commutes with shifts. -/
theorem eqToIso_commShift
    {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ] [HasShift B ℤ]
    {F G : A ⥤ B} (h : F = G) (q : G.CommShift ℤ) :
    @NatTrans.CommShift _ _ _ _ _ _ (eqToIso h).hom ℤ _ _ _
      (cast (congrArg (fun H : A ⥤ B ↦ H.CommShift ℤ) h.symm) q) q := by
  cases h
  constructor
  intro n
  ext K
  simp

/-- The ordinary-to-completed comparison on integral constructible objects, in
functor form. -/
noncomputable def sfIntegralOrdinaryScalarComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W ⋙ (sfIntegralConstructible l L W).ι :=
  sfIntegralOrdinaryComparison l E L ι W

/-- The ordinary-to-completed comparison is the normalized scalar completion map. -/
theorem sfIntegralOrdinaryScalarComparison_hom_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) (K : sfIntegralConstructibleCategory l E W) :
    (sfIntegralOrdinaryScalarComparison l E L ι W).hom.app K =
      (scalarCompletion l E L ι W).app K.obj := by
  let χ := scalarCompletion l E L ι W
  let (J : sfIntegralConstructibleCategory l E W) : IsIso (χ.app J.obj) :=
    (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.2 J.obj J.property.1
  let e : (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (sfIntegralConstructible l E W).ι ⋙ integralScalarExtension l E L ι W :=
    NatIso.ofComponents (fun J ↦ asIso (χ.app J.obj)) (fun f ↦ χ.naturality f.hom)
  have he : e = sfIntegralOrdinaryComparison l E L ι W := by
    apply (sfIntegralOrdinaryComparison_existsUnique l E L ι W).unique
    · intro P hP
      exact (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 P
    · exact (sfIntegralOrdinaryComparison_existsUnique l E L ι W).exists.choose_spec
  exact (congrArg (fun a ↦ a.hom.app K) he).symm

/-- The ordinary-to-completed comparison commutes with the ordinary derived scalar shift
and the normalized integral transition shift. -/
theorem sfIntegralOrdinaryScalarComparison_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (W : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :
    letI : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω W E L h
    NatTrans.CommShift (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom ℤ := by
  constructor
  intro n
  ext K
  have hn := (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W).exists.choose_spec n K
  have hn' := eq_of_heq hn
  change _ = (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).inv.app (K⟦n⟧) ≫
      (((sfIntegralConstructible l (Coefficient.{u} l Ω E) W).ι ⋙
        integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).commShiftIso n).hom.app K ≫
      (shiftFunctor (DerivedCategory (integralTowerModules l (Coefficient.{u} l Ω L) W)) n).map
        ((sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).hom.app K) at hn'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc, ObjectProperty.ι_map]
  change _ = (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom.app (K⟦n⟧) ≫ _
  rw [← Category.assoc, hn']
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]

/-- If two morphisms agree up to heterogeneous equality and the second factor is an
identity transport, then composing with it does not change the first factor. -/
theorem comp_heq_of_heq_id {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hYZ : Y = Z) (hg : HEq g (𝟙 Z)) : HEq (f ≫ g) f := by
  subst hYZ
  rw [eq_of_heq hg, Category.comp_id]

/-- Precomposing with the image of an identity transport does not change a morphism. -/
theorem map_comp_heq_of_heq_id {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y : C} {Z : D} (g : X ⟶ Y) (k : F.obj Y ⟶ Z) (hXY : X = Y) (hg : HEq g (𝟙 Y)) :
    HEq (F.map g ≫ k) k := by
  subst hXY
  rw [eq_of_heq hg, F.map_id, Category.id_comp]

/-- The inclusion of a shift-stable full subcategory has identity shift comparisons. -/
theorem fullSubcategory_ι_commShiftIso_hom_app_heq {C : Type*} [Category* C] [HasShift C ℤ]
    (P : ObjectProperty C) [P.IsStableUnderShift ℤ] (n : ℤ) (Z : P.FullSubcategory) :
    HEq ((P.ι.commShiftIso n).hom.app Z) (𝟙 (Z.obj⟦n⟧)) := by
  with_unfolding_all exact HEq.rfl

/-- Shifted objects of a shift-stable full subcategory are the ambient shifts. -/
theorem fullSubcategory_shift_obj_eq {C : Type*} [Category* C] [HasShift C ℤ]
    (P : ObjectProperty C) [P.IsStableUnderShift ℤ] (n : ℤ) (Z : P.FullSubcategory) :
    (Z⟦n⟧).obj = Z.obj⟦n⟧ := by
  with_unfolding_all rfl

/-- A lifted functor whose shift comparisons are the ambient ones commutes with the
identity comparison to the ambient functor. -/
theorem liftCompιIso_commShift_of_heq {C D : Type*} [Category* C]
    [Category* D] [HasShift C ℤ] [HasShift D ℤ] (P : ObjectProperty D)
    [P.IsStableUnderShift ℤ] (G : C ⥤ D) (hG : ∀ X, P (G.obj X)) [G.CommShift ℤ]
    {_ : (P.lift G hG).CommShift ℤ}
    (hs : ∀ X (n : ℤ), HEq (((P.lift G hG).commShiftIso n).hom.app X).hom
      ((G.commShiftIso n).hom.app X)) :
    NatTrans.CommShift (P.liftCompιIso G hG).hom ℤ := by
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, ObjectProperty.liftCompιIso, Iso.refl_hom,
    NatTrans.id_app, ObjectProperty.ι_map]
  apply eq_of_heq
  exact (comp_heq_of_heq_id _ _ rfl (heq_of_eq ((shiftFunctor D n).map_id _))).trans
    ((comp_heq_of_heq_id _ _ (fullSubcategory_shift_obj_eq P n _)
    (fullSubcategory_ι_commShiftIso_hom_app_heq P n _)).trans
      ((hs X n).trans (heq_of_eq (Category.id_comp _)).symm))

section ChainShift
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Limits Opposite
attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor
  CochainComplex.shiftFunctor

section RoosCoordinates
variable {A S : Type*} [Category A] [Abelian A] [HasCountableProducts A]
  [Category S] [HasShift S ℤ] (K : S ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ))
  [(K ⋙ integralOperationsRoosFunctor).CommShift ℤ]
  (p : ∀ (X : S) (m : ℤ), (∏ᶜ fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≅
    (∏ᶜ fun n ↦ (K.obj X).obj (op n))⟦m⟧)

/-- The first-inclusion coordinate equation of a shift on a Roos functor. -/
def RoosShiftInl : Prop :=
  ∀ (X : S) (m j : ℤ),
    (CochainComplex.mappingCocone.inl (scalarRoosBoundary (K.obj (X⟦m⟧)))).v j j
        (by omega) ≫
      (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X).f j =
    (p X m).hom.f j ≫
      (CochainComplex.mappingCocone.inl (scalarRoosBoundary (K.obj X))).v (j + m) (j + m)
        (by omega) ≫
      (CochainComplex.shiftFunctorObjXIso ((K ⋙ integralOperationsRoosFunctor).obj X)
        m j (j + m) rfl).inv

/-- The second-inclusion coordinate equation of a shift on a Roos functor. -/
def RoosShiftInr : Prop :=
  ∀ (X : S) (m i j : ℤ) (h : i + 1 = j),
    (CochainComplex.mappingCocone.inr (scalarRoosBoundary (K.obj (X⟦m⟧)))).1.v i j h ≫
      (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X).f j =
    m.negOnePow • ((p X m).hom.f i ≫
      (CochainComplex.mappingCocone.inr (scalarRoosBoundary (K.obj X))).1.v (i + m) (j + m)
        (by omega) ≫
      (CochainComplex.shiftFunctorObjXIso ((K ⋙ integralOperationsRoosFunctor).obj X)
        m j (j + m) rfl).inv)

/-- The first projection of a Roos shift is the product shift. -/
theorem roosShift_fst (hl : RoosShiftInl K p) (hr : RoosShiftInr K p) (X : S) (m : ℤ) :
    ((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K.obj X)))⟦m⟧' =
      CochainComplex.mappingCocone.fst (scalarRoosBoundary (K.obj (X⟦m⟧))) ≫ (p X m).hom := by
  ext j
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  apply SignedCoconeShift.cocone_ext_from _ j
  · rw [← Category.assoc]
    erw [hl X m j]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc]
    erw [Category.id_comp, CochainComplex.mappingCocone.inl_v_fst_f,
      ← Category.assoc, CochainComplex.mappingCocone.inl_v_fst_f]
    simp
  · rw [← Category.assoc]
    erw [hr X m (j - 1) j (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc, Linear.units_smul_comp]
    erw [Category.id_comp, CochainComplex.mappingCocone.inr_v_fst_f,
      ← Category.assoc, CochainComplex.mappingCocone.inr_v_fst_f]
    simp

/-- The second projection of a Roos shift is the signed product shift. -/
theorem roosShift_snd (hl : RoosShiftInl K p) (hr : RoosShiftInr K p) (X : S) (m j : ℤ) :
    (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X).f j ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v (j + m) (j - 1 + m)
          (by omega) =
      m.negOnePow • ((CochainComplex.mappingCocone.snd
        (scalarRoosBoundary (K.obj (X⟦m⟧)))).v j (j - 1) (by omega) ≫ (p X m).hom.f (j - 1)) := by
  apply SignedCoconeShift.cocone_ext_from _ j
  · rw [← Category.assoc]
    erw [hl X m j]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc, Linear.comp_units_smul]
    erw [Category.id_comp, CochainComplex.mappingCocone.inl_v_snd_v,
      ← Category.assoc, CochainComplex.mappingCocone.inl_v_snd_v]
    simp
  · rw [← Category.assoc]
    erw [hr X m (j - 1) j (by omega)]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
    erw [Category.id_comp, CochainComplex.mappingCocone.inr_v_snd_v,
      ← Category.assoc, CochainComplex.mappingCocone.inr_v_snd_v]
    simp

end RoosCoordinates

/-- Maps into a mapping cocone are determined by their two coordinates. -/
theorem mappingCocone_hom_ext_to {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) {T : C} (k q : ℤ) (hkq : k + -1 = q)
    {u v : T ⟶ (CochainComplex.mappingCocone φ).X k}
    (h₁ : u ≫ (CochainComplex.mappingCocone.fst φ).f k =
      v ≫ (CochainComplex.mappingCocone.fst φ).f k)
    (h₂ : u ≫ (CochainComplex.mappingCocone.snd φ).v k q hkq =
      v ≫ (CochainComplex.mappingCocone.snd φ).v k q hkq) : u = v := by
  rw [← Category.comp_id u, ← Category.comp_id v, ← CochainComplex.mappingCocone.id_X φ k q hkq]
  simp only [Preadditive.comp_add, ← Category.assoc, h₁, h₂]

section ScalarRoosShift
variable {A B S S' : Type*} [Category A] [Abelian A] [HasCountableProducts A]
  [Category B] [Abelian B] [HasCountableProducts B]
  [Category S] [HasShift S ℤ] [Category S'] [HasShift S' ℤ]
  (K : S ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ)) (K' : S' ⥤ (ℕᵒᵖ ⥤ CochainComplex B ℤ))
  (G : S ⥤ S') [G.CommShift ℤ] (O : A ⥤ B) [O.Additive]
  [eC : (K ⋙ integralOperationsRoosFunctor).CommShift ℤ]
  [eC' : (K' ⋙ integralOperationsRoosFunctor).CommShift ℤ]
  (p : ∀ (X : S) (m : ℤ), (∏ᶜ fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≅
    (∏ᶜ fun n ↦ (K.obj X).obj (op n))⟦m⟧)
  (p' : ∀ (X : S') (m : ℤ), (∏ᶜ fun n ↦ (K'.obj (X⟦m⟧)).obj (op n)) ≅
    (∏ᶜ fun n ↦ (K'.obj X).obj (op n))⟦m⟧)
  (α : K ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj (O.mapHomologicalComplex (.up ℤ)) ⟶
    G ⋙ K')

/-- The Roos scalar/tower chain comparison as a transformation of composite functors. -/
private noncomputable def scalarRoosChain :
    (K ⋙ integralOperationsRoosFunctor) ⋙ O.mapHomologicalComplex (.up ℤ) ⟶
      G ⋙ (K' ⋙ integralOperationsRoosFunctor) where
  app X := scalarRoosMap O (K.obj X) ≫ integralOperationsRoosMap (α.app X)
  naturality _ _ a := (scalarRoosTransformation K K' G O α).naturality a

omit [HasShift S ℤ] [HasShift S' ℤ] [G.CommShift ℤ] eC eC' in
/-- The first coordinate of the Roos chain comparison. -/
private theorem scalarRoosChain_fst (X : S) :
    (scalarRoosChain K K' G O α).app X ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary (K'.obj (G.obj X))) =
      (O.mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K.obj X))) ≫
        piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n ↦ (α.app X).app (op n)) := by
  dsimp only [scalarRoosChain]
  rw [Category.assoc]
  erw [(scalarRoosTowerCoordinates (α.app X)).1]
  rw [← Category.assoc]
  erw [(scalarRoosCoordinates O (K.obj X)).1]
  rw [Category.assoc]

omit [HasShift S ℤ] [HasShift S' ℤ] [G.CommShift ℤ] eC eC' in
/-- The second coordinate of the Roos chain comparison, after a product projection. -/
private theorem scalarRoosChain_snd_π (X : S) (k q : ℤ) (h : k + -1 = q) (n : ℕ) :
    ((scalarRoosChain K K' G O α).app X).f k ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary (K'.obj (G.obj X)))).v k q h ≫
        (Limits.Pi.π (fun n ↦ (K'.obj (G.obj X)).obj (op n)) n).f q =
      O.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v k q h ≫
        (Limits.Pi.π (fun n ↦ (K.obj X).obj (op n)) n).f q) ≫ ((α.app X).app (op n)).f q := by
  dsimp only [scalarRoosChain]
  rw [HomologicalComplex.comp_f, Category.assoc]
  erw [reassoc_of% ((scalarRoosTowerCoordinates (α.app X)).2 k q h)]
  have hπ := congrArg (fun z ↦ z.f q) (Limits.Pi.map_π (fun n ↦ (α.app X).app (op n)) n)
  simp only [HomologicalComplex.comp_f] at hπ
  have hs : (scalarRoosMap O (K.obj X)).f k ≫
      (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary (K.obj X ⋙ O.mapHomologicalComplex (.up ℤ)))).v k q h ≫
      (Limits.Pi.π (fun n ↦ (O.mapHomologicalComplex (.up ℤ)).obj ((K.obj X).obj (op n))) n).f q =
      O.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v k q h ≫
        (Limits.Pi.π (fun n ↦ (K.obj X).obj (op n)) n).f q) :=
    (scalarRoosMap_existsUnique O (K.obj X)).exists.choose_spec.2 k q h n
  erw [hπ]
  exact (reassoc_of% hs) (((α.app X).app (op n)).f q)

omit [HasShift S ℤ] [HasShift S' ℤ] [G.CommShift ℤ] eC eC' in
/-- The second coordinate of the Roos chain comparison. -/
private theorem scalarRoosChain_snd (X : S) (k q : ℤ) (h : k + -1 = q) :
    ((scalarRoosChain K K' G O α).app X).f k ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary (K'.obj (G.obj X)))).v k q h =
      O.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary (K.obj X))).v k q h) ≫
        (piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n))).f q ≫
        (Limits.Pi.map (fun n ↦ (α.app X).app (op n))).f q := by
  apply (isLimitOfHasProductOfPreservesLimit (HomologicalComplex.eval B (.up ℤ) q)
    (fun n ↦ (K'.obj (G.obj X)).obj (op n))).hom_ext
  rintro ⟨n⟩
  simp only [Fan.mk_π_app, HomologicalComplex.eval_map, Category.assoc]
  rw [scalarRoosChain_snd_π]
  have hπ := congrArg (fun z ↦ z.f q) (Limits.Pi.map_π (fun n ↦ (α.app X).app (op n)) n)
  have hc := congrArg (fun z ↦ z.f q) (piComparison_comp_π (O.mapHomologicalComplex (.up ℤ))
    (fun n ↦ (K.obj X).obj (op n)) n)
  simp only [HomologicalComplex.comp_f] at hπ hc
  erw [hπ, reassoc_of% hc, O.map_comp_assoc]
  rfl

/-- The Roos chain comparison commutes with Roos shifts satisfying the signed coordinate
equations, given the product square. -/
private theorem scalarRoosChain_commShift (hl : RoosShiftInl K p) (hr : RoosShiftInr K p)
    (hl' : RoosShiftInl K' p') (hr' : RoosShiftInr K' p')
    (hprod : ∀ (X : S) (m : ℤ),
      (O.mapHomologicalComplex (.up ℤ)).map (p X m).hom ≫
        ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
        (piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n)) ≫
          Limits.Pi.map (fun n ↦ (α.app X).app (op n)))⟦m⟧' =
      piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≫
        Limits.Pi.map (fun n ↦ (α.app (X⟦m⟧)).app (op n)) ≫
        Limits.Pi.map (fun n ↦ (K'.map ((G.commShiftIso m).hom.app X)).app (op n)) ≫
        (p' (G.obj X) m).hom) :
    NatTrans.CommShift (scalarRoosChain K K' G O α) ℤ := by
  constructor
  intro m
  ext X j
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    Functor.commShiftIso_comp_hom_app, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  have H : ((O.mapHomologicalComplex (.up ℤ)).map
        (((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app X) ≫
      ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
      ((scalarRoosChain K K' G O α).app X)⟦m⟧') ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K'.obj (G.obj X))))⟦m⟧' =
      ((scalarRoosChain K K' G O α).app (X⟦m⟧) ≫
        (K' ⋙ integralOperationsRoosFunctor).map ((G.commShiftIso m).hom.app X) ≫
        ((K' ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app (G.obj X)) ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary (K'.obj (G.obj X))))⟦m⟧' := by
    simp only [Category.assoc, ← Functor.map_comp, scalarRoosChain_fst]
    rw [Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc,
      ← Functor.map_comp_assoc, roosShift_fst K p hl hr X m, Functor.map_comp_assoc, hprod,
      roosShift_fst K' p' hl' hr' (G.obj X) m]
    have ht := (scalarRoosTowerCoordinates (K'.map ((G.commShiftIso m).hom.app X))).1
    erw [reassoc_of% ht]
    erw [reassoc_of% (scalarRoosChain_fst K K' G O α (X⟦m⟧))]
  erw [Category.comp_id]
  apply mappingCocone_hom_ext_to (scalarRoosBoundary (K'.obj (G.obj X))) (j + m) (j - 1 + m)
    (by omega)
  · have h := congrArg (fun z ↦ z.f j) H
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.assoc] at h
    erw [Category.id_comp] at h
    simpa only [Category.assoc] using h
  · simp only [Category.assoc]
    rw [scalarRoosChain_snd, roosShift_snd K' p' hl' hr' (G.obj X) m j, Linear.comp_units_smul,
      Linear.comp_units_smul]
    have ht := (scalarRoosTowerCoordinates (K'.map ((G.commShiftIso m).hom.app X))).2 j (j - 1)
      (by omega)
    erw [reassoc_of% ht]
    erw [reassoc_of% (scalarRoosChain_snd K K' G O α (X⟦m⟧) j (j - 1) (by omega))]
    rw [Functor.mapHomologicalComplex_map_f, ← O.map_comp_assoc]
    erw [roosShift_snd K p hl hr X m j]
    have hp := congrArg (fun z ↦ z.f (j - 1)) (hprod X m)
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f] at hp
    erw [Category.id_comp] at hp
    rw [Units.smul_def, Units.smul_def, Functor.map_zsmul, Preadditive.zsmul_comp]
    congr 1
    rw [O.map_comp, Category.assoc]
    erw [hp]

omit eC eC' in
/-- The product square for the Roos chain comparison follows from level squares. -/
private theorem scalarRoos_productSquare
    (e : ∀ (X : S) (m : ℤ) (n : ℕ), (K.obj (X⟦m⟧)).obj (op n) ≅ ((K.obj X).obj (op n))⟦m⟧)
    (e' : ∀ (X : S') (m : ℤ) (n : ℕ), (K'.obj (X⟦m⟧)).obj (op n) ≅ ((K'.obj X).obj (op n))⟦m⟧)
    (hp : ∀ X m n, (p X m).hom ≫ (Limits.Pi.π (fun n ↦ (K.obj X).obj (op n)) n)⟦m⟧' =
      Limits.Pi.π (fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) n ≫ (e X m n).hom)
    (hp' : ∀ X m n, (p' X m).hom ≫ (Limits.Pi.π (fun n ↦ (K'.obj X).obj (op n)) n)⟦m⟧' =
      Limits.Pi.π (fun n ↦ (K'.obj (X⟦m⟧)).obj (op n)) n ≫ (e' X m n).hom)
    (hlev : ∀ X m n, (O.mapHomologicalComplex (.up ℤ)).map (e X m n).hom ≫
        ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
        ((α.app X).app (op n))⟦m⟧' =
      (α.app (X⟦m⟧)).app (op n) ≫ (K'.map ((G.commShiftIso m).hom.app X)).app (op n) ≫
        (e' (G.obj X) m n).hom)
    (X : S) (m : ℤ) :
    (O.mapHomologicalComplex (.up ℤ)).map (p X m).hom ≫
        ((O.mapHomologicalComplex (.up ℤ)).commShiftIso m).hom.app _ ≫
        (piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj X).obj (op n)) ≫
          Limits.Pi.map (fun n ↦ (α.app X).app (op n)))⟦m⟧' =
      piComparison (O.mapHomologicalComplex (.up ℤ)) (fun n ↦ (K.obj (X⟦m⟧)).obj (op n)) ≫
        Limits.Pi.map (fun n ↦ (α.app (X⟦m⟧)).app (op n)) ≫
        Limits.Pi.map (fun n ↦ (K'.map ((G.commShiftIso m).hom.app X)).app (op n)) ≫
        (p' (G.obj X) m).hom := by
  apply (cancel_mono (PreservesProduct.iso (shiftFunctor (CochainComplex B ℤ) m)
    (fun n ↦ (K'.obj (G.obj X)).obj (op n))).hom).mp
  apply Limits.Pi.hom_ext
  intro n
  simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
  rw [hp']
  erw [Limits.Pi.map_π_assoc, Limits.Pi.map_π_assoc, piComparison_comp_π_assoc]
  rw [← Functor.map_comp, Category.assoc]
  erw [Limits.Pi.map_π, piComparison_comp_π_assoc]
  rw [Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc]
  erw [hp]
  rw [Functor.map_comp_assoc, hlev]

end ScalarRoosShift

end ChainShift

section LevelShift
open CategoryTheory.Limits Opposite
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The finite scalar pullback map is the generator-normalized module map in each degree. -/
private theorem scalarPullbackLevel_app_f {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) :
    ((scalarPullbackLevel l E L ι f n).app P).f i = pullbackScalarModule l E L ι f n (P.X i) := by
  let α : integralOperationsPullbackLevel l E f n ⋙
      (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n :=
    { app := fun P ↦
        { f := fun i ↦ pullbackScalarModule l E L ι f n (P.X i)
          comm' := fun i j _ ↦ (pullbackScalarModule_naturality l E L ι f n (P.d i j)).symm }
      naturality := fun P Q a ↦ HomologicalComplex.hom_ext _ _
        (fun i ↦ pullbackScalarModule_naturality l E L ι f n (a.f i)) }
  have hα : scalarPullbackLevel l E L ι f n = α :=
    (scalarPullbackLevel_existsUnique l E L ι f n).unique
      (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose_spec
      (fun P i V x ↦ pullbackScalarModule_unit l E L ι f n (P.X i) V x)
  rw [hα]

/-- The scalar pullback tower at a fixed level is the finite scalar pullback map. -/
theorem scalarPullbackTower_app_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    ((scalarPullbackTower l E L ι f).app P).app (op n) = (scalarPullbackLevel l E L ι f n).app P :=
  (scalarPullbackTower_existsUnique l E L ι f).exists.choose_spec P n

/-- The finite scalar pullback maps are compatible with degree reindexing. -/
theorem scalarPullbackLevel_app_shift_f {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (r k : ℤ) :
    ((scalarPullbackLevel l E L ι f n).app (P⟦r⟧)).f k =
      ((scalarPullbackLevel l E L ι f n).app P).f (k + r) := by
  rw [scalarPullbackLevel_app_f, scalarPullbackLevel_app_f]
  rfl

/-- The product of shift comparisons, composed with a shifted projection. -/
theorem piMapIso_shift_π {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] {C D : ℕ → CochainComplex A ℤ} (m : ℤ)
    (e : ∀ n, C n ≅ (D n)⟦m⟧) (n : ℕ) :
    (Limits.Pi.mapIso e ≪≫
        (PreservesProduct.iso (shiftFunctor (CochainComplex A ℤ) m) D).symm).hom ≫
        (Limits.Pi.π D n)⟦m⟧' = Limits.Pi.π C n ≫ (e n).hom := by
  rw [← piComparison_comp_π (shiftFunctor (CochainComplex A ℤ) m) D n]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← PreservesProduct.iso_hom, Iso.inv_hom_id_assoc]
  exact Limits.Pi.mapIso_hom_π e n

/-- The product shift comparison composed with a shifted projection is the level shift. -/
@[reassoc]
theorem productShift_hom_π {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (r : ℤ) (n : ℕ) :
    (IntegralCompletedComparison.productShift l E f P r).hom ≫
        (Limits.Pi.π (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj
          (op n)) n)⟦r⟧' =
      Limits.Pi.π (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj (P⟦r⟧)).obj
          (op n)) n ≫ (IntegralCompletedComparison.levelShift l E f P r n).hom := by
  unfold IntegralCompletedComparison.productShift
  exact piMapIso_shift_π r (fun n ↦ IntegralCompletedComparison.levelShift l E f P r n) n

/-- The finite scalar pullback maps commute with the termwise shift comparisons. -/
theorem scalarPullbackLevel_shift {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (r : ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (IntegralCompletedComparison.levelShift l E f P r n).hom ≫
      (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
        _ ≫ ((scalarPullbackLevel l E L ι f n).app P)⟦r⟧' =
    (scalarPullbackLevel l E L ι f n).app (P⟦r⟧) ≫
      (integralOperationsPullbackLevel l L f n).map
        ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
          r).hom.app P) ≫
      (IntegralCompletedComparison.levelShift l L f
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) r n).hom := by
  apply HomologicalComplex.hom_ext
  intro k
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, IntegralCompletedComparison.levelShift,
    Iso.app_hom]
  rw [scalarPullbackLevel_app_shift_f]
  erw [Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplexShiftIso_hom_app_f]
  have hD : ((integralOperationsPullbackLevel l L f n).map
      ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
        r).hom.app P)).f k = 𝟙 _ := by
    have hg : ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
        r).hom.app P).f k = 𝟙 _ := Functor.mapHomologicalComplex_commShiftIso_hom_app_f _ _ _ _
    have hm : ((integralOperationsPullbackLevel l L f n).map
        ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
          r).hom.app P)).f k =
        (SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (completedIntegralCommRingProjectionUnrestricted l L X n))).map
          ((integralOperationsLevelPullback l L f n).map
            ((unrestrictedIntegralReductionFunctor l L Y n).map
              (((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
                r).hom.app P).f k))) := rfl
    rw [hm, hg]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl
  erw [HomologicalComplex.comp_f, hD, CategoryTheory.Functor.map_id,
    Functor.mapCochainComplexShiftIso_hom_app_f, Category.id_comp, Category.id_comp]

end LevelShift

/-- The shift on the localization from good representatives. -/
@[instance_reducible]
private noncomputable def goodLocalizationCommShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [(integralOperationsGoodComplex l E X).IsStableUnderShift ℤ] :
    (integralOperationsGoodLocalization l E X).CommShift ℤ :=
  inferInstanceAs (((integralOperationsGoodComplex l E X).ι ⋙ DerivedCategory.Q).CommShift ℤ)

/-- The shift on the localized pullback construction on good representatives. -/
@[instance_reducible]
private noncomputable def pullbackOnGoodCommShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [(integralOperationsGoodComplex l E X).IsStableUnderShift ℤ]
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ) :
    (integralOperationsPullbackOnGood l E f).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ (integralOperationsGoodComplex l E X).ι
    (integralOperationsPullbackComplexFunctor l E f ⋙ DerivedCategory.Q) ℤ _ _ _ _
    inferInstance (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ c inferInstance)

set_option maxHeartbeats 1000000 in
-- Matching the good-subcategory and ambient derived category instances is slow.
/-- The defining integral pullback comparison commutes with the cochain and derived
pullback shifts related by representative descent. -/
private theorem integralDerivedPullbackComparison_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (d : (integralDerivedPullback l E f).CommShift ℤ)
    (hd : IntegralCompletedComparison.ShiftDescent l E f c d)
    [(integralOperationsGoodComplex l E X).IsStableUnderShift ℤ] :
    @NatTrans.CommShift _ _ _ _ _ _ (integralDerivedPullbackComparison l E f).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ (goodLocalizationCommShift l E X) d)
      (pullbackOnGoodCommShift l E f c) := by
  let := goodLocalizationCommShift l E X
  let := pullbackOnGoodCommShift l E f c
  constructor
  intro r
  ext P
  obtain ⟨hP, H⟩ := hd P r
  let g : P⟦r⟧ ⟶ (⟨P.obj⟦r⟧, hP⟩ : (integralOperationsGoodComplex l E X).FullSubcategory) :=
    ObjectProperty.homMk (((integralOperationsGoodComplex l E X).ι.commShiftIso r).hom.app P)
  have hn := (integralDerivedPullbackComparison l E f).hom.naturality g
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hG : ((integralOperationsGoodLocalization l E X).commShiftIso r).hom.app P =
      DerivedCategory.Q.map (((integralOperationsGoodComplex l E X).ι.commShiftIso r).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app P.obj :=
    Functor.commShiftIso_comp_hom_app (integralOperationsGoodComplex l E X).ι DerivedCategory.Q r P
  have hO : (@Functor.commShiftIso _ _ _ _ (integralOperationsPullbackOnGood l E f) ℤ _ _ _
      (pullbackOnGoodCommShift l E f c) r).hom.app P =
      DerivedCategory.Q.map ((integralOperationsPullbackComplexFunctor l E f).map
        (((integralOperationsGoodComplex l E X).ι.commShiftIso r).hom.app P)) ≫
      DerivedCategory.Q.map (((integralOperationsPullbackComplexFunctor l E f).commShiftIso
        r).hom.app P.obj) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) := by
    unfold pullbackOnGoodCommShift
    erw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
    simp only [Functor.comp_map]
    rfl
  rw [Functor.commShiftIso_comp_hom_app, hG, hO, Category.assoc]
  erw [H]
  erw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc (integralDerivedPullback l E f)
      ((DerivedCategory.Q.commShiftIso r).hom.app P.obj), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% hn]
  rfl

section ChainInstance
open CategoryTheory.Limits Opposite

/-- The Roos scalar/pullback chain comparison commutes with the signed Roos shifts. -/
private theorem scalarPullbackChainNat_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cE : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hcE : IntegralCompletedComparison.ShiftCoordinates l E f cE)
    (cL : (integralOperationsPullbackComplexFunctor l L f).CommShift ℤ)
    (hcL : IntegralCompletedComparison.ShiftCoordinates l L f cL) :
    @NatTrans.CommShift _ _ _ _ _ _ (scalarRoosChain (integralOperationsPullbackTowerFunctor l E f)
      (integralOperationsPullbackTowerFunctor l L f)
      ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ))
      (integralOrdinaryScalar l E L ι Y) (scalarPullbackTower l E L ι f)) ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ cE _)
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ cL) :=
  scalarRoosChain_commShift (eC := cE) (eC' := cL)
    (p := fun P r ↦ IntegralCompletedComparison.productShift l E f P r)
    (p' := fun P r ↦ IntegralCompletedComparison.productShift l L f P r)
    (hl := fun P r j ↦ (hcE P r).1 j) (hr := fun P r i j h ↦ (hcE P r).2 i j h)
    (hl' := fun P r j ↦ (hcL P r).1 j) (hr' := fun P r i j h ↦ (hcL P r).2 i j h)
    (hprod := scalarRoos_productSquare
      (e := fun P r n ↦ IntegralCompletedComparison.levelShift l E f P r n)
      (e' := fun P r n ↦ IntegralCompletedComparison.levelShift l L f P r n)
      (hp := fun P r n ↦ productShift_hom_π l E f P r n)
      (hp' := fun P r n ↦ productShift_hom_π l L f P r n)
      (hlev := fun P r n ↦ by
        rw [scalarPullbackTower_app_app, scalarPullbackTower_app_app]
        exact scalarPullbackLevel_shift l E L ι f n P r))

end ChainInstance

/-- The ordinary scalar/pullback comparison commutes with the descended integral pullback
shifts and the ordinary derived scalar shifts.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
theorem scalarPullbackOrdinary_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cE : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (dE : (integralDerivedPullback l E f).CommShift ℤ)
    (hcE : IntegralCompletedComparison.ShiftCoordinates l E f cE)
    (hdE : IntegralCompletedComparison.ShiftDescent l E f cE dE)
    (cL : (integralOperationsPullbackComplexFunctor l L f).CommShift ℤ)
    (dL : (integralDerivedPullback l L f).CommShift ℤ)
    (hcL : IntegralCompletedComparison.ShiftCoordinates l L f cL)
    (hdL : IntegralCompletedComparison.ShiftDescent l L f cL dL) :
    @NatTrans.CommShift _ _ _ _ _ _ (scalarPullbackOrdinary l E L ι f).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ dE _)
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ dL) := by
  let := dE
  let := dL
  let := cE
  let := cL
  have : (integralOperationsGoodComplex l E X).IsStableUnderShift ℤ :=
    ⟨fun r ↦ ⟨fun P hP ↦ (hdE ⟨P, hP⟩ r).1⟩⟩
  have : (integralOperationsGoodComplex l L X).IsStableUnderShift ℤ :=
    ⟨fun r ↦ ⟨fun P hP ↦ (hdL ⟨P, hP⟩ r).1⟩⟩
  let ιE := (integralOperationsGoodComplex l E X).ι
  let ιL := (integralOperationsGoodComplex l L X).ι
  let Q := (DerivedCategory.Q : CochainComplex (integralTowerModules l E X) ℤ ⥤ _)
  let FE := integralDerivedPullback l E f
  let FL := integralDerivedPullback l L f
  let TE := integralOperationsPullbackComplexFunctor l E f
  let TL := integralOperationsPullbackComplexFunctor l L f
  let OcX := (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
  let OcY := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)
  let ODX := integralOrdinaryDerivedScalar l E L ι X
  let ODY := integralOrdinaryDerivedScalar l E L ι Y
  let Og : (integralOperationsGoodComplex l E X).FullSubcategory ⥤
      (integralOperationsGoodComplex l L X).FullSubcategory :=
    (integralOperationsGoodComplex l L X).lift (ιE ⋙ OcX) (fun P ↦ scalarGood l E L ι X P)
  let eE : (ιE ⋙ DerivedCategory.Q) ⋙ FE ≅ ιE ⋙ TE ⋙ DerivedCategory.Q :=
    integralDerivedPullbackComparison l E f
  let eL : (ιL ⋙ DerivedCategory.Q) ⋙ FL ≅ ιL ⋙ TL ⋙ DerivedCategory.Q :=
    integralDerivedPullbackComparison l L f
  have : NatTrans.CommShift eE.hom ℤ :=
    integralDerivedPullbackComparison_commShift l E f cE dE hdE
  have : NatTrans.CommShift eL.hom ℤ :=
    integralDerivedPullbackComparison_commShift l L f cL dL hdL
  let ch : TE ⋙ OcY ⟶ OcX ⋙ TL :=
    scalarRoosChain (integralOperationsPullbackTowerFunctor l E f)
      (integralOperationsPullbackTowerFunctor l L f) OcX (integralOrdinaryScalar l E L ι Y)
      (scalarPullbackTower l E L ι f)
  have : NatTrans.CommShift ch ℤ := scalarPullbackChainNat_commShift l E L ι f cE hcE cL hcL
  let φY : DerivedCategory.Q ⋙ ODY ≅ OcY ⋙ DerivedCategory.Q :=
    (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors
  let φX : DerivedCategory.Q ⋙ ODX ≅ OcX ⋙ DerivedCategory.Q :=
    (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors
  let lamE : Og ⋙ ιL ≅ ιE ⋙ OcX := ObjectProperty.liftCompιIso _ _ _
  let θ : Og ⋙ (ιL ⋙ DerivedCategory.Q) ⟶ (ιE ⋙ DerivedCategory.Q) ⋙ ODX :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight lamE.hom DerivedCategory.Q ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ιE φX.inv ≫
      (Functor.associator _ _ _).inv
  let ψ : (ιE ⋙ DerivedCategory.Q) ⋙ (FE ⋙ ODY) ⟶ (ιE ⋙ DerivedCategory.Q) ⋙ (ODX ⋙ FL) :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eE.hom ODY ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ιE (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ιE (Functor.whiskerLeft TE φY.hom) ≫
      Functor.whiskerLeft ιE (Functor.associator _ _ _).inv ≫
      Functor.whiskerLeft ιE (Functor.whiskerRight ch DerivedCategory.Q) ≫
      Functor.whiskerLeft ιE (Functor.associator _ _ _).hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight lamE.inv (TL ⋙ DerivedCategory.Q) ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Og eL.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight θ FL ≫ (Functor.associator _ _ _).hom
  have hθ : NatTrans.CommShift θ ℤ := by
    dsimp only [θ]
    infer_instance
  have hψ : NatTrans.CommShift ψ ℤ := by
    dsimp only [ψ]
    infer_instance
  have hN := (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose_spec
  have key : Functor.whiskerLeft (ιE ⋙ DerivedCategory.Q) (scalarPullbackOrdinary l E L ι f).hom =
      ψ := by
    ext P
    have hP := hN P
    have hl1 : lamE.hom.app P = 𝟙 _ := rfl
    have hl2 : lamE.inv.app P = 𝟙 _ := rfl
    simp only [ψ, θ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, hl1, hl2]
    have hP' : ODY.map (eE.hom.app P) ≫ φY.hom.app (TE.obj (ιE.obj P)) ≫
        DerivedCategory.Q.map (ch.app (ιE.obj P)) ≫ eL.inv.app (Og.obj P) ≫
        FL.map (φX.inv.app (ιE.obj P)) =
        (scalarPullbackOrdinary l E L ι f).hom.app ((ιE ⋙ DerivedCategory.Q).obj P) := by
      have hP2 := (reassoc_of% hP) (eL.inv.app (Og.obj P) ≫ FL.map (φX.inv.app (ιE.obj P)))
      erw [Category.assoc] at hP2
      erw [hP2, Category.assoc, Category.assoc, eL.hom_inv_id_app_assoc (Og.obj P),
        ← FL.map_comp, φX.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
      rfl
    rw [← hP']
    simp only [CategoryTheory.Functor.map_id]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.id_comp, Category.id_comp]
  have hes (K : DerivedCategory (integralTowerModules l E X)) :
      ∃ P, Nonempty ((ιE ⋙ DerivedCategory.Q).obj P ≅ K) := by
    have := integralOperationsGoodLocalization_isLocalization l E X
    exact (Localization.essSurj (integralOperationsGoodLocalization l E X)
      ((HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
        (integralOperationsGoodComplex l E X).ι)).mem_essImage K
  apply natTrans_commShift_of_whiskerLeft_essSurj (ιE ⋙ DerivedCategory.Q) _ hes
  rw [key]
  exact hψ

attribute [local semireducible] constructibleIntegralPullback

/-- The ambient component of the integral pullback scalar comparison. -/
theorem integralPullbackScalarComparison_hom_hom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X) :
    (integralPullbackScalarComparison l E L ι f K).hom.hom =
      (scalarCompletionIso l E L ι Y ((integralDerivedPullback l E f).obj K.obj)
        ((constructibleIntegralPullback l E f).obj K).property.1).inv ≫
        (scalarPullbackOrdinary l E L ι f).hom.app K.obj ≫
        (integralDerivedPullback l L f).map ((scalarCompletion l E L ι X).app K.obj) :=
  rfl

/-- The integral pullback scalar comparison is the ordinary comparison conjugated by the
ordinary-to-completed scalar comparisons. -/
theorem integralPullbackScalarComparison_hom_hom_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X) :
    (sfIntegralOrdinaryScalarComparison l E L ι Y).inv.app
        ((constructibleIntegralPullback l E f).obj K) ≫
      (scalarPullbackOrdinary l E L ι f).hom.app ((sfIntegralConstructible l E X).ι.obj K) ≫
      (integralDerivedPullback l L f).map
        ((sfIntegralOrdinaryScalarComparison l E L ι X).hom.app K) =
    (integralPullbackScalarComparison l E L ι f K).hom.hom := by
  have hY := sfIntegralOrdinaryScalarComparison_hom_app l E L ι Y
    ((constructibleIntegralPullback l E f).obj K)
  have hYi : (sfIntegralOrdinaryScalarComparison l E L ι Y).inv.app
      ((constructibleIntegralPullback l E f).obj K) =
      (scalarCompletionIso l E L ι Y ((integralDerivedPullback l E f).obj K.obj)
        ((constructibleIntegralPullback l E f).obj K).property.1).inv := by
    rw [← Iso.app_inv]
    apply Iso.inv_ext
    rw [Iso.app_hom, hY]
    exact (scalarCompletionIso l E L ι Y ((integralDerivedPullback l E f).obj K.obj)
      ((constructibleIntegralPullback l E f).obj K).property.1).hom_inv_id
  rw [sfIntegralOrdinaryScalarComparison_hom_app, hYi, integralPullbackScalarComparison_hom_hom]
  rfl

/-- The constructible integral pullback is the restriction of the ambient integral
derived pullback. -/
noncomputable def constructibleIntegralPullbackCompι (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E f :=
  ObjectProperty.liftCompιIso _ _ _

/-- The restriction comparison has identity components. -/
theorem constructibleIntegralPullbackCompι_hom_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (K : sfIntegralConstructibleCategory l E X) :
    (constructibleIntegralPullbackCompι l E f).hom.app K = 𝟙 _ :=
  rfl

/-- The restriction comparison has identity inverse components. -/
theorem constructibleIntegralPullbackCompι_inv_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (K : sfIntegralConstructibleCategory l E X) :
    (constructibleIntegralPullbackCompι l E f).inv.app K = 𝟙 _ :=
  rfl

/-- The restriction comparison commutes with shifts whose components are the ambient ones. -/
theorem constructibleIntegralPullbackCompι_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [(constructibleIntegralPullback l E f).CommShift ℤ]
    [(integralDerivedPullback l E f).CommShift ℤ]
    (hs : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℤ),
        HEq (((constructibleIntegralPullback l E f).commShiftIso n).hom.app K).hom
          (((integralDerivedPullback l E f).commShiftIso n).hom.app K.obj)) :
    NatTrans.CommShift (constructibleIntegralPullbackCompι l E f).hom ℤ :=
  liftCompιIso_commShift_of_heq _ _ _ (fun K n ↦ (hs K n).trans (by
    rw [Functor.commShiftIso_comp_hom_app]
    exact (map_comp_heq_of_heq_id _ _ _ (fullSubcategory_shift_obj_eq _ n K)
      (fullSubcategory_ι_commShiftIso_hom_app_heq _ n K)).symm))

/-- The ambient form of the integral pullback scalar comparison: the ordinary
scalar/pullback comparison conjugated by the ordinary-to-completed comparisons. -/
noncomputable def integralPullbackScalarAmbientIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (constructibleIntegralPullback l E f ⋙ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y) ⋙ (sfIntegralConstructible l L Y).ι ≅
      (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι X ⋙ constructibleIntegralPullback l L f) ⋙ (sfIntegralConstructible l L Y).ι :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntegralOrdinaryScalarComparison l E L ι Y).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constructibleIntegralPullbackCompι l E f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarPullbackOrdinary l E L ι f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntegralOrdinaryScalarComparison l E L ι X) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (constructibleIntegralPullbackCompι l L f).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The components of the ambient comparison are those of the integral pullback scalar
comparison. -/
theorem integralPullbackScalarAmbientIso_hom_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X) :
    (integralPullbackScalarAmbientIso l E L ι f).hom.app K =
      (integralPullbackScalarComparison l E L ι f K).hom.hom := by
  simp only [integralPullbackScalarAmbientIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  have h1 : (integralOrdinaryDerivedScalar l E L ι Y).map
      ((constructibleIntegralPullbackCompι l E f).hom.app K) = 𝟙 _ :=
    (integralOrdinaryDerivedScalar l E L ι Y).map_id _
  rw [h1, constructibleIntegralPullbackCompι_inv_app]
  erw [Category.id_comp, Category.comp_id]
  exact integralPullbackScalarComparison_hom_hom_eq l E L ι f K

/-- The ambient comparison commutes with shifts once the ordinary scalar/pullback
comparison does. -/
theorem integralPullbackScalarAmbientIso_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [(integralDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(integralDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    (hsE : ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso n).hom.app K.obj))
    (hsL : ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso n).hom.app K.obj))
    (hS : NatTrans.CommShift (scalarPullbackOrdinary l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom ℤ) :
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
    NatTrans.CommShift (integralPullbackScalarAmbientIso l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom ℤ := by
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
  have : NatTrans.CommShift (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X).hom ℤ :=
    sfIntegralOrdinaryScalarComparison_commShift l Ω X E L h
  have : NatTrans.CommShift (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).hom ℤ :=
    sfIntegralOrdinaryScalarComparison_commShift l Ω Y E L h
  have : NatTrans.CommShift
      (constructibleIntegralPullbackCompι l (Coefficient.{u} l Ω E) f).hom ℤ :=
    constructibleIntegralPullbackCompι_commShift l _ f hsE
  have : NatTrans.CommShift
      (constructibleIntegralPullbackCompι l (Coefficient.{u} l Ω L) f).hom ℤ :=
    constructibleIntegralPullbackCompι_commShift l _ f hsL
  simp only [integralPullbackScalarAmbientIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The coefficient transition of the integral pullback scalar comparison commutes with the
supplied integral pullback shifts and the normalized integral transition shifts.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
theorem integralPullbackScalarComparison_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    (hE : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω E) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω E) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω E) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (self := d) n).hom.app K.obj))
    (hL : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω L) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω L) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω L) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (self := d) n).hom.app K.obj)) :
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
    ∃ α : constructibleIntegralPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) f,
      (∀ K, α.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f K) ∧
      NatTrans.CommShift α.hom ℤ := by
  obtain ⟨cE, dE, hcE, hdE, hsE⟩ := hE
  obtain ⟨cL, dL, hcL, hdL, hsL⟩ := hL
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
  let := dE
  let := dL
  have hδ := integralPullbackScalarAmbientIso_commShift l Ω f E L h hsE hsL
    (scalarPullbackOrdinary_commShift l _ _ _ f cE dE hcE hdE cL dL hcL hdL)
  let hI := (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).fullyFaithfulι.whiskeringRight
    (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
  let α : constructibleIntegralPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) f :=
    hI.preimageIso (integralPullbackScalarAmbientIso l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f)
  have hwα : Functor.whiskerRight α.hom (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι =
      (integralPullbackScalarAmbientIso l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom :=
    hI.map_preimage _
  refine ⟨α, fun K ↦ ?_, ?_⟩
  · apply Iso.ext
    apply ObjectProperty.hom_ext
    exact (NatTrans.congr_app hwα K).trans
      (integralPullbackScalarAmbientIso_hom_app l _ _ _ f K)
  · have : NatTrans.CommShift (Functor.whiskerRight α.hom
        (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι) ℤ := by
      rw [hwα]
      exact hδ
    exact NatTrans.CommShift.of_whiskerRight α.hom
      (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι

attribute [local irreducible] constructibleIntegralPullback

attribute [local irreducible] rationalPullbackScalarComparison


/-- The rational pullback scalar comparison commutes with the normalized rational shifts,
given the shift compatibility of its integral model.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph
(blueprint: lem-sf-rational-pullback-transition-shift). -/
theorem rationalPullbackScalarComparison_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [(rationalDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(rationalDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [iX : (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h).CommShift ℤ]
    [iY : (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).CommShift ℤ]
    [tX : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ]
    [tY : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ]
    (ntX : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X,
      HEq (((sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h)).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
          (((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (ntY : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y,
      HEq (((sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h)).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
          (((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nE : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nL : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (α : constructibleIntegralPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) f)
    (hα : ∀ K, α.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f K)
    (hs : NatTrans.CommShift α.hom ℤ) :
    @NatTrans.CommShift _ _ _ _ _ _ (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ tY)
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ tX _) := by
  let A := constructibleIntegralPullback l (Coefficient.{u} l Ω E) f
  let B := constructibleIntegralPullback l (Coefficient.{u} l Ω L) f
  let Ar := rationalDerivedPullback l (Coefficient.{u} l Ω E) f
  let Br := rationalDerivedPullback l (Coefficient.{u} l Ω L) f
  let S (W : Scheme.{u}) := GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E L h
  let T (W : Scheme.{u}) := sfRationalScalarExtension l (Coefficient.{u} l Ω E) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h)
  let Q (W : Scheme.{u}) := sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) W
  let QL (W : Scheme.{u}) := sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) W
  have oA (J : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) :
      Ar.obj ((Q X).obj J) = (Q Y).obj (A.obj J) := by
    simpa only [Ar, A, Q, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l (Coefficient.{u} l Ω E) f).exists.choose_spec.2.1
        ((Q X).obj J)
  have oB (J : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X) :
      Br.obj ((QL X).obj J) = (QL Y).obj (B.obj J) := by
    simpa only [Br, B, QL, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l (Coefficient.{u} l Ω L) f).exists.choose_spec.2.1
        ((QL X).obj J)
  have oT (W : Scheme.{u}) (J : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W) :
      (T W).obj ((Q W).obj J) = (QL W).obj ((S W).obj J) := by
    simpa only [T, S, QL, Q, GeneralAlgebraicallyClosedCoefficients.integralTransition,
      sfRationalScalarExtension, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (sfRationalScalarExtension_existsUnique l (Coefficient.{u} l Ω E) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).exists.choose_spec.2.1 ((Q W).obj J)
  have mA {J J' : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X}
      (a : J ⟶ J') : HEq (Ar.map ((Q X).map a)) ((Q Y).map (A.map a)) := by
    simp only [Ar, A, Q, sfRationalConstructibleLocalization, ScalarLocalization.localization]
    delta rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l
      (Coefficient.{u} l Ω E) f).exists.choose_spec.2.2 J J' a 1
  have mB {J J' : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X}
      (a : J ⟶ J') : HEq (Br.map ((QL X).map a)) ((QL Y).map (B.map a)) := by
    simp only [Br, B, QL, sfRationalConstructibleLocalization, ScalarLocalization.localization]
    delta rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l
      (Coefficient.{u} l Ω L) f).exists.choose_spec.2.2 J J' a 1
  have mT (W : Scheme.{u}) {J J' : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W}
      (a : J ⟶ J') : HEq ((T W).map ((Q W).map a)) ((QL W).map ((S W).map a)) := by
    have hh := sfRationalScalarExtension_map_tmul l (Coefficient.{u} l Ω E) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) J J' a 1
    simp only [T, Q, QL, S, GeneralAlgebraicallyClosedCoefficients.integralTransition,
      sfRationalConstructibleLocalization, ScalarLocalization.localization, map_one] at hh ⊢
    convert hh using 1
    rfl
  let eA := localizedEqToIso (Q X) (Q Y) A Ar oA mA
  let eB := localizedEqToIso (QL X) (QL Y) B Br oB mB
  let eTX := localizedEqToIso (Q X) (QL X) (S X) (T X) (oT X) (mT X)
  let eTY := localizedEqToIso (Q Y) (QL Y) (S Y) (T Y) (oT Y) (mT Y)
  have : NatTrans.CommShift eA.hom ℤ :=
    rationalLocalizedEqToIso_commShift l _ _ X Y A Ar oA mA (fun J ↦ nE ((Q X).obj J))
  have : NatTrans.CommShift eB.hom ℤ :=
    rationalLocalizedEqToIso_commShift l _ _ X Y B Br oB mB (fun J ↦ nL ((QL X).obj J))
  have : NatTrans.CommShift eTX.hom ℤ :=
    rationalLocalizedEqToIso_commShift l _ _ X X (S X) (T X) (oT X) (mT X)
      (fun J ↦ ntX ((Q X).obj J))
  have : NatTrans.CommShift eTY.hom ℤ :=
    rationalLocalizedEqToIso_commShift l _ _ Y Y (S Y) (T Y) (oT Y) (mT Y)
      (fun J ↦ ntY ((Q Y).obj J))
  let β := rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f
  have hw : Functor.whiskerLeft (Q X) β.hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eA.hom (T Y) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft A eTY.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.hom (QL Y) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (S X) eB.inv ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eTX.inv Br ≫
        (Functor.associator _ _ _).hom := by
    ext K
    have hb : HEq (β.hom.app ((Q X).obj K)) ((QL Y).map (integralPullbackScalarComparison l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)
        f K).hom) := by
      dsimp only [β]
      delta rationalPullbackScalarComparison
      exact (rationalPullbackScalarComparison_existsUnique l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).exists.choose_spec
        ((Q X).obj K)
    have ha : α.hom.app K = (integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f K).hom :=
      congrArg Iso.hom (hα K)
    have heA : eA.hom.app K = eqToHom (oA K) := rfl
    have heB : eB.inv.app ((S X).obj K) = eqToHom (oB ((S X).obj K)).symm := rfl
    have heTX : eTX.inv.app K = eqToHom (oT X K).symm := rfl
    have heTY : eTY.hom.app (A.obj K) = eqToHom (oT Y (A.obj K)) := rfl
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    simp only [heA, heB, heTX, heTY]
    rw [Category.id_comp]
    exact eq_of_heq (hb.trans ((heq_of_eq (congrArg (QL Y).map ha.symm)).trans
      (map_eqToHom_conj_heq _ _ _ _ _ _ _).symm))
  apply natTrans_commShift_of_whiskerLeft (Q X) β.hom
    (sfRationalConstructibleLocalization_obj_surjective l _ X)
  rw [hw]
  infer_instance

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift

/-- The actual coefficient-transition comparison preserves normalized pullback shifts.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph;
step 7 of lem-sf-automorphism-constructible-stage-equivalence and
lem-sf-framework-theta-shift-compatibility.
(blueprint: lem-sf-rational-pullback-transition-shift).

Proof: take the two cochain and derived shift witnesses in hE and hL. The
coordinates are the signed Roos coordinates, and the descent comparisons fix their
values on every good representative. For the coefficient transition take the
canonical completed scalar shifts, whose ordinary-to-completed comparison has the
normalization defining integralTransitionCommShift. The framework theta theorem
applies to these four shifts, using any finite-field datum of characteristic different
from l (no scheme structure map to that field is required). Identify theta with the prescribed
integral pullback
scalar comparison using its completion normalization. The full constructible
inclusion is faithful, so its ambient shift square is the integral scalar square.
Apply rational localization to that square. The supplied degree-one formulas rE
and rL and the canonical scalar-transition formula identify its sides with the
rational square at one. The CommShift zero and addition laws extend the square
to every positive integer; applying the inverse shift gives negative integers.
Finally commonStagePullbackTransition conjugates this comparison by the recorded
stage-transition isomorphisms, which preserve the transported shifts. Whiskering
and composing their squares proves the conclusion. The argument uses the entire
natural transformations, so it also covers zero objects, empty schemes, repeated
fields, and arbitrary scheme morphisms without an isomorphism hypothesis. -/
theorem rationalPullbackTransitionShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [rE : (rationalDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [rL : (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    (hE : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω E) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω E) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω E) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (self := d) n).hom.app K.obj))
    (hL : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω L) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω L) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω L) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (self := d) n).hom.app K.obj))
    (nE : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nL : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (1 : ℤ)).hom.app K.obj))) :
    letI := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
    letI := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
    @NatTrans.CommShift _ _ _ _ _ _ (commonStagePullbackTransition l Ω f h).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h)
        ℤ _ _ _ _ rE
        (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h))
      (@Functor.CommShift.comp _ _ _ _ _ _
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h)
        (rationalDerivedPullback l (Coefficient.{u} l Ω L) f)
        ℤ _ _ _ _
        (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h)
        rL) := by

  obtain ⟨α, hα, hs⟩ := integralPullbackScalarComparison_commShift l Ω f E L h hE hL
  let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
  let := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h
  let β : rationalDerivedPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h ⟶
      GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h ⋙
        rationalDerivedPullback l (Coefficient.{u} l Ω L) f :=
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom
  have hβ : NatTrans.CommShift β ℤ :=
    rationalPullbackScalarComparison_commShift
      (iX := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h)
      (iY := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h)
      (tX := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
      (tY := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
      l Ω f E L h
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
        l Ω X E L h).exists.choose_spec
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
        l Ω Y E L h).exists.choose_spec
      nE nL α hα hs
  have htX : NatTrans.CommShift (operationStageTransitionIso l Ω X E L h).hom ℤ :=
    eqToIso_commShift ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω X).exists.choose_spec.1 E L h)
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
  have htY : NatTrans.CommShift (operationStageTransitionIso l Ω Y E L h).hom ℤ :=
    eqToIso_commShift ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω Y).exists.choose_spec.1 E L h)
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
  have key : NatTrans.CommShift
      (Functor.whiskerLeft (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
          (operationStageTransitionIso l Ω Y E L h).hom ≫ β ≫
        Functor.whiskerRight (operationStageTransitionIso l Ω X E L h).inv
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f)) ℤ := inferInstance
  exact key

end WeilConjectures
