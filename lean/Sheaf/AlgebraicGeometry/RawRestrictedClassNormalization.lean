module

public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import Sheaf.AlgebraicGeometry.RawRestrictedResolutionNaturality
import Sheaf.AlgebraicGeometry.RawRestrictedResolutionRestriction
import Sheaf.AlgebraicGeometry.RawRestrictedResolutionClass

/-! # Normalization of raw and restricted cohomology classes

Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance


private theorem normalizationLift_eq {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    normalizationLift f q F = (canonicalComparison f q F).hom := by
  apply ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ _).injective
  rw [normalizationLift, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  ext V z
  exact (canonicalComparison_class f q F V.unop z).symm

private theorem normalizationLift_isIso {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (normalizationLift f q F) := by
  rw [normalizationLift_eq]
  infer_instance

private theorem normalizationKappa_apply {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : S.Etale) (z : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :
    (normalizationKappa f q F).app (op V) z =
      abelianHigherDirectImageClass f q F V z := rfl

private theorem adjunct_shift_naturality
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) [R.CommShift ℤ]
    (n : ℤ) {A : C} {K K' : D} (x : L.obj A ⟶ K⟦n⟧) (g : K ⟶ K') :
    adj.homEquiv _ _ x ≫ (R.commShiftIso n).hom.app K ≫
        (shiftFunctor C n).map (R.map g) =
      adj.homEquiv _ _ (x ≫ (shiftFunctor D n).map g) ≫
        (R.commShiftIso n).hom.app K' := by
  rw [← R.commShiftIso_hom_naturality g n]
  rw [← Category.assoc, ← adj.homEquiv_naturality_right]

private theorem adjunct_homology_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) [R.CommShift ℤ]
    (H₀ Hn : C ⥤ E) (n : ℤ) (σ : shiftFunctor C n ⋙ H₀ ≅ Hn)
    {A : C} {B : E} (s : B ⟶ H₀.obj A) {K K' : D}
    (x : L.obj A ⟶ K⟦n⟧) (g : K ⟶ K') :
    (s ≫ H₀.map (adj.homEquiv _ _ x) ≫
        (H₀.mapIso ((R.commShiftIso n).app K) ≪≫ σ.app (R.obj K)).hom) ≫
          Hn.map (R.map g) =
      s ≫ H₀.map (adj.homEquiv _ _ (x ≫ (shiftFunctor D n).map g)) ≫
        (H₀.mapIso ((R.commShiftIso n).app K') ≪≫ σ.app (R.obj K')).hom := by
  exact map_shifted_triangle_iso H₀ Hn n σ s
    (adj.homEquiv _ _ x) ((R.commShiftIso n).app K)
    (adj.homEquiv _ _ (x ≫ (shiftFunctor D n).map g))
    ((R.commShiftIso n).app K') _ _ rfl rfl (R.map g)
    (adjunct_shift_naturality L R adj n x g)

private theorem normalizationKappa_coefficient {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    normalizationRawCoefficient f q φ ≫ normalizationKappa f q G =
      normalizationKappa f q F ≫ (normalizationHigherCoefficient f q φ).hom := by
  ext V z
  simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply]
  let adj := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus
  let R := R+((f)_*[AddCommGrpCat.{u + 1}])
  let A := (abelianComparisonFree S).obj V.unop
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let K' := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let g := (DerivedCategory.Plus.singleFunctor _ 0).map φ
  let x := (((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ z
  let x' := (((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
    z ≫ (shiftFunctor _ (q : ℤ)).map g
  let H₀ := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let Hq := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  have hm :
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
        H₀.map (adj.homEquiv _ _ x) ≫ (abelianComparisonShift f q F).hom) ≫ Hq.map (R.map g) =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
        H₀.map (adj.homEquiv _ _ x') ≫ (abelianComparisonShift f q G).hom := by
    simpa only [abelianComparisonShift, x, x', K, K', g, Category.assoc] using
      adjunct_homology_naturality _ _ adj H₀ Hq (q : ℤ)
        (H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _))
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A) x g
  exact (eval_sheaf_composition _ _ _ hm V
    (((toSheafify S.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj V.unop ⋙ AddCommGrpCat.free)).app V).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 V.unop))))).symm


private theorem normalizationLift_coefficient {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (normalizationRawCoefficient f q φ) ≫ normalizationLift f q G =
      normalizationLift f q F ≫ normalizationHigherCoefficient f q φ := by
  apply ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [normalizationLift, Equiv.apply_symm_apply]
  exact normalizationKappa_coefficient f q φ

private theorem compatible_comparisons
    {C : Type*} [Category C] {A A' B B' H H' : C}
    (c : A ⟶ B) [Epi c] (c' : A' ⟶ B') (i : B ⟶ H) (i' : B' ⟶ H')
    (a : A ⟶ A') (b : B ⟶ B') (h : H ⟶ H') (k : A ⟶ H) (k' : A' ⟶ H')
    (hr : a ≫ c' = c ≫ b) (hc : c ≫ i = k) (hc' : c' ≫ i' = k')
    (hk : a ≫ k' = k ≫ h) : b ≫ i' = i ≫ h := by
  apply (cancel_epi c).mp
  rw [← Category.assoc, ← hr, Category.assoc, hc', hk, ← hc, Category.assoc]

private theorem normalizationIota_coefficient_of_class
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (hF : ∀ V : S.Etale,
      rawRestrictedCohomologyComparison f q F V ≫ normalizationIota f q F V =
        (normalizationKappa f q F).app (op V))
    (hG : ∀ V : S.Etale,
      rawRestrictedCohomologyComparison f q G V ≫ normalizationIota f q G V =
        (normalizationKappa f q G).app (op V))
    (hc : ∀ V : S.Etale,
      (normalizationRawCoefficient f q φ).app (op V) ≫
          rawRestrictedCohomologyComparison f q G V =
        rawRestrictedCohomologyComparison f q F V ≫
          normalizationRestrictedCoefficient f q φ V)
    (V : S.Etale) :
    normalizationRestrictedCoefficient f q φ V ≫ normalizationIota f q G V =
      normalizationIota f q F V ≫ (normalizationHigherCoefficient f q φ).hom.app (op V) := by
  have : IsIso (rawRestrictedCohomologyComparison f q F V) :=
    isIso_rawRestrictedCohomologyComparison f q F V
  apply compatible_comparisons
    (rawRestrictedCohomologyComparison f q F V)
    (rawRestrictedCohomologyComparison f q G V)
    (normalizationIota f q F V) (normalizationIota f q G V)
    ((normalizationRawCoefficient f q φ).app (op V))
    (normalizationRestrictedCoefficient f q φ V)
    ((normalizationHigherCoefficient f q φ).hom.app (op V))
    ((normalizationKappa f q F).app (op V))
    ((normalizationKappa f q G).app (op V)) (hc V) (hF V) (hG V)
    (NatTrans.congr_app (normalizationKappa_coefficient f q φ) (op V))


private theorem evaluation_shiftIso_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R₀ : D ⥤ AddCommGrpCat.{u + 1}) [R₀.Additive] [PreservesFiniteLimits R₀]
    (q : ℕ) {F G : C} (φ : F ⟶ G) :
    (RawRestrictedComparison.Evaluation.functor L R₀ ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        ((shiftFunctor _ (q : ℤ)).map ((DerivedCategory.Plus.singleFunctor C 0).map φ)) ≫
      (RawRestrictedComparison.Evaluation.shiftIso L R₀ q G).hom =
    (RawRestrictedComparison.Evaluation.shiftIso L R₀ q F).hom ≫
      (R₀.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map (L.map φ))) := by
  let R := R₀.rightDerivedFunctor
  let S₀ := DerivedCategory.Plus.singleFunctor
    C 0
  let D := RawRestrictedComparison.Evaluation.functor L R₀
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let Hq := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  let τ : shiftFunctor _ (q : ℤ) ⋙ D ⋙ H₀ ≅ D ⋙ Hq :=
    Functor.isoWhiskerRight (D.commShiftIso (q : ℤ)) H₀ ≪≫
      Functor.isoWhiskerLeft D (H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _))
  let δ : S₀ ⋙ D ≅ L ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R :=
    (Functor.associator S₀ DerivedCategory.Plus.ι (L.mapDerivedCategory ⋙ R)).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0)
        (L.mapDerivedCategory ⋙ R) ≪≫
      (Functor.associator (DerivedCategory.singleFunctor _ 0) L.mapDerivedCategory R).symm ≪≫
      Functor.isoWhiskerRight (L.mapDerivedCategorySingleFunctor 0) R ≪≫
      Functor.associator L (DerivedCategory.singleFunctor _ 0) R
  let e := Functor.isoWhiskerLeft S₀ τ ≪≫ Functor.isoWhiskerRight δ Hq ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight
      (DerivedCategory.singleFunctorIsoCompQ _ 0) (R ⋙ Hq))
  have he (A : C) :
      e.hom.app A = (RawRestrictedComparison.Evaluation.shiftIso L R₀ q A).hom := by
    dsimp only [e, τ, δ, Functor.isoWhiskerLeft, Functor.isoWhiskerRight,
      Functor.mapIso, Functor.whiskeringLeft, Functor.whiskeringRight,
      Functor.whiskerLeft, Functor.whiskerRight, Iso.trans, Iso.symm,
      Functor.associator]
    simp only [RawRestrictedComparison.Evaluation.shiftIso,
      RawRestrictedComparison.Evaluation.singleIso, NatTrans.comp_app,
      Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Functor.comp_map,
      Category.id_comp, Category.comp_id, Category.assoc]
    erw [Hq.map_id, Category.id_comp]
  have hn := e.hom.naturality (X := F) (Y := G) φ
  rw [he, he] at hn
  exact hn

private theorem evaluate_naturality
    {E : Type*} [Category.{u + 1} E] [Preadditive E]
    (T : E ⥤ AddCommGrpCat.{u + 1}) [T.Additive]
    {A B C : E} (x : T.obj A) (g : B ⟶ C) :
    (preadditiveYoneda.map g).app (op A) ≫
        RawRestrictedComparison.Evaluation.evaluate T x =
      RawRestrictedComparison.Evaluation.evaluate T x ≫ T.map g := by
  ext z
  change T.map (z ≫ g) x = T.map g (T.map z x)
  rw [T.map_comp]
  rfl

private theorem evaluation_coefficient
    {C D : Type*} [Category.{u + 1} C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R₀ : D ⥤ AddCommGrpCat.{u + 1}) [R₀.Additive] [PreservesFiniteLimits R₀]
    (q : ℕ) {F G : C} (φ : F ⟶ G) (A : DerivedCategory.Plus C)
    (x : (RawRestrictedComparison.Evaluation.functor L R₀ ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).obj A) :
    (preadditiveYoneda.map ((shiftFunctor _ (q : ℤ)).map
        ((DerivedCategory.Plus.singleFunctor C 0).map φ))).app (op A) ≫
        (RawRestrictedComparison.Evaluation.evaluate
          (RawRestrictedComparison.Evaluation.functor L R₀ ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0) x ≫
          (RawRestrictedComparison.Evaluation.shiftIso L R₀ q G).hom) =
      (RawRestrictedComparison.Evaluation.evaluate
          (RawRestrictedComparison.Evaluation.functor L R₀ ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0) x ≫
        (RawRestrictedComparison.Evaluation.shiftIso L R₀ q F).hom) ≫
        (R₀.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
          (DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map (L.map φ))) := by
  rw [← Category.assoc, evaluate_naturality, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ RawRestrictedComparison.Evaluation.evaluate
          (RawRestrictedComparison.Evaluation.functor L R₀ ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0) x ≫ k)
      (evaluation_shiftIso_naturality L R₀ q φ)

private theorem raw_coefficient {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (V : S.Etale) :
    (normalizationRawCoefficient f q φ).app (op V) ≫
        rawRestrictedCohomologyComparison f q G V =
      rawRestrictedCohomologyComparison f q F V ≫
        normalizationRestrictedCoefficient f q φ V := by
  let W : X.Etale := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  let x := (RawRestrictedComparison.zeroIso W
    ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))).inv
      (RawRestrictedComparison.generator f V)
  exact evaluation_coefficient
    (upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f))
    (Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) q φ
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))) x


private theorem transported_naturality
    {C : Type*} [Category C] {P Q A B A' B' : C}
    (a : P ⟶ A) (b : Q ⟶ B) (t : P ⟶ Q) (i : A ≅ A') (j : B ≅ B')
    (s : A' ⟶ B') (h : t ≫ b ≫ j.hom = a ≫ i.hom ≫ s) :
    t ≫ b = a ≫ (i.hom ≫ s ≫ j.inv) := by
  apply (cancel_mono j.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem transported_map_eq
    {C : Type*} [Category C] {A B A' B' : C}
    (i : A ≅ A') (j : B ≅ B') (s : A' ⟶ B') (a : A ⟶ B)
    (h : a ≫ j.hom = i.hom ≫ s) :
    i.hom ≫ s ≫ j.inv = a := by
  apply (cancel_mono j.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm

private theorem transported_presheaf_map_eq
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    (A : C → D) (e : ∀ V : C, A V ≅ P.obj V)
    {V V' : C} (t : V ⟶ V') (a : A V ⟶ A V')
    (h : a ≫ (e V').hom = (e V).hom ≫ P.map t) :
    (normalizationTransportPresheaf P A e).map t = a :=
  transported_map_eq (e V) (e V') (P.map t) a h

private theorem transported_presheaf_iso
    {C D : Type*} [Category C] [Category D] (P Q : C ⥤ D)
    (A : C → D) (e : ∀ V : C, A V ≅ Q.obj V)
    (c : ∀ V : C, P.obj V ⟶ A V) (h : ∀ V : C, IsIso (c V))
    (hn : ∀ {V V' : C} (t : V ⟶ V'),
      P.map t ≫ c V' ≫ (e V').hom = c V ≫ (e V).hom ≫ Q.map t) :
    ∃ k : P ≅ normalizationTransportPresheaf Q A e,
      ∀ V : C, k.hom.app V = c V := by
  refine ⟨NatIso.ofComponents
    (fun V ↦ @asIso _ _ _ _ (c V) (h V)) ?_, fun V ↦ rfl⟩
  intro V V' t
  exact transported_naturality (c V) (c V') (P.map t) (e V) (e V') (Q.map t) (hn t)

private theorem comparison_class_value
    {A B C : AddCommGrpCat.{u + 1}} (c : A ⟶ B) (i : B ⟶ C) (k : A ⟶ C)
    (v : A → C) (h : c ≫ i = k) (hk : ∀ z : A, k z = v z) :
    ∀ z : A, i (c z) = v z := by
  intro z
  exact (ConcreteCategory.congr_hom h z).trans (hk z)

set_option backward.isDefEq.respectTransparency true in
/-- Raw evaluation is an isomorphism of presheaves, with the specified restriction,
cocycle class, sheafification lift and coefficient compatibilities.
Source: Stacks Project, Tags 03Q8 and 072W.
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).

Proof:
1. Use the chosen injective resolution. The three fixed-resolution comparisons
identify raw evaluation with section homology, chart pullback with restriction on
that homology, and the image of the section class with the canonical derived class.
2. Cancel the restricted resolution isomorphism in the first comparison. The raw
comparison is therefore natural. Its components are invertible by the existing
raw comparison theorem, so they assemble into the required presheaf isomorphism.
The second comparison identifies the transported presheaf restriction with the
specified cohomology pullback. The third gives the specified iota class formula.
3. The kappa class formula is its definition. Sheafification's Hom equivalence and
the library's constructed canonicalComparison_class identify normalizationLift
with canonicalComparison.hom. That map is invertible.
4. For coefficients, naturality of the derived adjunction Hom equivalence and the
homology shift comparison gives kappa naturality. Naturality of the restriction,
single and shift isomorphisms gives raw evaluation naturality in coefficients.
Cancel the invertible raw comparison and use the class formula to obtain iota
naturality. Finally apply sheafification's Hom equivalence to kappa naturality;
its naturality gives the required equality of sheafification lifts. -/
theorem rawRestrictedClassNormalization {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∃ c : abelianHigherDirectImageRawPresheaf f q F ≅
      normalizationRestrictedPresheaf f q F,
      ∀ V : S.Etale, c.hom.app (op V) = rawRestrictedCohomologyComparison f q F V) ∧
    (∀ (V V' : S.Etale) (t : V' ⟶ V),
      (normalizationRestrictedPresheaf f q F).map t.op =
        normalizationCohomologyRestriction f q F t) ∧
    (∀ (V : S.Etale) (z : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)),
      (normalizationKappa f q F).app (op V) z = abelianHigherDirectImageClass f q F V z) ∧
    IsIso (normalizationLift f q F) ∧
    (∀ (V : S.Etale) (z : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)),
      normalizationIota f q F V (rawRestrictedCohomologyComparison f q F V z) =
        abelianHigherDirectImageClass f q F V z) ∧
    (∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G),
      (∀ V : S.Etale,
        (normalizationRawCoefficient f q φ).app (op V) ≫
            rawRestrictedCohomologyComparison f q G V =
          rawRestrictedCohomologyComparison f q F V ≫
            normalizationRestrictedCoefficient f q φ V) ∧
      (∀ V : S.Etale,
        normalizationRestrictedCoefficient f q φ V ≫ normalizationIota f q G V =
          normalizationIota f q F V ≫ (normalizationHigherCoefficient f q φ).hom.app (op V)) ∧
      (normalizationRawCoefficient f q φ ≫ normalizationKappa f q G =
        normalizationKappa f q F ≫ (normalizationHigherCoefficient f q φ).hom) ∧
      ((presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (normalizationRawCoefficient f q φ) ≫ normalizationLift f q G =
        normalizationLift f q F ≫ normalizationHigherCoefficient f q φ)) := by
  refine ⟨?_, ?_,
    fun V z ↦ normalizationKappa_apply f q F V z,
    normalizationLift_isIso f q F, ?_, ?_⟩
  · obtain ⟨c, he⟩ := transported_presheaf_iso
      (abelianHigherDirectImageRawPresheaf f q F)
      ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ))
      (fun V ↦ rawAffineRestrictedCohomology f q F V.unop)
      (fun V ↦ normalizationRestrictedIso f q F (injectiveResolution F) V.unop)
      (fun V ↦ rawRestrictedCohomologyComparison f q F V.unop)
      (fun V ↦ isIso_rawRestrictedCohomologyComparison f q F V.unop)
      (fun t ↦ rawRestrictedResolution_naturality f q F t)
    exact ⟨c, fun V ↦ he (op V)⟩
  · intro V V' t
    exact transported_presheaf_map_eq
      ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ))
      (fun W ↦ rawAffineRestrictedCohomology f q F W.unop)
      (fun W ↦ normalizationRestrictedIso f q F (injectiveResolution F) W.unop)
      t.op (normalizationCohomologyRestriction f q F t)
      (rawRestrictedResolution_restriction f q F t)
  · intro V
    exact comparison_class_value
      (rawRestrictedCohomologyComparison f q F V) (normalizationIota f q F V)
      ((normalizationKappa f q F).app (op V))
      (abelianHigherDirectImageClass f q F V) (rawRestrictedResolution_class f q F V)
      (normalizationKappa_apply f q F V)
  · intro G φ
    exact ⟨raw_coefficient f q φ,
      normalizationIota_coefficient_of_class f q φ (rawRestrictedResolution_class f q F)
        (rawRestrictedResolution_class f q G) (raw_coefficient f q φ),
      normalizationKappa_coefficient f q φ, normalizationLift_coefficient f q φ⟩

end AlgebraicGeometry.Etale
