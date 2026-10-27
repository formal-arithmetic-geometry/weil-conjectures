# IntegralImmersionNormalization comparison data

## Reason

Move the existing presentations and clauses verbatim into a data module so two independent proof lemmas can refer to them without importing the theorem they help prove. The item publicly reexports the data module. Every existing name, universe, signature, body, scalar action and shift convention is preserved. No source-library file changes and no target meaning changes.

## Old

In lean/Sheaf/Paper/IntegralImmersionPullbackNormalization.lean:

```lean
namespace WeilConjectures.IntegralImmersionNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Inverse coefficient transport along the existing normalized completed-ring iso.
Source: Stacks 099N, coefficient identification
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev back (T : Scheme.{u}) :=
  pbcDerivedRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom

/-- The scalar restriction round trip is identity on every module section.
Source: Stacks 03DA; coefficient identification in the localization proof
(blueprint: lem-sf-integral-immersion-pullback-normalization).
Proof: both coefficient restrictions leave underlying sections and maps unchanged.
Their composite action is the original action by the inverse identities of the ring
iso. The sectionwise identity and its inverse define the natural iso; the equation
on all sections determines every component, hence proves uniqueness. -/
theorem moduleRoundTrip_exists (T : Scheme.{u}) :
    ∃! e : pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom ⋙
        pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv ≅
          𝟭 (scalarReductionSource.{u, u} l E T),
      ∀ (M : scalarReductionSource.{u, u} l E T) (V : T.ProEtᵒᵖ) (x : M.val.obj V),
        ((e.hom.app M).val.app V) x = x := by
  let e := ImmersionCompletedPullback.completedRingIso l E T
  have hV (V : T.ProEtᵒᵖ) :
      RingHom.id _ = (e.hom.hom.app V).hom.comp (e.inv.hom.app V).hom := by
    exact congrArg (fun f ↦ (f.hom.app V).hom) e.inv_hom_id.symm
  let eM (M : scalarReductionSource.{u, u} l E T) :
      (pbcRestrict e.inv).obj ((pbcRestrict e.hom).obj M) ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        (ModuleCat.restrictScalarsComp'App (e.inv.hom.app V).hom
          (e.hom.hom.app V).hom (RingHom.id _) (hV V) (M.val.obj V)).symm ≪≫
            ModuleCat.restrictScalarsId'App _ rfl (M.val.obj V))
        (fun {V W} f ↦ by ext x; rfl))
  let η : pbcRestrict e.hom ⋙ pbcRestrict e.inv ≅ 𝟭 _ :=
    NatIso.ofComponents eM (fun f ↦ by ext V x; rfl)
  refine ⟨η, ?_, ?_⟩
  · intro M V x
    rfl
  · intro η' hη'
    apply Iso.ext
    ext M V x
    exact hη' M V x

/-- The unique identity-on-sections coefficient restriction round trip.
Source: Stacks 03DA
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def moduleRoundTrip (T : Scheme.{u}) := (moduleRoundTrip_exists l E T).exists.choose

/-- Descent of that identity-on-sections comparison, using exact restriction.
Source: Stacks 015F, 03DA
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def roundTrip (T : Scheme.{u}) :
    back l E T ⋙ ImmersionCompletedPullback.transport l E T ≅
      𝟭 (DerivedCategory (scalarReductionSource.{u, u} l E T)) :=
  (Functor.mapDerivedCategoryCompIso
    (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom)
    (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (moduleRoundTrip l E T) ≪≫
        Functor.mapDerivedCategoryIdIso _

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The canonical completed coefficient isomorphism, in the recorded integral presentation.
Source: Stacks 098T; the finite-projection-normalized coefficient transport
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def coefficientIso :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X) ≅
      completedIntegralCommRingSheafUnrestricted l E Y :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (ImmersionCompletedPullback.completedRingIso l E X).symm ≪≫
    (pbcIntegralDatum l E).integralRingIso g ≪≫
      ImmersionCompletedPullback.completedRingIso l E Y

/-- The finite coefficient comparison with the same prescribed quotient identifications.
Source: Stacks 098T
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def finiteCoefficientIso (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E X n) ≅
      integralCoefficientCommRingSheaf l E Y n :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (ImmersionCompletedPullback.finiteRingIso l E X n).symm ≪≫
    (pbcIntegralDatum l E).finiteRingIso g n ≪≫
      ImmersionCompletedPullback.finiteRingIso l E Y n

/-- The coefficient identifications keep constants, projections and the entire quotient
system, in its existing function-sheaf presentation. Source: Stacks 098T and 097N
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def CoefficientNormalization : Prop :=
  (∀ (V : X.ProEt) (r : Padic.coefficientExtensionIntegers l E),
    (((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _)
      (coefficientIso l E g).hom).hom.app (op V)).hom
        (integralScalarConstant l E X (op V) r)) =
      integralScalarConstant l E Y (op ((proEtaleBaseChange g).obj V)) r) ∧
  (∀ n : ℕ, (coefficientIso l E g).hom ≫
      completedIntegralCommRingProjectionUnrestricted l E Y n =
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (completedIntegralCommRingProjectionUnrestricted l E X n) ≫
        (finiteCoefficientIso l E g n).hom) ∧
  ∀ (b a : ℕᵒᵖ) (h : b ⟶ a),
    ((pbcIntegralDatum l E).finiteRingIso g b.unop).hom ≫
        (reductionCoefficientSystem Y (pbcIntegralDatum l E)).map h =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        ((reductionCoefficientSystem X (pbcIntegralDatum l E)).map h) ≫
          ((pbcIntegralDatum l E).finiteRingIso g a.unop).hom

/-- Ordinary module inverse image with the specified coefficient identification.
The two restrictions only identify the existing completed-ring presentations.
Source: Stacks 03D2; localization integral paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev ordinaryModule :=
  pbcRestrict (ImmersionCompletedPullback.completedRingIso l E X).hom ⋙
    ImmersionCompletedPullback.modulePull l E g ⋙
      pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv

/-- Ordinary pullback with its canonical termwise derived shift comparison.
Source: Stacks 015F, 03D2
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev ordinary := (ordinaryModule l E g).mapDerivedCategory

/-- The original strict quotient-tower completed pullback, in the recorded integral
coefficient category. Source: Stacks 099N(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev completed := back l E X ⋙
  pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙
    ImmersionCompletedPullback.transport l E Y

/-- The counit-normalized comparison with ordinary termwise inverse image.
Source: Stacks 015F and the recorded immersion comparison
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def ordinaryPresentation :
    back l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        ImmersionCompletedPullback.transport l E Y ≅ ordinary l E g :=
  isoWhiskerLeft (back l E X)
    (isoWhiskerRight (ImmersionCompletedPullback.derivedIso l E g)
      (ImmersionCompletedPullback.transport l E Y)) ≪≫
    isoWhiskerLeft (back l E X)
      (Functor.mapDerivedCategoryCompIso (ImmersionCompletedPullback.modulePull l E g)
        (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso
      (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E X).hom)
      (ImmersionCompletedPullback.modulePull l E g ⋙
        pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv)).symm

/-- The actual completion comparison, built from the published strict quotient unit.
Source: Stacks 099N(2),(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def completionComparison : ordinary l E g ⟶ completed l E g :=
  (ordinaryPresentation l E g).inv ≫
    whiskerLeft (back l E X)
      (whiskerRight (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g)
        (ImmersionCompletedPullback.transport l E Y))

/-- The actual finite projection of strict pullback, transported to integral coefficients.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def finiteProjection (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (ImmersionCompletedPullback.transport l E Y).map
    (ImmersionCompletedPullback.actualCompletedProjection l E g ((back l E X).obj K) n)

/-- A fixed interval for every positive reduction, including empty intervals.
Source: localization integral paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def HasReductionInterval (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) (a b : ℤ) : Prop :=
  ∀ n : ℕ, proEtaleCohomologicalSupport
    ((scalarReductionDerivedExtension.{u, u} l E T n).obj K) ⊆ Set.Icc a b

/-- The normalized comparisons and their exact, scalar-linear constructible restrictions.
The integral comparison contains its representative projection and canonical signed-shift
normalization. The displayed gamma is required to be exactly its transport to the original
strict construction. Thus no arbitrary isomorphism or arbitrary shift is substituted.
Source: localization integral/rational paragraphs; Stacks 09AA, 099N, 0941 and 015F
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
structure Comparison where
  coefficients : CoefficientNormalization l E g
  integralComparison : IntegralCompletedComparison.Comparison l E g
  complete_back : ∀ K : sfIntegralConstructibleCategory l E X,
    IntegralCompletedComparison.Complete l E ((back l E X).obj K.obj)
  gamma : (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g ≅
    (sfIntegralConstructible l E X).ι ⋙ completed l E g
  gamma_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    gamma.hom.app K =
      (integralDerivedPullback l E g).map ((roundTrip l E X).inv.app K.obj) ≫
      (integralComparison.gamma ((back l E X).obj K.obj) (complete_back K)).hom ≫
      (ImmersionCompletedPullback.transport l E Y).map
        ((IntegralCompletedComparison.towerIso l E g).inv.app
          ⟨(back l E X).obj K.obj,
            integralComparison.intrinsic ((back l E X).obj K.obj) (complete_back K)⟩)
  c : (sfIntegralConstructible l E X).ι ⋙ ordinary l E g ≅
    (sfIntegralConstructible l E X).ι ⋙ completed l E g
  c_hom : c.hom = whiskerLeft (sfIntegralConstructible l E X).ι
    (completionComparison l E g)
  completion_projections : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    c.hom.app K ≫ finiteProjection l E g K.obj n =
      (ordinaryPresentation l E g).inv.app K.obj ≫
        (ImmersionCompletedPullback.transport l E Y).map
          ((ImmersionCompletedPullback.reductionUnit l E Y n).app
            ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj
              ((back l E X).obj K.obj)))
  completion_transitions : ∀ (K : sfIntegralConstructibleCategory l E X)
      (b a : ℕ) (h : a ≤ b),
    finiteProjection l E g K.obj b ≫
      (ImmersionCompletedPullback.transport l E Y).map
        (ImmersionCompletedPullback.reductionTransition l E Y b a h
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj
            ((back l E X).obj K.obj))) = finiteProjection l E g K.obj a
  completedShift : (completed l E g).CommShift ℤ
  gamma_shifts :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ]
      [_sc : (completed l E g).CommShift ℤ] ↦ NatTrans.CommShift gamma.hom ℤ)
      (_si := integralComparison.derivedShift) (_sc := completedShift)
  completion_shifts :
    (fun [_sc : (completed l E g).CommShift ℤ] ↦
      NatTrans.CommShift c.hom ℤ) (_sc := completedShift)
  composite_shifts :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ] ↦
      NatTrans.CommShift (gamma ≪≫ c.symm).hom ℤ)
        (_si := integralComparison.derivedShift)
  ordinary_exact : ((sfIntegralConstructible l E X).ι ⋙ ordinary l E g).IsTriangulated
  integral_exact :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ] ↦
      ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g).IsTriangulated)
      (_si := integralComparison.derivedShift)
  completed_exact :
    (fun [_sc : (completed l E g).CommShift ℤ] ↦
      ((sfIntegralConstructible l E X).ι ⋙ completed l E g).IsTriangulated)
      (_sc := completedShift)
  ordinary_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ ordinary l E g)
  integral_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g)
  completed_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ completed l E g)
  constructible : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((ordinary l E g).obj K.obj) ∧
    sfIntegralConstructible l E Y ((completed l E g).obj K.obj) ∧
    sfIntegralConstructible l E Y ((integralDerivedPullback l E g).obj K.obj)
  interval : ∀ (K : sfIntegralConstructibleCategory l E X) (a b : ℤ),
    HasReductionInterval l E X K.obj a b →
      HasReductionInterval l E Y ((integralDerivedPullback l E g).obj K.obj) a b

/-- The finite perfect quotients, with the specified two-term free resolution and quotient
augmentation. Source: Stacks 0657; localization coefficient paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def FinitePerfectQuotients : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Finite (Padic.coefficientExtensionRing l E n) ∧
    ∃ P : CochainComplex (ModuleCat (Padic.coefficientExtensionIntegers l E)) ℤ,
      P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0 ∧
      (∀ q : ℤ, Module.Free (Padic.coefficientExtensionIntegers l E) (P.X q) ∧
        Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X q)) ∧
      ∃ (em : P.X (-1) ≅ ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l E))
        (e0 : P.X 0 ≅ ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l E))
        (ε : P ⟶ (CochainComplex.singleFunctor
          (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
            (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionRing l E n))),
        P.d (-1) 0 = em.hom ≫ ModuleCat.ofHom
          (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionUniformizer l E ^ n)) ≫ e0.inv ∧
        QuasiIso ε ∧
        ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionRing l E n))).hom =
          e0.hom ≫ ModuleCat.ofHom
            (AlgHom.toLinearMap (Ideal.Quotient.mkₐ (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIdeal l E n)))

end WeilConjectures.IntegralImmersionNormalization
```

## New

The same declarations, verbatim, occur in lean/Sheaf/Paper/IntegralImmersionPullbackNormalizationData.lean. The original module publicly imports it, preserving its importer-visible declarations:

```lean
namespace WeilConjectures.IntegralImmersionNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Inverse coefficient transport along the existing normalized completed-ring iso.
Source: Stacks 099N, coefficient identification
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev back (T : Scheme.{u}) :=
  pbcDerivedRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom

/-- The scalar restriction round trip is identity on every module section.
Source: Stacks 03DA; coefficient identification in the localization proof
(blueprint: lem-sf-integral-immersion-pullback-normalization).
Proof: both coefficient restrictions leave underlying sections and maps unchanged.
Their composite action is the original action by the inverse identities of the ring
iso. The sectionwise identity and its inverse define the natural iso; the equation
on all sections determines every component, hence proves uniqueness. -/
theorem moduleRoundTrip_exists (T : Scheme.{u}) :
    ∃! e : pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom ⋙
        pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv ≅
          𝟭 (scalarReductionSource.{u, u} l E T),
      ∀ (M : scalarReductionSource.{u, u} l E T) (V : T.ProEtᵒᵖ) (x : M.val.obj V),
        ((e.hom.app M).val.app V) x = x := by
  let e := ImmersionCompletedPullback.completedRingIso l E T
  have hV (V : T.ProEtᵒᵖ) :
      RingHom.id _ = (e.hom.hom.app V).hom.comp (e.inv.hom.app V).hom := by
    exact congrArg (fun f ↦ (f.hom.app V).hom) e.inv_hom_id.symm
  let eM (M : scalarReductionSource.{u, u} l E T) :
      (pbcRestrict e.inv).obj ((pbcRestrict e.hom).obj M) ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        (ModuleCat.restrictScalarsComp'App (e.inv.hom.app V).hom
          (e.hom.hom.app V).hom (RingHom.id _) (hV V) (M.val.obj V)).symm ≪≫
            ModuleCat.restrictScalarsId'App _ rfl (M.val.obj V))
        (fun {V W} f ↦ by ext x; rfl))
  let η : pbcRestrict e.hom ⋙ pbcRestrict e.inv ≅ 𝟭 _ :=
    NatIso.ofComponents eM (fun f ↦ by ext V x; rfl)
  refine ⟨η, ?_, ?_⟩
  · intro M V x
    rfl
  · intro η' hη'
    apply Iso.ext
    ext M V x
    exact hη' M V x

/-- The unique identity-on-sections coefficient restriction round trip.
Source: Stacks 03DA
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def moduleRoundTrip (T : Scheme.{u}) := (moduleRoundTrip_exists l E T).exists.choose

/-- Descent of that identity-on-sections comparison, using exact restriction.
Source: Stacks 015F, 03DA
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def roundTrip (T : Scheme.{u}) :
    back l E T ⋙ ImmersionCompletedPullback.transport l E T ≅
      𝟭 (DerivedCategory (scalarReductionSource.{u, u} l E T)) :=
  (Functor.mapDerivedCategoryCompIso
    (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom)
    (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (moduleRoundTrip l E T) ≪≫
        Functor.mapDerivedCategoryIdIso _

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The canonical completed coefficient isomorphism, in the recorded integral presentation.
Source: Stacks 098T; the finite-projection-normalized coefficient transport
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def coefficientIso :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X) ≅
      completedIntegralCommRingSheafUnrestricted l E Y :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (ImmersionCompletedPullback.completedRingIso l E X).symm ≪≫
    (pbcIntegralDatum l E).integralRingIso g ≪≫
      ImmersionCompletedPullback.completedRingIso l E Y

/-- The finite coefficient comparison with the same prescribed quotient identifications.
Source: Stacks 098T
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def finiteCoefficientIso (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E X n) ≅
      integralCoefficientCommRingSheaf l E Y n :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (ImmersionCompletedPullback.finiteRingIso l E X n).symm ≪≫
    (pbcIntegralDatum l E).finiteRingIso g n ≪≫
      ImmersionCompletedPullback.finiteRingIso l E Y n

/-- The coefficient identifications keep constants, projections and the entire quotient
system, in its existing function-sheaf presentation. Source: Stacks 098T and 097N
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def CoefficientNormalization : Prop :=
  (∀ (V : X.ProEt) (r : Padic.coefficientExtensionIntegers l E),
    (((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _)
      (coefficientIso l E g).hom).hom.app (op V)).hom
        (integralScalarConstant l E X (op V) r)) =
      integralScalarConstant l E Y (op ((proEtaleBaseChange g).obj V)) r) ∧
  (∀ n : ℕ, (coefficientIso l E g).hom ≫
      completedIntegralCommRingProjectionUnrestricted l E Y n =
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (completedIntegralCommRingProjectionUnrestricted l E X n) ≫
        (finiteCoefficientIso l E g n).hom) ∧
  ∀ (b a : ℕᵒᵖ) (h : b ⟶ a),
    ((pbcIntegralDatum l E).finiteRingIso g b.unop).hom ≫
        (reductionCoefficientSystem Y (pbcIntegralDatum l E)).map h =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        ((reductionCoefficientSystem X (pbcIntegralDatum l E)).map h) ≫
          ((pbcIntegralDatum l E).finiteRingIso g a.unop).hom

/-- Ordinary module inverse image with the specified coefficient identification.
The two restrictions only identify the existing completed-ring presentations.
Source: Stacks 03D2; localization integral paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev ordinaryModule :=
  pbcRestrict (ImmersionCompletedPullback.completedRingIso l E X).hom ⋙
    ImmersionCompletedPullback.modulePull l E g ⋙
      pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv

/-- Ordinary pullback with its canonical termwise derived shift comparison.
Source: Stacks 015F, 03D2
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev ordinary := (ordinaryModule l E g).mapDerivedCategory

/-- The original strict quotient-tower completed pullback, in the recorded integral
coefficient category. Source: Stacks 099N(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev completed := back l E X ⋙
  pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙
    ImmersionCompletedPullback.transport l E Y

/-- The counit-normalized comparison with ordinary termwise inverse image.
Source: Stacks 015F and the recorded immersion comparison
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def ordinaryPresentation :
    back l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        ImmersionCompletedPullback.transport l E Y ≅ ordinary l E g :=
  isoWhiskerLeft (back l E X)
    (isoWhiskerRight (ImmersionCompletedPullback.derivedIso l E g)
      (ImmersionCompletedPullback.transport l E Y)) ≪≫
    isoWhiskerLeft (back l E X)
      (Functor.mapDerivedCategoryCompIso (ImmersionCompletedPullback.modulePull l E g)
        (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso
      (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E X).hom)
      (ImmersionCompletedPullback.modulePull l E g ⋙
        pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv)).symm

/-- The actual completion comparison, built from the published strict quotient unit.
Source: Stacks 099N(2),(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def completionComparison : ordinary l E g ⟶ completed l E g :=
  (ordinaryPresentation l E g).inv ≫
    whiskerLeft (back l E X)
      (whiskerRight (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g)
        (ImmersionCompletedPullback.transport l E Y))

/-- The actual finite projection of strict pullback, transported to integral coefficients.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def finiteProjection (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (ImmersionCompletedPullback.transport l E Y).map
    (ImmersionCompletedPullback.actualCompletedProjection l E g ((back l E X).obj K) n)

/-- A fixed interval for every positive reduction, including empty intervals.
Source: localization integral paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def HasReductionInterval (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) (a b : ℤ) : Prop :=
  ∀ n : ℕ, proEtaleCohomologicalSupport
    ((scalarReductionDerivedExtension.{u, u} l E T n).obj K) ⊆ Set.Icc a b

/-- The normalized comparisons and their exact, scalar-linear constructible restrictions.
The integral comparison contains its representative projection and canonical signed-shift
normalization. The displayed gamma is required to be exactly its transport to the original
strict construction. Thus no arbitrary isomorphism or arbitrary shift is substituted.
Source: localization integral/rational paragraphs; Stacks 09AA, 099N, 0941 and 015F
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
structure Comparison where
  coefficients : CoefficientNormalization l E g
  integralComparison : IntegralCompletedComparison.Comparison l E g
  complete_back : ∀ K : sfIntegralConstructibleCategory l E X,
    IntegralCompletedComparison.Complete l E ((back l E X).obj K.obj)
  gamma : (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g ≅
    (sfIntegralConstructible l E X).ι ⋙ completed l E g
  gamma_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    gamma.hom.app K =
      (integralDerivedPullback l E g).map ((roundTrip l E X).inv.app K.obj) ≫
      (integralComparison.gamma ((back l E X).obj K.obj) (complete_back K)).hom ≫
      (ImmersionCompletedPullback.transport l E Y).map
        ((IntegralCompletedComparison.towerIso l E g).inv.app
          ⟨(back l E X).obj K.obj,
            integralComparison.intrinsic ((back l E X).obj K.obj) (complete_back K)⟩)
  c : (sfIntegralConstructible l E X).ι ⋙ ordinary l E g ≅
    (sfIntegralConstructible l E X).ι ⋙ completed l E g
  c_hom : c.hom = whiskerLeft (sfIntegralConstructible l E X).ι
    (completionComparison l E g)
  completion_projections : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    c.hom.app K ≫ finiteProjection l E g K.obj n =
      (ordinaryPresentation l E g).inv.app K.obj ≫
        (ImmersionCompletedPullback.transport l E Y).map
          ((ImmersionCompletedPullback.reductionUnit l E Y n).app
            ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj
              ((back l E X).obj K.obj)))
  completion_transitions : ∀ (K : sfIntegralConstructibleCategory l E X)
      (b a : ℕ) (h : a ≤ b),
    finiteProjection l E g K.obj b ≫
      (ImmersionCompletedPullback.transport l E Y).map
        (ImmersionCompletedPullback.reductionTransition l E Y b a h
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj
            ((back l E X).obj K.obj))) = finiteProjection l E g K.obj a
  completedShift : (completed l E g).CommShift ℤ
  gamma_shifts :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ]
      [_sc : (completed l E g).CommShift ℤ] ↦ NatTrans.CommShift gamma.hom ℤ)
      (_si := integralComparison.derivedShift) (_sc := completedShift)
  completion_shifts :
    (fun [_sc : (completed l E g).CommShift ℤ] ↦
      NatTrans.CommShift c.hom ℤ) (_sc := completedShift)
  composite_shifts :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ] ↦
      NatTrans.CommShift (gamma ≪≫ c.symm).hom ℤ)
        (_si := integralComparison.derivedShift)
  ordinary_exact : ((sfIntegralConstructible l E X).ι ⋙ ordinary l E g).IsTriangulated
  integral_exact :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ] ↦
      ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g).IsTriangulated)
      (_si := integralComparison.derivedShift)
  completed_exact :
    (fun [_sc : (completed l E g).CommShift ℤ] ↦
      ((sfIntegralConstructible l E X).ι ⋙ completed l E g).IsTriangulated)
      (_sc := completedShift)
  ordinary_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ ordinary l E g)
  integral_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g)
  completed_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ completed l E g)
  constructible : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((ordinary l E g).obj K.obj) ∧
    sfIntegralConstructible l E Y ((completed l E g).obj K.obj) ∧
    sfIntegralConstructible l E Y ((integralDerivedPullback l E g).obj K.obj)
  interval : ∀ (K : sfIntegralConstructibleCategory l E X) (a b : ℤ),
    HasReductionInterval l E X K.obj a b →
      HasReductionInterval l E Y ((integralDerivedPullback l E g).obj K.obj) a b

/-- The finite perfect quotients, with the specified two-term free resolution and quotient
augmentation. Source: Stacks 0657; localization coefficient paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def FinitePerfectQuotients : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Finite (Padic.coefficientExtensionRing l E n) ∧
    ∃ P : CochainComplex (ModuleCat (Padic.coefficientExtensionIntegers l E)) ℤ,
      P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0 ∧
      (∀ q : ℤ, Module.Free (Padic.coefficientExtensionIntegers l E) (P.X q) ∧
        Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X q)) ∧
      ∃ (em : P.X (-1) ≅ ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l E))
        (e0 : P.X 0 ≅ ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l E))
        (ε : P ⟶ (CochainComplex.singleFunctor
          (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
            (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionRing l E n))),
        P.d (-1) 0 = em.hom ≫ ModuleCat.ofHom
          (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionUniformizer l E ^ n)) ≫ e0.inv ∧
        QuasiIso ε ∧
        ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionRing l E n))).hom =
          e0.hom ≫ ModuleCat.ofHom
            (AlgHom.toLinearMap (Ideal.Quotient.mkₐ (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIdeal l E n)))

end WeilConjectures.IntegralImmersionNormalization
```

## Users

All modules returned by tools/downstream.py are below, including direct declaration users. Names resolve through the public reexport with the same types and bodies. No consumer requires adaptation and no module held by another group is edited. The shared snapshot records no local claim for these unchanged consumers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicClosureScalarCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageHeartExactness | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteScalarCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingCore | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingFunctoriality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingHom | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingTensor | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.BarrettIndRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationIdentity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompletedPullbackFractionDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionCyclicSheetPartition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetTensorSplitting | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateAdjunctionComposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerCompactTranspose | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerExceptionalCompositors | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationFusion | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CurveClassicalPullbackExists | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.CurveRestrictionLocalPowers | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.DerivedTensorRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteSheafH0Augmentation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.GeometricCommonStageDirectImage | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralClosedSupportNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralLissePullbackNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralOpenSupportNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralSupportNormalizationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeChoiceExistence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLiftData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeLisseDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeSingleComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LissePointNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedPullbackNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.NormalizedPullbackObjects | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OpenWeilCarrierRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OpenWeilCoefficientFibres | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OpenWeilGeometricFibres | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.OrientationLocalResidue | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointIdentityExchangeRecipe | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointScalarPunctualSpectrum | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointWeilAlgebraicFlag | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlagData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ProperSupportFiniteAdjunction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ProperWeilIterateGermFormula | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityChernClasses | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityKummerTriangleConcentration | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityTateDatum | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalAmbientPullComposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalAmbientPullModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalBalancedFreePullback | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalContinuousFiltrationModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalContinuousPullbackTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalPullSingleComputation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationHomTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarBalancedLocalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalStalkExact | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RealWeights | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReconstructedBrownMateLaws | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementCommon | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RelativeKummerSiteNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RelativeKunneth | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RelativeKunnethClosedFibre | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RelativeKunnethConstructions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreComponentData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreComponents | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SectionsRationalModelComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearCommonSupportCubes | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearGermIterationDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SemilinearRationalSupportCubes | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationExactDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TensorHeartSpecialization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TensorHomExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThom | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilGeometricFiberProperties | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilIndOpenRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilIndOpenRepresentability | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilIndProperOpenHigher | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionRestrictionAssembly | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionAssembly | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionTExact | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlWeilPullCompositorEquivariance | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | no local claim recorded | Same public declarations through reexport; no adaptation. |
| Sheaf.Paper.IntegralImmersionPullbackNormalization | no local claim recorded | Same public declarations through reexport; no adaptation. |

## Status

landed 20261026T070255-L-3512892 2026-10-26 (merge of deliver/M3/Sheaf.Paper.IntegralImmersionPullbackNormalization)
