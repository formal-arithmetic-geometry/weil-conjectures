# Native locally finite adic realization data and proof separation

## Reason

The native realization proof requires three independent mathematical steps: construct the
normalized functor and coefficient comparisons; prove derived Hom and object descent for
that functor; count native constructible sheaves. Their statements must refer to the
existing realization presentations without importing the theorem that uses them. Move
that data block verbatim to `Sheaf.Paper.LocallyFiniteAdicRealizationData`, publicly
reexported by the original module. Keep every original public import, especially
`WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion`: the previous R1 return
reported a lost lower-shriek export used by compact-support consumers. The current
source exports the open-extension API through this public import, which is retained.

Every old name, signature, definition body, instance and attribute is unchanged. No target
meaning changes. The additional normalized-functor structure omits Hom bijectivity,
essential image, and both smallness fields; it includes the actual common-field equation
in the construction, rather than asserting that equation for an arbitrary old core.
The long equation is wrapped in a concrete predicate to avoid repeated kernel checking
of its expanded expression in generated structure projections. This changes only the new
definition's presentation and no shared reducibility attribute.

## Old

The following block was in `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`.

```lean
/-- The native locally finite coefficient ring, read in abelian sheaves.
Source: Bhatt--Scholze, 6.8.1--6.8.2, native coefficient specialization
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
abbrev abRing :=
  (ProEtale.weilCoefficientsForgetAb l X).obj (ProEtale.adicConstantSheaf l X)

/-- The sectionwise ring of the native internal coefficient. Its underlying sections
are exactly the same locally finite continuous functions, with pointwise operations.
Source: Bhatt--Scholze, 6.8.1--6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def ringSheaf [IsCommMonObj (abRing l X)] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (ProEt.topology X) (abRing l X)

/-- The canonical section-module functor, retaining the native module action.
Source: internal-module convention of def-sf-native-weil-derived-framework and
Bhatt--Scholze, 6.8.1
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def sections [IsCommMonObj (abRing l X)] :=
  ProEtale.AdicSheaf.forgetAb l X ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) (abRing l X)).functor

/-- The specified finite-field inclusion, undoing only the published size transport.
Source: common finite-field convention and Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def embedding (E : Index l (PadicAlgCl l)) :
    Coefficient.{u} l (PadicAlgCl l) E →ₐ[Padic l] PadicAlgCl l :=
  E.val.val.comp (Shrink.algEquiv (Padic l) E.val).toAlgHom

/-- The inverse-limit and localization identifications used in one integral formula.
All ring maps are fixed pointwise, and all finite-quotient isomorphisms fix constants.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure CoefficientPresentation [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) where
  integral : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ≅
    completedIntegralCommRingSheafUnrestricted l E X
  finite : ∀ n : ℕ,
    integralCoefficientCommRingSheaf l E X n ≅
      finiteContinuousCoefficientSheaf l X E n
  finite_constants : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : finiteCoefficientRing l E n)
      (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finite n).hom.hom.app U ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (finiteCoefficientRing l E n))).app U a)) x = a
  integral_residues : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l
        E X n ≫ (finite n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X U s x)
  localization : integralCoefficientLocalization l X E ≅
    rationalCoefficientSheaf l X E
  localization_normalized : integralCoefficientLocalizationNormalized l
    E X localization.hom
  integralInclusion : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ⟶
    rationalCoefficientSheaf l X E
  integralInclusion_normalized : integralRationalCoefficientNormalized l
    E X integralInclusion
  rationalInclusion : rationalCoefficientSheaf l X E ⟶
    ringSheaf l X
  rationalInclusion_normalized : ∀ (U : X.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (rationalInclusion.hom.app U s).down.1 x =
      i (rationalCoefficientValue l E X U s x)

/-- The actual structural ring map B_integral to B_native. It is the composite of the
normalized completion identification, integral inclusion and finite-field inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def CoefficientPresentation.integralMap [IsCommMonObj (abRing l X)]
    {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {i : E →ₐ[Padic l] PadicAlgCl l} (C : CoefficientPresentation l X E i) :
    completedIntegralCommRingSheafUnrestricted l
      E X ⟶ ringSheaf l X :=
  C.integral.inv ≫ C.integralInclusion ≫ C.rationalInclusion

/-- One ordinary realization, with its exact essential image and full derived Hom
bijections. The comparison to the universal derived tensor functor is natural on
integral arrows; functoriality then sends inverse uniformizer powers to their inverses.
The common-stage category already uses balanced extension and eventual equality of
representatives, so its arrows, including arrows between different finite stages, are
realized by the same functor. The `common_field` equation fixes its transition
isomorphisms by the canonical completion map and balanced derived tensor associator;
HEq retains the published literal-object transports instead of selecting new isomorphisms.
Source: Bhatt--Scholze, Proposition 6.8.14 and the native smallness addendum
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure RealizationCore where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X
  J : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ⥤
    DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : J.Additive]
  [shift : J.CommShift ℤ]
  triangulated : J.IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective (J.map : (K ⟶ L) → (J.obj K ⟶ J.obj L))
  image : ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
    ∃ A, Nonempty (J.obj A ≅ K)
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
        J ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((coefficient E).integralMap l X)
  sourceSmall : EssentiallySmall.{u + 1}
    (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
  targetSmall : EssentiallySmall.{u + 1}
    (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory

/-- The specific completion map, read through the canonical derived tensor presentation.
This is the published map characterized by its quotient-completion chain map and counit.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def completedTensorComparison
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) :
    pbcDerivedExtend.{u} (completedCoefficientMap l E L i X) ⟶
      integralScalarExtensionOfUniverses l E L i X :=
  completedScalarComparison l E L i X

/-- The common-field identification is the specified completion and balanced-tensor map.
Source: Bhatt--Scholze, Proposition 6.8.14, and the completion-map scalar comparison
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def commonField (R : RealizationCore l X) : Prop :=
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
          (R.J.map ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨E, (sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom)))
      ((R.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((R.coefficient L).integralMap l X) ((R.coefficient E).integralMap l X)
          (R.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((R.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (R.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))

/-- A realization with its canonical common-field transition normalization.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure Realization extends RealizationCore l X where
  common_field : commonField l X toRealizationCore

```

## New

The identical block is in `Sheaf.Paper.LocallyFiniteAdicRealizationData`; the original
module publicly imports it and retains all original public imports.

```lean
/-- The native locally finite coefficient ring, read in abelian sheaves.
Source: Bhatt--Scholze, 6.8.1--6.8.2, native coefficient specialization
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
abbrev abRing :=
  (ProEtale.weilCoefficientsForgetAb l X).obj (ProEtale.adicConstantSheaf l X)

/-- The sectionwise ring of the native internal coefficient. Its underlying sections
are exactly the same locally finite continuous functions, with pointwise operations.
Source: Bhatt--Scholze, 6.8.1--6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def ringSheaf [IsCommMonObj (abRing l X)] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (ProEt.topology X) (abRing l X)

/-- The canonical section-module functor, retaining the native module action.
Source: internal-module convention of def-sf-native-weil-derived-framework and
Bhatt--Scholze, 6.8.1
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def sections [IsCommMonObj (abRing l X)] :=
  ProEtale.AdicSheaf.forgetAb l X ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) (abRing l X)).functor

/-- The specified finite-field inclusion, undoing only the published size transport.
Source: common finite-field convention and Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def embedding (E : Index l (PadicAlgCl l)) :
    Coefficient.{u} l (PadicAlgCl l) E →ₐ[Padic l] PadicAlgCl l :=
  E.val.val.comp (Shrink.algEquiv (Padic l) E.val).toAlgHom

/-- The inverse-limit and localization identifications used in one integral formula.
All ring maps are fixed pointwise, and all finite-quotient isomorphisms fix constants.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure CoefficientPresentation [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) where
  integral : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ≅
    completedIntegralCommRingSheafUnrestricted l E X
  finite : ∀ n : ℕ,
    integralCoefficientCommRingSheaf l E X n ≅
      finiteContinuousCoefficientSheaf l X E n
  finite_constants : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : finiteCoefficientRing l E n)
      (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finite n).hom.hom.app U ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (finiteCoefficientRing l E n))).app U a)) x = a
  integral_residues : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l
        E X n ≫ (finite n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X U s x)
  localization : integralCoefficientLocalization l X E ≅
    rationalCoefficientSheaf l X E
  localization_normalized : integralCoefficientLocalizationNormalized l
    E X localization.hom
  integralInclusion : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ⟶
    rationalCoefficientSheaf l X E
  integralInclusion_normalized : integralRationalCoefficientNormalized l
    E X integralInclusion
  rationalInclusion : rationalCoefficientSheaf l X E ⟶
    ringSheaf l X
  rationalInclusion_normalized : ∀ (U : X.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (rationalInclusion.hom.app U s).down.1 x =
      i (rationalCoefficientValue l E X U s x)

/-- The actual structural ring map B_integral to B_native. It is the composite of the
normalized completion identification, integral inclusion and finite-field inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def CoefficientPresentation.integralMap [IsCommMonObj (abRing l X)]
    {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {i : E →ₐ[Padic l] PadicAlgCl l} (C : CoefficientPresentation l X E i) :
    completedIntegralCommRingSheafUnrestricted l
      E X ⟶ ringSheaf l X :=
  C.integral.inv ≫ C.integralInclusion ≫ C.rationalInclusion

/-- One ordinary realization, with its exact essential image and full derived Hom
bijections. The comparison to the universal derived tensor functor is natural on
integral arrows; functoriality then sends inverse uniformizer powers to their inverses.
The common-stage category already uses balanced extension and eventual equality of
representatives, so its arrows, including arrows between different finite stages, are
realized by the same functor. The `common_field` equation fixes its transition
isomorphisms by the canonical completion map and balanced derived tensor associator;
HEq retains the published literal-object transports instead of selecting new isomorphisms.
Source: Bhatt--Scholze, Proposition 6.8.14 and the native smallness addendum
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure RealizationCore where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X
  J : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ⥤
    DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : J.Additive]
  [shift : J.CommShift ℤ]
  triangulated : J.IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective (J.map : (K ⟶ L) → (J.obj K ⟶ J.obj L))
  image : ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
    ∃ A, Nonempty (J.obj A ≅ K)
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
        J ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((coefficient E).integralMap l X)
  sourceSmall : EssentiallySmall.{u + 1}
    (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
  targetSmall : EssentiallySmall.{u + 1}
    (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory

/-- The specific completion map, read through the canonical derived tensor presentation.
This is the published map characterized by its quotient-completion chain map and counit.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def completedTensorComparison
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) :
    pbcDerivedExtend.{u} (completedCoefficientMap l E L i X) ⟶
      integralScalarExtensionOfUniverses l E L i X :=
  completedScalarComparison l E L i X

/-- The common-field identification is the specified completion and balanced-tensor map.
Source: Bhatt--Scholze, Proposition 6.8.14, and the completion-map scalar comparison
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def commonField (R : RealizationCore l X) : Prop :=
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
          (R.J.map ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨E, (sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom)))
      ((R.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((R.coefficient L).integralMap l X) ((R.coefficient E).integralMap l X)
          (R.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((R.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (R.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))

/-- A realization with its canonical common-field transition normalization.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure Realization extends RealizationCore l X where
  common_field : commonField l X toRealizationCore

```

The new `FunctorData`, `FunctorData.commonField`, and `NormalizedFunctor` definitions are
in `Sheaf.Paper.LocallyFiniteAdicNormalizedFunctorData` and are owned by
`def-sf-locally-finite-adic-normalized-functor`. They assume no descent or smallness.
The final theorem obtains their witness only inside a proof of Nonempty; no definition
chooses data from an unproved existence theorem.

## Users

The table includes all 182 transitive importers found by tools/downstream.py, hence every
textual user of a relocated name. Holders are from the shared claim snapshot. No consumer
is edited. Direct consumers are checked against the delivered overlay.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | M2 | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCoefficientRingReindexing | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCommonPullbackIdentityUnit | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCompletedTensorCommonLift | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftAgreement | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCompletedTensorFiniteModelCore | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCompletedTensorFiniteModelExistence | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCompletedTensorFiniteModels | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicIntegralReindexingDescent | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicNormalizedPullbackRealization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicProperOrdinaryPushPreservation | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingComposition | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingCore | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingHom | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingIdentity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingTensorCompatibility | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicReindexingUnitCompatibility | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.AdicTensorReindexingModels | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.CoefficientPresentationIntegralMapIndependence | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.CompactSupportStageActionAdjunction | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportData | unclaimed in shared snapshot | Direct importer; unchanged API through public reexport; compile against overlay. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed in shared snapshot | Direct importer; unchanged API through public reexport; compile against overlay. |
| Sheaf.Paper.LocallyFiniteCompactSupportStageAction | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed in shared snapshot | Direct importer; unchanged API through public reexport; compile against overlay. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCoefficientInverseImage | unclaimed in shared snapshot | Direct importer; unchanged API through public reexport; compile against overlay. |
| Sheaf.Paper.NativeCompactSupportFiniteComparison | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence | D6 | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompactSupportGeometry | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompactSupportIntegralLocalization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompactSupportScalarMateInvertible | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompletedCoefficientChange | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeCompletedCoefficientChangeData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeDirectImageSections | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed in shared snapshot | Direct importer; unchanged API through public reexport; compile against overlay. |
| Sheaf.Paper.NativePinnedCounitData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativePinnedCounitDataExistence | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeProperScalarMateBoundedBelow | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilComparisonStructure | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilFreeCoproduct | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilHeartProperties | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilInductionSummands | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed in shared snapshot | Direct importer; unchanged API through public reexport; compile against overlay. |
| Sheaf.Paper.NativeWeilProperNormalization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed in shared snapshot | Direct importer; unchanged API through public reexport; compile against overlay. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalHomTransport | H6 | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.StructuralBidualInvertible | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.StructuralDualizingIdentification | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| TargetsCheck | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.Statement | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.Curve | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.Examples | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |
| WeilConjectures.ZetaFunction.Weights | unclaimed in shared snapshot | Transitive importer; unchanged names, signatures, bodies and public import closure. |

## Status

landed 20261027T234035-L-4169620 2026-10-27 (merge of deliver/K3/Sheaf.Paper.LocallyFiniteAdicConstructibleRealization)
