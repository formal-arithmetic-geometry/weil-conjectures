# WeilConjectures.OpenSemilinearTensor comparison interfaces

## Reason

Move the existing interface declarations verbatim into
`Sheaf.SixFunctors.OpenSemilinearTensorModelData`, publicly imported by the original module.
Ordinary scalar comparison and augmented reduction computation need these interfaces to state
independent lemmas. Keeping their definitions in the existence module would make those proof
imports cyclic. No declaration name, signature, universe, attribute or body changes. The
original declaration block and the extracted block have been compared byte for byte.

## Old

In `Sheaf.SixFunctors.OpenSemilinearTensorModel`:

```lean
/-- The existing ordinary open operations, including their actual adjunctions.
Source: Stacks 03DI--03DJ, 0E8I (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev Operations := IntegralOpenReduction.Operations l E j

variable (o : Operations l E j)

/-- Termwise ordinary open extension, without imposing a representative condition.
Source: Stacks 0GL1 (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev extensionComplex :=
  (IntegralOpenReduction.extension l E j o).mapHomologicalComplex (.up ℤ)

/-- Termwise ordinary restriction.
Source: Stacks 0GL1 (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev restrictionComplex :=
  (IntegralOpenReduction.restriction l E j o).mapHomologicalComplex (.up ℤ)

/-- The published total tensor, with its direct sums and signed differential.
Source: Stacks 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev total (T : Scheme.{t}) := totalTensor.{t + 1, t, max u (t + 1)} (ProEt.topology T)
  (completedIntegralCommRingSheafUnrestricted l E T)

/-- The published ordinary sheaf tensor.
Source: Stacks 03EK (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev tensor (T : Scheme.{t}) := ordinaryTensor.{t + 1, t, max u (t + 1)}
  (ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)

/-- The recorded summand insertion in the total tensor, with no extra sign.
Source: Stacks 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev summand (T : Scheme.{t}) := tensorSummand.{t + 1, t, max u (t + 1)}
  (ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)

/-- Identify a restricted section through the actual slice-equivalence counit.
This writes the canonical identification, rather than assuming an arbitrary map of sections.
Source: Stacks 03DJ (blueprint: lem-sf-open-semilinear-tensor-model). -/
def restrictedSection (N : scalarReductionSource l E X) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (y : ((IntegralOpenReduction.restriction l E j o).obj N).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) : N.val.obj (op V) :=
  (o.integral.counitIso.hom.app
    ((SheafOfModules.localizedSystemRestriction.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (IntegralOpenReduction.openObject j)).obj N)).val.app (op (Over.mk a))
    (((eqToHom o.integralFunctor.symm).app
      ((IntegralOpenReduction.restriction l E j o).obj N)).val.app (op (Over.mk a)) y)

/-- The family of ordinary open tensor isomorphisms.
Source: Stacks 0E8I, 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev OrdinaryTensorComparison :=
  ∀ (M : scalarReductionSource l E U) (N : scalarReductionSource l E X),
    tensor l E X ((IntegralOpenReduction.extension l E j o).obj M) N ≅
      (IntegralOpenReduction.extension l E j o).obj
        (tensor l E U M ((IntegralOpenReduction.restriction l E j o).obj N))

/-- The family of signed total tensor chain isomorphisms.
Source: Stacks 0E8I, 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
abbrev TotalTensorComparison :=
  ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ),
    (total l E X).obj ((extensionComplex l E j o).obj Q, F) ≅
      (extensionComplex l E j o).obj
        ((total l E U).obj (Q, (restrictionComplex l E j o).obj F))

/-- Naturality of the ordinary isomorphism in both module maps.
Source: Stacks 0E8I, 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
def OrdinaryNaturality (μ : OrdinaryTensorComparison l E j o) : Prop :=
  ∀ {M M' : scalarReductionSource l E U}
    {N N' : scalarReductionSource l E X} (f : M ⟶ M') (g : N ⟶ N'),
    ordinaryTensorHom.{t + 1, t, max u (t + 1)} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)
        ((IntegralOpenReduction.extension l E j o).map f) g ≫ (μ M' N').hom =
      (μ M N).hom ≫ (IntegralOpenReduction.extension l E j o).map
        (ordinaryTensorHom.{t + 1, t, max u (t + 1)} (ProEt.topology U)
          (completedIntegralCommRingSheafUnrestricted l E U) f
          ((IntegralOpenReduction.restriction l E j o).map g))

/-- The ordinary comparison on every extension-sheafification generator.
Source: Stacks 0E8I, 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
def OrdinaryGenerators (μ : OrdinaryTensorComparison l E j o) : Prop :=
  ∀ (M : scalarReductionSource l E U) (N : scalarReductionSource l E X)
    (V : X.ProEt) (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))))
    (y : ((IntegralOpenReduction.restriction l E j o).obj N).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
    ((μ M N).hom.val.app (op V))
      (tensorSection.{t + 1, t, max u (t + 1)} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) _ N (op V)
        (IntegralOpenReduction.extensionSection l E j o M V a x)
        (restrictedSection l E j o N V a y)) =
      IntegralOpenReduction.extensionSection l E j o _ V a
        (tensorSection.{t + 1, t, max u (t + 1)} (ProEt.topology U)
          (completedIntegralCommRingSheafUnrestricted l E U) M _
          (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x y)

/-- Each total summand is the displayed ordinary comparison, without extra signs.
Source: Stacks 0E8I, 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
def TotalSummands (μ : OrdinaryTensorComparison l E j o)
    (φ : TotalTensorComparison l E j o) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (a b d : ℤ) (h : a + b = d),
    summand l E X ((extensionComplex l E j o).obj Q) F a b d h ≫ (φ Q F).hom.f d =
      (μ (Q.X a) (F.X b)).hom ≫
        (IntegralOpenReduction.extension l E j o).map
          (summand l E U Q ((restrictionComplex l E j o).obj F) a b d h)

/-- Naturality in both chain maps of the total comparison.
Source: Stacks 0E8I, 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
def TotalNaturality (φ : TotalTensorComparison l E j o) : Prop :=
  ∀ {Q Q' : CochainComplex (scalarReductionSource l E U) ℤ}
    {F F' : CochainComplex (scalarReductionSource l E X) ℤ} (f : Q ⟶ Q') (g : F ⟶ F'),
    (total l E X).map (Prod.mkHom ((extensionComplex l E j o).map f) g) ≫
        (φ Q' F').hom =
      (φ Q F).hom ≫ (extensionComplex l E j o).map
        ((total l E U).map (Prod.mkHom f ((restrictionComplex l E j o).map g)))

/-- Ordinary and total comparisons with the generator and summand normalizations.
Source: Stacks 0E8I, 012Z (blueprint: lem-sf-open-semilinear-tensor-model). -/
structure TotalComparison where
  ordinary : OrdinaryTensorComparison l E j o
  chain : TotalTensorComparison l E j o
  ordinary_naturality : OrdinaryNaturality l E j o ordinary
  generators : OrdinaryGenerators l E j o ordinary
  summands : TotalSummands l E j o ordinary chain
  naturality : TotalNaturality l E j o chain

/-- A single ordinary reduction functor, retaining every quotient square before deriving.
Its evaluation comparisons are natural in modules, not chosen separately for each complex.
Source: Stacks 06YY, 0941 (blueprint: lem-sf-open-semilinear-tensor-model). -/
structure OrdinaryReduction (T : Scheme.{t}) where
  functor : scalarReductionSource l E T ⥤ coefficientSequenceModules l E T
  [additive : functor.Additive]
  evaluation : ∀ n : ℕ, functor ⋙ coefficientSequenceEvaluation l E T n ≅
    scalarReductionExtension l E T n
  quotient : ∀ (M : scalarReductionSource l E T) (m n : ℕ) (h : n ≤ m),
    (coefficientSequenceTransition l E T h).app (functor.obj M) ≫
        (normalizedDVRModuleRes l E T h).map ((evaluation n).hom.app M) =
      (evaluation m).hom.app M ≫ (coefficientOrdinaryQuotient l E T h).app M

attribute [instance] OrdinaryReduction.additive

/-- Evaluation on complexes is the termwise ordinary evaluation, with its composition
comparisons inserted explicitly. Source: Stacks 0941
(blueprint: lem-sf-open-semilinear-tensor-model). -/
def OrdinaryReduction.complexEvaluation {T : Scheme.{t}} (A : OrdinaryReduction l E T)
    (Q : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
    ((coefficientSequenceEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj
      ((A.functor.mapHomologicalComplex (.up ℤ)).obj Q) ≅
        ((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)).obj Q :=
  (NatIso.mapHomologicalComplex (A.evaluation n) (.up ℤ)).app Q

/-- The specified simultaneous computation, with both the quotient equations and the
actual scalar-unit augmentation. Source: Stacks 06YS, 06YY, 0941
(blueprint: lem-sf-open-semilinear-tensor-model). -/
structure Computation {T : Scheme.{t}} (S : CoefficientDerivedSystemCalculus l E T)
    (A : OrdinaryReduction l E T) (Q : CochainComplex (scalarReductionSource l E T) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted l E T) Q) where
  iso : S.reduction.obj (DerivedCategory.Q.obj Q) ≅
    DerivedCategory.Q.obj ((A.functor.mapHomologicalComplex (.up ℤ)).obj Q)
  presentation : CoefficientReductionPresentation l E T S.toCoefficientDerivedSystemReduction
    Q hQ _ iso (A.complexEvaluation l E Q)
  augmentation : IntegralOpenReduction.AugmentedPresentation l E T S Q _ iso
    (A.complexEvaluation l E Q)

/-- Open extension preserves the actual independent-coefficient K-flat predicate.
Source: Stacks 0GL1, 06YS, 0941 (blueprint: lem-sf-open-semilinear-tensor-model). -/
def KFlatPreservation : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U) Q →
      flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology U)
        (completedIntegralCommRingSheafUnrestricted l E U) Q →
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        ((extensionComplex l E j o).obj Q)

/-- The ordinary strict-system isomorphism applied termwise to complexes.
Source: Stacks 0941 (blueprint: lem-sf-open-semilinear-tensor-model). -/
def ordinaryChain (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)
    (e : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
      AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ) :
    (AX.functor.mapHomologicalComplex (.up ℤ)).obj ((extensionComplex l E j o).obj Q) ≅
      ((IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ)).obj
        ((AU.functor.mapHomologicalComplex (.up ℤ)).obj Q) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ e.app (Q.X i))
    (fun i k _h ↦ (e.hom.naturality (Q.d i k)).symm)

/-- The strict chain comparison localizes under the canonical augmented computations.
Source: Stacks 0GL1, 06YS, 0941 (blueprint: lem-sf-open-semilinear-tensor-model). -/
def RepresentativeSquare (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)
    (r : IntegralOpenReduction.shriek l E j o ⋙ SX.reduction ≅
      SU.reduction ⋙ IntegralOpenReduction.J l E j o)
    (ordinary : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
      AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o)
    (hk : KFlatPreservation l E j o) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U) Q)
    (hf : flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology U)
      (completedIntegralCommRingSheafUnrestricted l E U) Q),
    ∃ (cU : Computation l E SU AU Q hQ)
      (cX : Computation l E SX AX ((extensionComplex l E j o).obj Q) (hk Q hQ hf)),
    r.hom.app (DerivedCategory.Q.obj Q) ≫
        (IntegralOpenReduction.J l E j o).map cU.iso.hom ≫
        (IntegralOpenReduction.systemExtension l E j o).mapDerivedCategoryFactors.hom.app
          ((AU.functor.mapHomologicalComplex (.up ℤ)).obj Q) =
      SX.reduction.map
          ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        cX.iso.hom ≫ DerivedCategory.Q.map
          (ordinaryChain l E j o AX AU ordinary Q).hom

/-- The comparison is constructed in the strict system category. Its localization is
fixed by the representative square on the specified augmented computations, for every
flat-term K-flat representative, and is natural on the entire derived category.
Source: Stacks 0GL1, 0E8I, 06YS, 0941
(blueprint: lem-sf-open-semilinear-tensor-model). -/
structure Comparison (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)
    (tensorComparison : IntegralOpenReduction.TensorComparison l E j o) where
  totalComparison : TotalComparison l E j o
  preservesFlatTerms : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U) Q →
    flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology U)
        (completedIntegralCommRingSheafUnrestricted l E U) Q →
      flatTerms.{t + 1, t, max u (t + 1)} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) ((extensionComplex l E j o).obj Q)
  kflat : KFlatPreservation l E j o
  ordinary : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
    AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o
  components : ∀ (M : scalarReductionSource l E U) (n : ℕ),
    (coefficientSequenceEvaluation l E X n).map (ordinary.hom.app M) ≫
        (IntegralOpenReduction.extensionEvaluation l E j o n).hom.app (AU.functor.obj M) ≫
        (IntegralOpenReduction.finiteExtension l E j o n).map ((AU.evaluation n).hom.app M) =
      (AX.evaluation n).hom.app ((IntegralOpenReduction.extension l E j o).obj M) ≫
        (tensorComparison.ordinary n).hom.app M
  r : IntegralOpenReduction.shriek l E j o ⋙ SX.reduction ≅
    SU.reduction ⋙ IntegralOpenReduction.J l E j o
  model : RepresentativeSquare l E j o SX SU AX AU r ordinary kflat
```

## New

The exact declaration block above now occurs in
`Sheaf.SixFunctors.OpenSemilinearTensorModelData`. The original module replaces that block by:

```lean
public import Sheaf.SixFunctors.OpenSemilinearTensorModelData
```

## Users

The downstream query included every moved declaration. The latest scan lists nine
transitive importers, including the four direct importers CompletedOpenTensorSystemRealization,
BasicRealizationShiftSquare, OpenRoosUnitAdjunction and OpenTensorQuotientAugmentation.
The table also preserves four additional importers from the earlier snapshot; their
interfaces are unchanged as well. Occurrences may be indirect or share an unqualified name.
The theorem statement and all definitions it uses retain exactly their former meaning;
no target statement review is reopened by a semantic change.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicRealizationIsomorphismNormalization` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarProjectionIdentification` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.Paper.CompletedOpenTensorSystemRealization` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationCommonStage` | T1 | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.Paper.SfRationalLocalizationOrthogonality` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | A5 | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletion` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenRoosUnitAdjunction` | P2 | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare` | unclaimed | Same declarations, publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenTensorQuotientAugmentation` | unclaimed | Same declarations, publicly reexported; no adaptation. |

## Status

landed 20261025T043154-L-1688691 2026-10-25 (merge of deliver/A7/Sheaf.SixFunctors.OpenSemilinearTensorModel)
