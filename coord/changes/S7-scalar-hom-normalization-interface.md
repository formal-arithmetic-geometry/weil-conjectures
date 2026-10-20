# CategoryTheory.ScalarHomTensorComparison

## Reason

Extract the existing data interface into `Sheaf.Algebra.Homology.ScalarInternalHomData`
so separate ordinary, chain, derived tensor and coefficient-tower proofs can import it
without importing their own conclusion. The original module publicly reexports it.
All existing declaration names, universes, categories, functors and equations are retained.
The normalization field was expensive to elaborate repeatedly. Its full representative
square is now a named Prop; the field has precisely that definitionally equal type.
Local irreducibility of the monoidal structure and representative comparison definitions
and transparency controls keep elaboration within the per-file limit.

The old and new field types are definitionally equal after unfolding
`ScalarHomTensorNormalization`. This is a performance and module dependency repair,
not a change in the mathematical meaning of any target. It does not add a hypothesis
or weaken a conclusion. The independent reader can compare the expanded normalization
square verbatim below. Target statement review should verify this definitional equality.

## Old

```lean
structure ScalarHomTensorComparison (a : R ⟶ S) where
  /-- Scalar extension carries K-flat complexes to K-flat complexes. -/
  preservesKFlat : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
  /-- The actual chain tensor comparison, with the differential signs retained. -/
  complexIso : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
    (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P,
         (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
  /-- It sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). -/
  generators : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((complexIso P Q).hom.f k).val.app V
        (scalarHomUnitSection M a _ V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
      coefficientTensorGenerator.{r, c, v} J S
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
        p q k h V (scalarHomUnitSection M a _ V x) (scalarHomUnitSection M a _ V y)
  /-- The natural derived strong tensor comparison. -/
  iso : (M.closed R).tensor ⋙ (M.scalar a).derived ≅
    ((M.scalar a).derived.prod (M.scalar a).derived) ⋙ (M.closed S).tensor
  /-- Its defining square on the actual K-flat representatives. -/
  normalization : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    (M.scalar a).derived.map
        ((CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
          P Q hp hq).hom) ≫
      iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (M.closed S).tensor.map (Prod.mkHom
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit P)
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit Q)) =
      scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
          (M.scalar a).derived (M.scalar a).counit
            ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (complexIso P Q).hom ≫
          (CoefficientTensorModels.iso.{r, c, v, w} J S (M.closed S) (M.model S)
            _ _ (preservesKFlat P hp) (preservesKFlat Q hq)).hom

```

## New

The following declarations are in `ScalarInternalHomData`; the item module has
`public import Sheaf.Algebra.Homology.ScalarInternalHomData`.

```lean
def ScalarHomTensorNormalization (a : R ⟶ S)
    (hE : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P))
    (e : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
      (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
        (coefficientTotalTensor.{r, c, v} J S).obj
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P,
           (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q))
    (μ : (M.closed R).tensor ⋙ (M.scalar a).derived ≅
      ((M.scalar a).derived.prod (M.scalar a).derived) ⋙ (M.closed S).tensor) : Prop :=
  ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    (M.scalar a).derived.map
        ((CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
          P Q hp hq).hom) ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (M.closed S).tensor.map (Prod.mkHom
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit P)
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit Q)) =
      scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
          (M.scalar a).derived (M.scalar a).counit
            ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (e P Q).hom ≫
          (CoefficientTensorModels.iso.{r, c, v, w} J S (M.closed S) (M.model S)
            _ _ (hE P hp) (hE Q hq)).hom

attribute [local irreducible] ScalarHomTensorNormalization

set_option backward.isDefEq.respectTransparency.types true in
/-- Strong scalar tensor comparison, retaining its actual pure-tensor normalization
before and after passage to the derived category.
Source: Stacks 07A4 and 0D6D
(blueprint: def-sfb-scalar-hom-comparison-data). -/
structure ScalarHomTensorComparison (a : R ⟶ S) where
  /-- Scalar extension carries K-flat complexes to K-flat complexes. -/
  preservesKFlat : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
  /-- The actual chain tensor comparison, with the differential signs retained. -/
  complexIso : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
    (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P,
         (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
  /-- It sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). -/
  generators : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((complexIso P Q).hom.f k).val.app V
        (scalarHomUnitSection M a _ V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
      coefficientTensorGenerator.{r, c, v} J S
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
        p q k h V (scalarHomUnitSection M a _ V x) (scalarHomUnitSection M a _ V y)
  /-- The natural derived strong tensor comparison. -/
  iso : (M.closed R).tensor ⋙ (M.scalar a).derived ≅
    ((M.scalar a).derived.prod (M.scalar a).derived) ⋙ (M.closed S).tensor
  /-- Its defining square on the actual K-flat representatives. -/
  normalization : ScalarHomTensorNormalization M a preservesKFlat complexIso iso

```

Every other data declaration formerly preceding the main theorem is copied verbatim,
except blueprint docstring references and local elaboration settings. Its name and
visibility remain public. No `WeilConjectures` file is changed.

## Users

`tools/downstream.py --uses CategoryTheory.ScalarHomTensorComparison` and the same
query for `ScalarHomModels` list the first two rows as actual named uses. The direct
importers are also listed; all retain the same declarations by the public reexport.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ScalarInternalHomAdjunction | S7 | Proved from extracted data and proof helpers; statement unchanged. |
| Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange | unclaimed | Original compiles unchanged (13.1 s); pre-existing long-line warning at line 24. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates | unclaimed | Original compiles unchanged (35.4 s). |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData | unclaimed | Original compiles unchanged (8.3 s). |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | C1 | Original compile timed out; a diagnostic with only its proof import changed to the extracted data compiled (58.1 s). No consumer adaptation is delivered, since no declaration/type change is required. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Original compiles unchanged (8.3 s). |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Original times out at 60 s against both the unchanged baseline item and this packet; no mathematical interface use or adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Original compiles unchanged (17.0 s). |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Original compiles unchanged (21.1 s). |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Original times out at 60 s against both the unchanged baseline item and this packet; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Original compiles unchanged (30.1 s). |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Original compiles unchanged (46.0 s); no adopted-source edit. |

| Sheaf.Paper.DirectImageChangeRingTranspose | quarantined, unclaimed | Lexical short-name match to its own scalar functor; it does not use the moved declarations. No adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | quarantined, unclaimed | Lexical short-name match to its own scalar functor; it does not use the moved declarations. No adaptation. |
| Sheaf.Paper.FiniteConstantModelResolution | quarantined, unclaimed | Lexical short-name match to its own scalar functor; it does not use the moved declarations. No adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | quarantined, unclaimed | Lexical short-name match to its own scalar functor; it does not use the moved declarations. No adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | quarantined, unclaimed | Lexical short-name match to its own scalar functor; it does not use the moved declarations. No adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | quarantined, unclaimed | Lexical short-name match to its own scalar functor; it does not use the moved declarations. No adaptation. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom | unclaimed | Same public reexport; no mathematical change or adaptation. |

The transitive import closure also includes SemidualizingRHomConservative,
RingedFiniteFreeHomBaseChange, RingedFiniteFreeHomBaseChangeHom,
RingedFiniteFreeHomBaseChangeTensor, AlgebraicShriekCalculus,
AlgebraicShriekRelativePerfect and UpperShriekBoundedCoherent. The original direct importers
above retain the same public interface to these modules. The shared checkout added
many importers during this session; its full downstream import closure now has 896
modules. None uses a changed mathematical definition.

## Status

landed 20261020T221348-L-4178240 2026-10-20 (merge of deliver/S7/Sheaf.Algebra.Homology.ScalarInternalHomAdjunction)
