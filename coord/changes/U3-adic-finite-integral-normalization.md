# WeilConjectures.AdicFiniteRealization.ScalarData

## Reason

The previous integral clause used HEq to equate theta for the literal-identity PBC
transition with theta for ordinary tensor extension. HEq also equates the sources of
the two arrows. For E = F the former source is J(QK), whereas the latter is
J(Q(K tensor B_E)); the actual tensor unitor is an isomorphism between these objects,
not an equality of the derived objects. For unequal fields the completed ring maps
also have two uniquely isomorphic presentations. This is an interface error, not a
property supplied by the cited scalar comparison.

Use the two normalized single-derived-tensor flattenings as the common target and
insert J_F of the published pbcScalarIntegralComparison on the PBC side. This is the
actual integral diagram of BS 6.8.14(2) and the node's steps 5--6. It retains all
scalar normalization content without identifying distinct tensor presentations.

The data declarations move to Sheaf.Paper.AdicFiniteRealizationData with the same
names and visibility, and the item publicly reexports that module. This is needed
so each of three strictly smaller proof-step modules can import the definitions
without importing the theorem it is used to prove. Every other existing definition body,
structure field and the final theorem signature is unchanged. This separation was
chosen before compilation and is not a workaround for a compile-time limit.

Profiling then identified repeated kernel checking of the expanded integral diagram
in ScalarData recursors. Its identical proposition is packaged as the public
irreducible predicate integralNormalization; the integral field refers to that
predicate with the same coefficient, theta and completed_square arguments.
scalarComparison, sectionDerived and closureComparison are marked irreducible,
with unchanged bodies and types. These changes reduce the data module's timing
run from over 85 seconds to about 29 seconds; no file was split for timing.

## Old

```lean
structure ScalarData (C : Core l T) where
  coefficient : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    RationalRealizationScalarComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) F)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) h) T
      (C.realization E) (C.realization F)
  theta : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    (pbcScalarSystem l (PadicAlgCl l) T dT.out iT.out).T h ⋙ (C.realization F).J ≅
      (C.realization E).J ⋙ pbcDerivedExtend (coefficient h).coefficient
  integral : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F)
      (K : pbcIntegralStage l (PadicAlgCl l) T E),
    HEq ((theta h).hom.app ((pbcStageLocalization l (PadicAlgCl l) T E).obj K))
      ((coefficient h).theta.hom.app
        ((pbcStageLocalization l (PadicAlgCl l) T E).obj K))
```

## New

```lean
@[irreducible] def integralNormalization (C : Core l T)
    (coefficient : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    RationalRealizationScalarComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) F)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) h) T
      (C.realization E) (C.realization F))
    (theta : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    (pbcScalarSystem l (PadicAlgCl l) T dT.out iT.out).T h ⋙ (C.realization F).J ≅
      (C.realization E).J ⋙ pbcDerivedExtend (coefficient h).coefficient)
    (completed_square : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F),
    pbcCompletedScalarMap l (PadicAlgCl l) T h ≫
        rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) F) (C.realization F) =
      rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
        (coefficient h).coefficient) : Prop :=
  ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F)
      (K : pbcIntegralStage l (PadicAlgCl l) T E),
    (theta h).hom.app ((pbcStageLocalization l (PadicAlgCl l) T E).obj K) ≫
      (pbcDerivedExtend (coefficient h).coefficient).map
        (eqToHom ((C.realization E).objects K)) ≫
      (pbcReductionNormalization
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E))
        (coefficient h).coefficient
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
          (coefficient h).coefficient) rfl K.obj).hom =
    (C.realization F).J.map
      ((pbcScalarIntegralComparison l (PadicAlgCl l) T dT.out iT.out h).hom.app K) ≫
      eqToHom ((C.realization F).objects
        ((pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out h).obj K)) ≫
      (pbcReductionNormalization (pbcCompletedScalarMap l (PadicAlgCl l) T h)
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) F) (C.realization F))
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
          (coefficient h).coefficient) (completed_square h) K.obj).hom

/-- Continuous finite-field comparisons, including their integral normalization.
The comparison for completed S is subsequently composed with raw.beta inverse.
Source: BS 6.8.14(2); quotient comparison of the node
(blueprint: def-sf-adic-finite-realization-data). -/
structure ScalarData (C : Core l T) where
  coefficient : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    RationalRealizationScalarComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) F)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) h) T
      (C.realization E) (C.realization F)
  theta : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    (pbcScalarSystem l (PadicAlgCl l) T dT.out iT.out).T h ⋙ (C.realization F).J ≅
      (C.realization E).J ⋙ pbcDerivedExtend (coefficient h).coefficient
  completed_square : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F),
    pbcCompletedScalarMap l (PadicAlgCl l) T h ≫
        rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) F) (C.realization F) =
      rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
        (coefficient h).coefficient
  integral : integralNormalization l T C coefficient theta completed_square
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicFiniteRealizationCocone | U3 | Publicly reexport its data module; prove the item by construction. |
| Sheaf.Paper.AdicFiniteRealizationData | new, U3 | Own all existing data declarations; repair the integral diagram. |
| Sheaf.Paper.AdicFiniteScalarCoherence | new, U3 | State only finite scalar comparisons and their actual coherence. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | new, U3 | State native coefficient cocone and constructibility transport. |
| Sheaf.Paper.AdicClosureScalarCoherence | new, U3 | State preservation of coherence by closure scalar extension. |

`python3 tools/downstream.py Sheaf.Paper.AdicFiniteRealizationCocone` reports zero
current Lean importers. The DAG parents still need the item and are preserved;
there is no withdrawal. The target signatures are unchanged. Any future target use
of these data should read the corrected integral diagram as part of statement review.

## Status

landed 20261025T203334-L-2806294 2026-10-25 (merge of deliver/U3/Sheaf.Paper.AdicFiniteRealizationCocone)
