# Strict étale coefficient transport interfaces

## Reason

The assigned composition theorem concerns exceptional right adjoints. Its geometric
input is the strictly smaller cocycle for compact-support projection squares, before
choosing any exceptional adjoints. That lemma needs the existing coefficient change,
transport, inverse-image square and tensor composition records. Their present owner
is the theorem module, so importing its geometric input would form a cycle. Move only
these declarations unchanged to `Sheaf.Paper.EtaleCoefficientTransportInterfaces` and
publicly re-export that module from the old owner. No target type, coefficient category,
functor, natural transformation, data field, equation, instance, or public declaration
signature changes. Exceptional-adjoint data remain in the assigned module.

This extraction serves an import dependency, not the compile-time limit. No upstream
source module is changed. All existing public imports of the assigned module remain.

## Old

The following declaration signatures (and their complete bodies) are defined in
`Sheaf.Paper.EtaleCoefficientSystemAdjoint`:

```lean
theorem strictCoefficientMap_kills (n : ℕ) (x : O) (hx : x ∈ (Ideal.span ({ell} : Set O)) ^ (n + 1)) : Ideal.Quotient.mk ((Ideal.span ({φ ell} : Set O')) ^ (n + 1)) (φ x) = 0
def strictCoefficientRingMap (n : ℕ) : O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1) →+* O' ⧸ (Ideal.span ({φ ell} : Set O')) ^ (n + 1)
def strictCoefficientSheafMap (T : Scheme.{u}) (n : ℕ) : coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell n ⟶ coefficientQuotientSheaf (J := T.smallEtaleTopology) O' (φ ell) n
def strictEtaleTransition {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O} (M : strictEtaleCoefficientSystem T O ell) (n : ℕ)
structure StrictEtaleCoefficientChange (O O' : Type (u + 1)) [CommRing O] [CommRing O'] (ell : O) (mu : O') (phi : O →+* O') (index : ℕ →o ℕ)
def StrictEtaleCoefficientChange.sheaf {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n : ℕ) : coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell (index n) ⟶ coefficientQuotientSheaf (J := T.smallEtaleTopology) O' mu n
abbrev StrictEtaleLevelScalar {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n : ℕ)
structure StrictEtaleCoefficientTransportData {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu)
def StrictEtaleCoefficientTransportCoherence {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu) (record : StrictEtaleCoefficientTransportData a T PA PB) : Prop
def StrictEtaleCoefficientTransport {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu)
abbrev StrictEtaleCoefficientTransport.ordinary (record : StrictEtaleCoefficientTransport a T PA PB)
abbrev StrictEtaleCoefficientTransport.additive (record : StrictEtaleCoefficientTransport a T PA PB)
abbrev StrictEtaleCoefficientTransport.unit (record : StrictEtaleCoefficientTransport a T PA PB)
abbrev StrictEtaleCoefficientTransport.derived (record : StrictEtaleCoefficientTransport a T PA PB)
abbrev StrictEtaleCoefficientTransport.factors (record : StrictEtaleCoefficientTransport a T PA PB)
abbrev StrictEtaleCoefficientTransport.level (record : StrictEtaleCoefficientTransport a T PA PB)
abbrev StrictEtaleCoefficientTransport.derivedEvaluation (record : StrictEtaleCoefficientTransport a T PA PB)
def StrictEtaleTransportQuotientCoherence {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}} {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu} (U : StrictEtaleCoefficientTransport a T PA PB) (ordinary : ∀ {m n : ℕ} (h : n ≤ m), coefficientTensor (J := T.smallEtaleTopology) (O := O) (ell := ell) (index.monotone h) ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) ≅ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T m) ⋙ coefficientTensor (J := T.smallEtaleTopology) (O := O') (ell := mu) h) (derived : ∀ {m n : ℕ} (h : n ≤ m), (PA.scalar (index.monotone h)).derived ⋙ (U.level n).derived ≅ (U.level m).derived ⋙ (PB.scalar h).derived) : Prop
def StrictEtaleTransportQuotient {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}} {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu} (U : StrictEtaleCoefficientTransport a T PA PB)
abbrev StrictEtaleTransportQuotient.derived (record : StrictEtaleTransportQuotient U) : ∀ {m n : ℕ} (h : n ≤ m), (PA.scalar (index.monotone h)).derived ⋙ (U.level n).derived ≅ (U.level m).derived ⋙ (PB.scalar h).derived
def StrictEtaleCoefficientTransport.setUnit {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}} {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu} (U : StrictEtaleCoefficientTransport a T PA PB) (n : ℕ)
def strictEtaleInverseUnderlying {O : Type (u + 1)} [CommRing O] {ell : O} {T S : Scheme.{u}} {g : T ⟶ S} (A : StrictEtaleOrdinaryImage O ell g) (n : ℕ) : (A.inverse ⋙ coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) ⋙ coefficientUnderlying (J := T.smallEtaleTopology) O ell n ≅ coefficientEvaluation (J := S.smallEtaleTopology) (O := O) (ell := ell) n ⋙ (coefficientUnderlying (J := S.smallEtaleTopology) O ell n ⋙ Scheme.etaleSetPullback g)
def StrictEtaleInverseTransportCoherence {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T S : Scheme.{u}} {g : T ⟶ S} {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell} {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu} (UT : StrictEtaleCoefficientTransport a T PTA PTB) (US : StrictEtaleCoefficientTransport a S PSA PSB) (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g) (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj) (DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj) (ordinary : US.ordinary ⋙ B.inverse ≅ A.inverse ⋙ UT.ordinary) (derived : US.derived ⋙ DB.inverse ≅ DA.inverse ⋙ UT.derived) : Prop
def StrictEtaleInverseTransport {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ} {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T S : Scheme.{u}} {g : T ⟶ S} {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell} {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu} (UT : StrictEtaleCoefficientTransport a T PTA PTB) (US : StrictEtaleCoefficientTransport a S PSA PSB) (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g) (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj) (DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj)
abbrev StrictEtaleInverseTransport.derived (record : StrictEtaleInverseTransport UT US A B DA DB) : US.derived ⋙ DB.inverse ≅ DA.inverse ⋙ UT.derived
structure StrictEtaleCompactSupportTransportData
def StrictEtaleCompactSupportTransportCoherence (record : StrictEtaleCompactSupportTransportData a c SA SB TX TY TZ) : Prop
def StrictEtaleCompactSupportTransport
abbrev StrictEtaleCompactSupportTransport.openComparison (record : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ)
abbrev StrictEtaleCompactSupportTransport.properComparison (record : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ)
def StrictEtaleCompactSupportTransport.projection (P : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ) : SA.functor ⋙ TY.derived ≅ TX.derived ⋙ SB.functor
def StrictEtaleCoefficientChange.comp {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃] {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃} {r₁₂ r₂₃ : ℕ →o ℕ} (a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂) (b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃) : StrictEtaleCoefficientChange O₁ O₃ ell₁ ell₃ (phi₂₃.comp phi₁₂) (r₁₂.comp r₂₃)
def StrictEtaleTransportCompositionCoherence {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃] {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃} {r₁₂ r₂₃ : ℕ →o ℕ} {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂} {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃} {T : Scheme.{u}} {P₁ : StrictEtaleEvaluation T O₁ ell₁} {P₂ : StrictEtaleEvaluation T O₂ ell₂} {P₃ : StrictEtaleEvaluation T O₃ ell₃} (U₁₂ : StrictEtaleCoefficientTransport a T P₁ P₂) (U₂₃ : StrictEtaleCoefficientTransport b T P₂ P₃) (U₁₃ : StrictEtaleCoefficientTransport (a.comp b) T P₁ P₃) (ordinary : U₁₂.ordinary ⋙ U₂₃.ordinary ≅ U₁₃.ordinary) (derived : U₁₂.derived ⋙ U₂₃.derived ≅ U₁₃.derived) : Prop
def StrictEtaleTransportComposition {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃] {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃} {r₁₂ r₂₃ : ℕ →o ℕ} {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂} {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃} {T : Scheme.{u}} {P₁ : StrictEtaleEvaluation T O₁ ell₁} {P₂ : StrictEtaleEvaluation T O₂ ell₂} {P₃ : StrictEtaleEvaluation T O₃ ell₃} (U₁₂ : StrictEtaleCoefficientTransport a T P₁ P₂) (U₂₃ : StrictEtaleCoefficientTransport b T P₂ P₃) (U₁₃ : StrictEtaleCoefficientTransport (a.comp b) T P₁ P₃)
abbrev StrictEtaleTransportComposition.derived (record : StrictEtaleTransportComposition U₁₂ U₂₃ U₁₃) : U₁₂.derived ⋙ U₂₃.derived ≅ U₁₃.derived
def StrictEtaleTransportIdentityCoherence {O : Type (u + 1)} [CommRing O] {ell : O} {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)} {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell} (U : StrictEtaleCoefficientTransport a T P P) (ordinary : U.ordinary ≅ 𝟭 _) (derived : U.derived ≅ 𝟭 _) : Prop
def StrictEtaleTransportIdentity {O : Type (u + 1)} [CommRing O] {ell : O} {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)} {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell} (U : StrictEtaleCoefficientTransport a T P P)
abbrev StrictEtaleTransportIdentity.derived (record : StrictEtaleTransportIdentity U) : U.derived ≅ 𝟭 _
```

## New

These exact signatures and bodies are now defined in
`Sheaf.Paper.EtaleCoefficientTransportInterfaces`. A source comparison using the project's
declaration parser verified equality of every moved signature and body. Their docstrings
now cite the new definition-owner node. The old owner gains:

```lean
public import Sheaf.Paper.EtaleCoefficientTransportInterfaces
import Sheaf.Paper.StrictEtaleCompactSupportComposition
```

Its composition proof applies the latter's compact-support projection cocycle, and
proves the exceptional mate equation by a private categorical lemma. All existing
importers retain every moved declaration through the public re-export; their mathematical
statements and their definitions mean exactly the same things. No consumer is adapted. The assigned module also adds two proved private additive-instance
aliases, and explicitly normalizes composite objects in its private identity-mate proof.
These change no public signature or mathematical data. The complete sandbox passed
`lcompile.py --all` with exit 0 (result `2e4301c16d4ab043214923d1`).

## Users

The source-only `tools/downstream.py --uses`/`stage3_delivery.downstream_users` scan was
run for every relocated declaration. This table includes every textual consumer (the
scan matches final name segments and therefore deliberately over-approximates uses
of common names such as `derived`). Holders are read from current claim records.
All rows retain exactly the same API through the old module's public import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | C1 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | E3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | D4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | J1 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | B7 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | B8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemSupport | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | B3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | D8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | M7 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Q3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunction | G9 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | C6 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | R2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | C8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalProOriginExactLinear | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalProperOpenOriginComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalSiteOriginComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalSystemInterfaces | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ExceptionalSystemTransport | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | V6 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | F1 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | K9 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | W9 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | C4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | M4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | S3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | G4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | A2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | V4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | M7 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | N1 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | W4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | Y7 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.FreeInsertionCompactSupportCoherence | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | S6 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | J2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedStrictSystems | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.LineKummerFieldRealization | P9 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.LineZeroClassExchange | Z6 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.P1KummerTraceSiteTransport | W8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | E5 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | W2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | B3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PuritySectionEtaleRestriction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PuritySectionRestrictionData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | R8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | A5 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | N3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | Q4 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | F2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | X2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | S2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | R9 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | Y8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | Q1 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | K3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | N3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | T2 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | X6 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | B8 | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | J7 | Public re-export and composition proof. |
| Sheaf.Paper.EtaleCoefficientTransportInterfaces | J7 (new) | Sole owner of relocated declarations. |
| Sheaf.Paper.StrictEtaleCompactSupportComposition | J7 (new) | Strictly geometric cocycle statement. |

## Status

landed 20261025T204745-L-3005538 2026-10-25 (merge of deliver/J7/Sheaf.Paper.EtaleCoefficientSystemAdjoint)
