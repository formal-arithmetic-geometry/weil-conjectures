## What changed

Corrected the auxiliary pullback normalization in
`Sheaf.Paper.IntegralComparisonRealizationModels`: it now tests whole-system
adjunction-coherent quotient presentations. Added
`IsIntegralComparisonPresentationCoherent`, a real proposition specifying the
strict tensor-unit transpose of the comparison in the derived tower category.
This corrects the invisible-twist defect already documented in the T6 report.
The main theorem's text is unchanged; its model interface is explicitly repaired.
No target statement or definition used to state a target is edited. The item
node's previously truncated prose is completed to the existing Lean signature.
The existing Roos-map definition receives an explicit return type, with its
value and elaborated type unchanged, to reduce repeated type inference. Its Roos
model field is also factored through IsIntegralComparisonRoosNormalized, whose
unfolding is the original field equation; this shortens structure elaboration
without changing any mathematical normalization.

The proposed main proof constructs its realization from an ordinary quotient model, its
derived comparison to the supplied calculus, the strict pullback tower comparison,
and the supplied Roos comparison. The existing uniqueness clause of
`integralOperationsWellDefined` descends this natural isomorphism to the ambient
derived category. For an arbitrary coherent presentation, the strict quotient
isomorphism supplies q; naturality and cancellation of a followed by a inverse
prove the required Roos equation. The proof does not use faithfulness of finite
derived evaluations. Its proof-only imports are the two new modules below.

The correction record is `coord/changes/S9-pullback-presentation-coherence.md`.
It contains the original and corrected predicates verbatim, the counterexample,
the fourteen-module pullback audit, the thirty-one-module audit for the
definitionally unchanged Roos-field factor, and all existing DAG citers. No consumer
code adaptation has been necessary. The unclaimed realization-model module's
existing complete proofs and the scalar predicate are retained.

Verification resumed on 2026-10-26. The required initial deliver3.py run
reached elaboration. The repaired interface compiled in 39.7 seconds, and the two
new statement modules compiled in 38.5 and 35.7 seconds. The main proof exposed
one unclosed functor cancellation; this is repaired by explicit map_comp,
hom_inv_id and map_id rewrites. Profiling then identified expensive kernel
checking of an unnecessary elimination of the tensor-descent existence package.
The proof now projects only the pullback uniqueness property, retaining abstract
ordinary and derived model witnesses. The complete main proof compiled in
48.2 seconds, with kernel checking reduced from 45.6 to 26.1 seconds. All
profiling settings were removed before final delivery. No time limit was raised.
An intervening check failed before elaboration because the published snapshot
was missing DerivedCategory.Constructible.olean; the subsequent supported compile
succeeded. No shared build or launcher script was changed. Final delivery checks
are run by deliver3.py.

## Proved and sorry left

The item originally had one hole. Its only declaration,
`WeilConjectures.primitiveQuotientPullbackModelExistence`, now contains a complete
assembly proof for the explicitly corrected model interface. The complete
proof has compiled within the required 60-second limit. No `sorry` remains in the item or the adapted definition module. This does not prove the old,
false arbitrary-presentation normalization.

Two genuine parts of the construction remain as named public theorem holes:

- `WeilConjectures.coherentQuotientReductionComparison`, node
  `lem-trf-coherent-quotient-reduction-comparison`, in its own new module.
  This has no scheme map, no supplied Roos model and no completed pullback;
  it identifies a quotient presentation in the system derived category itself.
- `WeilConjectures.ordinaryQuotientPullbackTowerComparison`, node
  `lem-trf-ordinary-quotient-pullback-tower-comparison`, in its own new module.
  This has no derived calculus, localization or total limit: it is an ordinary
  strict-tower comparison natural on all complexes, with its section formula.

The draft has zero textual holes in the item and adds two lower theorem holes.
This is a definition repair and a one-to-two decomposition with a naturality/descent
assembly, not a net reduction in the sorry ledger. The main hole is closed for the
corrected interface; two named lower holes are added. No axiom, proof-free data
choice or hollow definition is added.

## No longer needed

No original import is removed: the item's original public definition import is
still required. No module is withdrawn and no adopted-source declaration is
removed. The main proof now has only the two strict substeps, the existing
operation-descent theorem and the realization interface as its direct proof
inputs. It does not invoke the original twenty-two-dependency monolithic plan.
The following nodes and their modules are no longer direct proof dependencies of
this item (some remain necessary for the canonical quotient construction or
other consumers, so this is not a claim that all can be globally deleted):

- `lem-pc-kflat-resolution` (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`).
- `lem-pur-kflat-change-of-rings-independent` (`Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`).
- `lem-coef-derived-system-evaluation-calculus` (`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`).
- `def-pur-site-sheaf-tensor-presentation-data` (`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`).
- `def-weil-l-adic-coefficient-extension` (`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`).
- `prop-weil-pbc-proetale-constant-exact` (`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`).
- `lem-coef-semilinear-derived-sections` (`Sheaf.Paper.SemilinearDerivedSections`).
- `def-pur-integral-derived-operations` (`Sheaf.Paper.IntegralDerivedOperationsOnSlices`).
- `lem-weil-proetale-countable-products-exact` (`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`).
- `lem-weil-strict-roos-comparison` (`Sheaf.CategoryTheory.StrictRoosComparison`).
- `def-weil-integral-scalar-extension` (`Sheaf.Paper.IntegralScalarExtensionUniverses`).
- `def-pur-sheaf-tensor-product` (`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`).
- `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` (`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`).
- `def-weil-pbc-system-scalar-coherence` (`Sheaf.CategoryTheory.SystemScalarCoherence`).
- `def-trf-integral-scalar-tower-functors` (`Sheaf.Paper.IntegralScalarExtensionWellDefined`).
- `lem-pur-derived-change-of-rings` (`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`).
- `lem-pur-flat-single-derived-normalization` (`Sheaf.Algebra.Homology.FlatSingleDerivedNormalization`).
- `lem-pur-kflat-tensor-quasiiso-independent` (`Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`).
- `lem-weil-pbc-ringed-topos-kflat-pullback` (`Sheaf.Paper.KFlatRingedToposPullback`).
- `lem-pur-flat-roos-functor-descent` (`Sheaf.CategoryTheory.FlatRoosFunctorDescent`).

Reviewer correction: `def-trf-integral-comparison-sequence-systems` and
`def-coef-ringed-sequence-site` remain direct proof dependencies (the proof uses
`integralComparisonSequencePullback`, its derived version, `coefficientSequenceRestriction`
and `coefficientSequenceLimit`); they were added back to the item node's `proof_deps`.

The existing unit route is retained: the supplied Roos comparison and the actual
integral pullback on good complexes remain the comparisons used by the proof.
Only their quotient-system construction is separated into independent parts.

## Where the brief, the DAG or earlier work was wrong

The old universal normalization was false. `CoefficientReductionPresentation`
only pins e after finite derived evaluation. A nontrivial automorphism invisible
at every finite level can twist e while leaving C and kappa unchanged; its total
derived limit need not be trivial. The strict generator formula fixes q, so the
two universal normalization equations would contradict each other. See the exact
nonclosed-image example in the change record and prior T6 report. This is a
mathematical counterexample for review, not a Lean-certified counterexample.

The missing hypothesis concerns the comparison data, not the complex: e must
be the derived adjunction comparison of the strict quotient presentation. The
new predicate expresses this in the entire tower category. Its two Hom
bijections pin e uniquely. The ordinary tensor-derived presentation satisfies it
by the derived Hom formula, including for zero objects and exponent one. Thus
canonical presentations still normalize every flat-term K-flat input. No
completeness, boundedness or extra geometric assumption is imposed on inputs.

The parent remains marked STATEMENT-DISPUTED because its scalar conjunct and
separate completion-presentation normalizations have the analogous pre-existing
problem. They are not used by this proof and are not repaired by this delivery.
The new lemmas do not assume finite derived evaluation is faithful. The original
DAG prose was a single monolithic step; the new node proof records the actual
strict comparison, descent, and cancellation steps instead.

## New nodes

`lem-trf-coherent-quotient-reduction-comparison`, module
`Sheaf.Paper.CoherentQuotientReductionComparison`, isolates ordinary/derived
quotient-model construction and coherent presentation comparison. Its docstring
and node give the ordinary tensor adjunction, derived transport, strict quotient
isomorphism and entire-system transpose proof. Its construction can start from
the existing canonical completion models and transport to the supplied calculus.

`lem-trf-ordinary-quotient-pullback-tower-comparison`, module
`Sheaf.Paper.OrdinaryQuotientPullbackTowerComparison`, isolates the ordinary
finite inverse-image comparison, strict transition naturality and tensor-unit
section equation. It is independent of the first lemma once M is supplied.
Neither lemma restates model existence under another name.

The existing definition node records the coherence predicate and its statement
correction; no duplicate definition node is introduced. Change record:
`coord/changes/S9-pullback-presentation-coherence.md`.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
