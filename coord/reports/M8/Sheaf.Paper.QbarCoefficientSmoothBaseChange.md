## What changed

Closed both original holes in `Sheaf.Paper.QbarCoefficientSmoothBaseChange`,
retaining both theorem signatures verbatim and the original definitions of the
three stage operations, `Presentation.ambientExchange`, `Presentation.exchange`
and `Presentation.atStage`. No target statement changes.

`tensorModel_eq` identifies the completed coefficient map by its finite
projections and uniqueness, then uses naturality of the normalized finite
coefficient comparisons. The main proof assembles `Presentation` from the existing
`finiteStageRationalExchangeCoherence`, cancels inverse comparison maps in the raw
normalization equations, applies `eCoefficientSmoothBaseChange` to the admissible
finite-stage lattice, and transports its local isomorphism through the two identity
Karoubi projectors and the actual pair quotient. Naturality along the specified
representative isomorphism gives the component at the original object. The proved
pair-representative formula from `alpha.comm` gives the original `atStage` clause
at every overfield. The finite-E theorem gives admissible-lattice independence.

Added complete private helpers and the private proof imports
`Mathlib.Tactic.Choose` and `Sheaf.Paper.FiniteStageRationalExchangeCoherence`.
Four literal normalization propositions name the existing record proof clauses;
the records' data and proof obligations are unchanged. Disabled unused generated
size, injectivity and constructor-index auxiliaries for these records.

Included four support modules because the direct proof exposed expensive
coefficient-category normalization:

- `AmbientCompleteRawSystem`: the existing raw carrier becomes an ordinary
  definition, with explicit names for its original category and preadditive
  instances. Its body and all transition data remain definitionally identical.
- `StageSystemFunctorDescent`: match the input pair first, and use `Functor.copyObj`
  to retain the specified object function literally. Complete public equalities
  recover the old projection formula and chosen whole functor, including its maps.
- `AmbientCompleteCoefficientCategories`: keep the same two Karoubi transition
  bodies as ordinary definitions; adapt one private additivity proof by rewriting
  with the proved whole-functor equality. All original public coherence proofs
  and signatures are preserved.
- `FiniteStageRationalExchangeData`: name four existing composite/normalization
  propositions and use those names in the same existential clauses.

All four support modules were unclaimed when checked on 2026-10-22. The private
Ambient additivity adaptation is forced by the new copyObj normal form: the
original reports that `choose_spec` has the old witness's map formula rather than
the expected copyObj formula. Rewriting by `coefficientPairFunctor_eq_chosen`
restores the original uniqueness proof. The other modules' public signatures
are preserved; no adopted `WeilConjectures` file is changed.

Updated the five existing nodes' proof descriptions/attachments to match these
constructions and this proof route. No node is added or withdrawn. Definition
and target-meaning review is requested through these change records:

- `coord/changes/M8-qbar-normalization-definitions.md`
- `coord/changes/M8-ambient-stage-category-interface.md`
- `coord/changes/M8-coherent-descent-explicit-objects.md`
- `coord/changes/M8-ambient-transition-definitions.md`
- `coord/changes/M8-finite-stage-coherence-clause-definitions.md`

## Proved and sorry left

Original item holes: 2. Closed:

- `AlgebraicGeometry.Scheme.QbarCoefficientSmoothBaseChange.tensorModel_eq`.
- `AlgebraicGeometry.Scheme.qbarCoefficientSmoothBaseChange`.

Item holes left: 0. Holes added: 0. Split-off theorems: 0.
The other three support modules besides `AmbientCompleteRawSystem` have zero
holes. Its seven pre-existing holes, all attached to node
`def-sbc-ambient-complete-raw-scalar-system`, are retained unchanged:

- `AlgebraicGeometry.Scheme.pbcAmbientCompleteTensor_preserves`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteRaw_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteIntegralUnit_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteIntegralComparison_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteIntegralAssociator_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteRawAssociator_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteRaw_laws`.

No existing proved declaration is replaced by a hole. The main theorem uses the
already stated finite-stage coherence and finite-E base-change theorems. This is
a complete assembly from those declarations; their existing proof dependencies
retain their current proof status.

Validation: the complete five-file support/proof set compiles without warnings;
the item with its original `atStage` body compiled in 39.6 seconds. The eleven-file consumer run passed with all six unchanged downstream modules:
`FiniteStageKaroubiExtension` (3.4 s), `RationalRawOperationCoherence` (4.0 s),
`RationalRawSquareExchangeCoherence` (11.0 s), `RationalOperationCoherence` (8.8 s),
`RationalSquareExchangeCoherence` (37.9 s), and
`FiniteStageRationalExchangeCoherence` (7.3 s). The item passed again in the same
run (48.4 s), with no warnings. The final five-file packet also passed independently after removing the
redundant private import: descent 1.6 s, raw system 12.1 s, completed categories
32.6 s, coherence data 11.4 s, and the item 40.5 s; no errors or warnings.

## No longer needed

Removed the private import `Sheaf.Paper.IntrinsicQbarCategory`: this theorem uses
the published raw `pbcQbarCategory`, available from the retained public imports.
The temporary explicit proof import of `FiniteStageRationalExchangeData` is also
unnecessary: the retained private coherence import publicly supplies its interface.

This item's proof does not need node
`lem-sbc-common-stage-inverse-through-karoubi` or module
`Sheaf.CategoryTheory.CommonStageKaroubiInverse`. Its representative enters both
Karoubi envelopes through identity projectors. Mathlib's
`functorExtension₂CompWhiskeringLeftToKaroubiIso` and the existing
`StageSystem.Morphism.isIso_descNatTrans_app` give exactly the required local
inverse transport. Removed that node from this item's proof dependencies. No
arbitrary-projector inverse or constructible landing of direct images is used.
No module or node is withdrawn; other parents may still need that general lemma.
The unit route is preserved (`sk-rem-rest` has no separate realized steps).

All other stated mathematical dependencies and original public imports are
retained. No adopted source-library declaration or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The general common-stage inverse theorem is stronger than this item's actual
conclusion needs: the raw-Qbar representative has identity inner and outer
projectors. The existing Mathlib comparison and functorial preservation of local
isomorphisms suffice. The common-overfield admissibility premise is preserved
verbatim, although the chosen representative and unconditional scalar-exchange
compatibility already prove the stated conclusions.

The mathematical argument did not require weakening a statement or moving a
hole. Most implementation work was finding which eager carrier, category-instance
and object projections caused repeated expansion of scalar-localized derived
sheaf categories. The final repairs retain the same data and equations and keep
the original representative formula. No compile limit, launcher script, budget
metadata or adopted-source declaration is modified.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
