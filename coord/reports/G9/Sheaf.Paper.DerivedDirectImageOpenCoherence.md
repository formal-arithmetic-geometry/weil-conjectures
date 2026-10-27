## What changed

The parent theorem is reduced to the separate source arguments for associativity,
open-restriction normalization, successive restriction and mixed pasting. Its composition
normalization is proved directly from the universal right-derived comparison unit and
`rightDerivedFunctorNatTrans_app_Q_obj`. The proof combines those results for arbitrary
commutative condensed coefficients and specializes to the two prescribed coefficient rings.

The canonical maps and predicates move verbatim to
`Sheaf.Paper.DerivedDirectImageOpenCoherenceData`, publicly re-exported by the parent.
This permits the separate source statements to import the exact existing constructions.
Names, signatures, attributes, visibility and data bodies are unchanged. No source-library
file or target statement changes. The change record is
`coord/changes/G9-derived-open-coherence-data.md`.

## Proved and sorry left

This is a decomposition, not a completed proof: the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.derivedDirectImageOpenCoherence` is replaced
by four holes in the following declarations (namespace
`AlgebraicGeometry.ProEtale.CondensedRing`):

- `derivedDirectImageAssociativity`: node `lem-sfb-derived-direct-image-associativity`.
- `derivedOpenRestrictionNormalization`: node `lem-sfb-derived-open-restriction-normalization`.
- `derivedOpenRestrictionSuccessive`: node `lem-sfb-derived-open-restriction-successive`.
- `derivedOpenRestrictionMixed`: node `lem-sfb-derived-open-restriction-mixed`.

Holes closed: one original upper hole; holes added: four, net minus three.
The private `composition_normalized` proof has no holes. Each residual result is
strictly one argument of the conjunction, with the source proof in its docstring.
No definition has a hole. The compiled assembly has no placeholder proof steps.

## No longer needed

All original proof-only imports are removed from the parent. In particular,
`RingedToposDerivedPushforwardComposition` is replaced for the proved normalization
by the universal derived-composition identity. The internal-module equivalence,
ringed-site resolution, K-injective derived-map computation and pro-etale open-counit
modules are no longer direct imports of the assembly; their mathematics remains in
the proof plans of the residual source arguments through the word-model and
module-pasting dependencies. The redundant imports of right-derived composition,
module Basic, LowerShriek.Defs, UpperLowerStar.Defs and the duplicated finite-coefficient
UpperLowerStar.Defs are supplied by the retained statement imports.

No module is withdrawn and no dependency is claimed globally unused. The word-model
and module-pasting nodes remain needed by the residual arguments. The affine-space
unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The two existing dependencies prove word descent and underived pasting, but identifying
their cells with the actual canonical mate and compositor is additional glue. The
canonical mate formula was proved generically in experiments, but its specialization
and several word-cell comparisons trigger large definitional reductions in these
module categories. Both a direct formalism route and the word route were attempted
and compiled repeatedly. The delivered decomposition states the separate mathematical
arguments explicitly; it does not claim those experimental proofs compiled.

The definitions were interleaved with the theorem in the original module. Moving them
verbatim to a public interface is required for independently importing these source
arguments without a circular import. Existing consumers continue to receive the same
constants through the parent import.

## New nodes

`def-sfb-derived-direct-image-open-coherence-data` attaches the unchanged canonical
interface in its new module; it adds no hypothesis or mathematical claim.

`lem-sfb-derived-direct-image-associativity` records the corresponding separate source argument in `Sheaf.Paper.DerivedDirectImageAssociativity`. Its docstring gives the complete K-injective/degreewise-pasting proof and the node records the existing word-model and module-pasting inputs.

`lem-sfb-derived-open-restriction-normalization` records the corresponding separate source argument in `Sheaf.Paper.DerivedOpenRestrictionNormalization`. Its docstring gives the complete K-injective/degreewise-pasting proof and the node records the existing word-model and module-pasting inputs.

`lem-sfb-derived-open-restriction-successive` records the corresponding separate source argument in `Sheaf.Paper.DerivedOpenRestrictionSuccessive`. Its docstring gives the complete K-injective/degreewise-pasting proof and the node records the existing word-model and module-pasting inputs.

`lem-sfb-derived-open-restriction-mixed` records the corresponding separate source argument in `Sheaf.Paper.DerivedOpenRestrictionMixed`. Its docstring gives the complete K-injective/degreewise-pasting proof and the node records the existing word-model and module-pasting inputs.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
