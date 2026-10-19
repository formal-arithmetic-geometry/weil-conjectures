## What changed

Completed the Lean proof of
`AlgebraicGeometry.ProEtale.normalizedEtaleOriginWitnesses` without changing its statement
or `NormalizedOriginCompatibility`. The proof constructs the normalization comparison,
reflects lower cohomological bounds through the two exact faithful functors, lifts the
comparison isomorphism and its inverse using the existing comparison Hom bijection, and
proves compatibility and uniqueness. It descends the scalar unit and quotient cocycle by
naturality, cancellation and comparison Hom injectivity.

Added and fully proved `Sheaf.Paper.NormalizedOriginComparisonCoherence` for the
unit/composition part of the canonical scalar comparison. Its private lemmas prove ordinary
restriction coherence by conjugation, transport the diagrams using the existing exact
functor derived-category pasting theorems, and transpose them using mates. The generic
`mateComp` lemma follows from Mathlib's mates-pasting and conjugation identities. The unit
calculation is proved separately through `mateUnit`; no K-flat calculation or quotient
flatness is needed. All private helpers and the public coherence theorem are proved.

Moved the five scalar definitions `normalizedOriginRestrictionUnit`,
`normalizedOriginScalarUnit`, `normalizedOriginQuotientUnit`,
`normalizedOriginQuotientComp` and `normalizedOriginReduction` verbatim into
`Sheaf.Paper.NormalizedOriginScalarComparisons`, publicly reexported by the original
module. This permits the coherence module to use them without a cycle. Names, binders,
universes, signatures, visibility and bodies remain identical. The definition node and
change record document the relocation; no consumer adaptation is included.

The proof uses the already proved upstream
`bijective_comparisonUpperStar_mapDerivedCategory_map`, and the existing exact-functor
cohomology reflection theorem. The proof-only import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison` gives the Hom
bijection directly. Source and Mathlib searches were performed before this route was chosen.

All three delivery modules compile cleanly together through lcompile after the coherence
proof was finished: scalar support 0.1 seconds, coherence 11.8 seconds, assigned module
4.8 seconds. No compilation timeout occurred. On resumption, lcompile --all confirmed all three
modules compile cleanly against the current server library; their retained compiled
artifacts were accepted in 0.1, 0.1 and 1.0 seconds respectively. All five direct
consumers also compiled unchanged against them: `Sheaf.Paper.AdicSmoothBaseChange`,
`Sheaf.Paper.FiniteCoefficientAdjointComparisons`, `Sheaf.Paper.PreservationConstructible`,
`Sheaf.SixFunctors.FiniteDualizing`, and `Sheaf.SixFunctors.GeoCartierCoeffExtension`.
Those consumer copies were removed from the delivery after checking. The current required
`tools/downstream.py --uses` scan found 188 transitive importers and five downstream
scalar-unit users, including the newly landed `FiniteExceptionalSystemAdjunction`. Byte-for-byte checks confirm the five relocated definition bodies are identical
to the current source and both existing declaration signatures are unchanged. The largest of
these file compilations took 36.8 seconds. There are no target edits or hollow definitions.

## Proved and sorry left

Original hole closed in the assigned module:
`AlgebraicGeometry.ProEtale.normalizedEtaleOriginWitnesses`
(node `lem-weil-pbc-normalized-etale-origin-witnesses`). The assigned module now has
zero holes. The private helpers `plus_of_map`, `normalizedOrigin_bounded`, and
`normalizationLift` are fully proved; the private normalization isomorphism is constructed
by composing the three specified isomorphisms. The final unit and cocycle deductions
are complete Lean proofs from the coherence statement.

The new public theorem
`AlgebraicGeometry.ProEtale.normalizedOriginComparisonCoherence`
(node `lem-weil-pbc-normalized-origin-comparison-coherence`) is also completely proved.
Its private helpers `mateComp`, `mateUnit`, `ordinaryRestrictionUnit`,
`derivedRestrictionUnit`, `comparisonScalarUnit`, `ordinaryRestrictionComp`,
`derivedRestrictionComp`, and `comparisonScalarComp` have no holes. The scalar support
module contains only the five existing explicit definitions and has zero holes.

The resumed required dry run passed compilation and preflight. The axiom probe for
`NormalizedOriginComparisonCoherence` received no compile-server answer within 201 seconds;
deliver3 reported that the merge reruns this probe. No axiom finding was reported.

Holes closed: 1, namely `AlgebraicGeometry.ProEtale.normalizedEtaleOriginWitnesses`.
Holes added: 0. Holes remaining in the three delivered modules: 0. No split-off theorem
is left unfinished. This is a proof from existing library declarations; pre-existing
holes in imported modules are not claimed as closed. No new axiom is introduced.

## No longer needed

Removed the following public imports from the assigned module:
`Sheaf.Paper.AdicCoefficientDatum` (available through the scalar support module),
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`, and
`Sheaf.Paper.PbcActualScalarPullback`. The original scalar definitions still use the
same canonical witness/scalar interface through `WitnessCompatibility`; no construction
is replaced. The direct consumer compilations check the public-import removal.

Removed the unused proof imports
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` from the authoritative module
at inspection. The shorter proof accesses the upstream comparison Hom bijection directly.

The parent proof no longer separately realizes the K-flat calculations of
`lem-pur-derived-change-of-rings` or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; the canonical comparison is already
part of `def-weil-pbc-witness-compatibility`. Their statement references are retained
unchanged. These dependencies may remain needed transitively by that interface and
other targets; no global pruning of them is claimed. The obsolete parent `tool_uses`
entry for `lem-pur-derived-change-of-rings` is withdrawn. No module is deleted.
The unit's preservation-constructibility route is retained. The proof import of
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` is retained as required by
the unit route, despite using the upstream Hom bijection directly.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had read the authoritative server source when the local checkout
lacked the assigned module. The current local source is now present; its existing theorem
signature and the five moved scalar definition bodies were checked against the sandbox.
No statement was reconstructed from an outdated signature. The supplied previous failure
was a git checkout timeout before compilation, not evidence of a slow Lean definition.
The complete delivered files compile well below 60 seconds, so no definition-performance
change or consumer adaptation was necessary.

The original proof plan called for redoing K-flat comparison calculations in this module.
The supplied witness interface already has the canonical comparison mate and its
invertibility, and the source library already proves the needed comparison Hom bijection.
The specialized coherence of that specified mate with the specified scalar unit and
associator is now proved in the new coherence module, without duplicating scalar extension
or adding normalization hypotheses. The new node's proof uses ordinary
restriction/coextension and mate pasting; this avoids requiring flat quotient maps.

Edge cases checked in the statements and proof: n=0 is the first positive quotient;
repeated indices use the actual self-quotient map and its proved identity; the cocycle
includes all weak inequalities; zero quotient rings are permitted; and every boundedness
argument uses the supplied bound at the particular target level, never a common bound.
No statement is disputed. No held consumer was edited. The resumed preflight identified the newly landed
`FiniteExceptionalSystemAdjunction` scalar-unit user; it has been added to the change
record, with unchanged semantics through the same public reexport.

## New nodes

`def-weil-pbc-normalized-origin-scalar-comparisons` attaches the five existing scalar
comparison definitions to their support module. Their construction and meaning are
unchanged; its proof list is empty because it introduces only explicit definitions.

`lem-weil-pbc-normalized-origin-comparison-coherence` is the fully proved unit/associator
theorem for comparison and quotient scalar extension on ambient derived categories. Its
three proof steps are realized by the ordinary restriction calculations, existing exact
functor derived-category pasting, and generic mates composition. It introduces no hole.

Change record: `coord/changes/A8-normalized-origin-scalar-comparisons.md`.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
