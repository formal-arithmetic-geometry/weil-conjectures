## What changed

Prove `WeilConjectures.weilScalarAssociator_exists` from the scalar/automorphism
compatibility square. A private categorical lemma constructs each component with
`Endofunctor.Algebra.isoMk` and `ObjectProperty.isoMk`. The square and naturality
of the coefficient associator prove the commuting equation for the Weil structure
arrow. Underlying naturality gives a natural isomorphism; equality of underlying
components proves uniqueness. All existing public signatures and definitions stay
unchanged. The noetherian instance and coefficient-hypotheses theorem now reuse a proved
private noetherian helper, removing their duplicate construction; the other five
previously completed proofs stay unchanged.

Add `Sheaf.Paper.PbcRationalAutomorphismScalarCoherence` as a private proof import.
Its statement is the rational coefficient square required in the parent's original
step 4. It assumes no Weil object, structure map, natural isomorphism on Weil
categories, or uniqueness property. It is strictly a part of the original argument.
Its docstring and node give the ordinary mates argument, derived/integral restriction,
and conjugation by rationalization comparisons in detail.

Validation: the final item compiled successfully in 27.2 seconds through `lcompile.py`;
the new statement module also compiled. The import-direction check permits the new
proof import, and all Lean lines meet the 100-character limit.

## Proved and sorry left

Closed: `WeilConjectures.weilScalarAssociator_exists` (1 of 1 item holes).
Remaining in the item: none (0).
Added: `AlgebraicGeometry.Scheme.pbcIsoRationalScalarComparison_comp` (1 hole),
node `lem-sf-pbc-rational-automorphism-coherence`.
This is a decomposition, not a complete axiom-free proof: one upper hole is replaced
by one strictly lower compatibility obligation.

The new lemma includes repeated coefficient fields. Identity automorphisms give the
scalar associator square; zero objects give the zero-arrow equation. Its hypotheses
are the same coefficient-stage hypotheses needed to state the existing comparisons.
It chooses no data from an unproved mere existence theorem.

## No longer needed

None of the existing imports, nodes, modules or declarations is removed. All six
existing parent proof dependencies remain used. No unit route changes: the unit
`sk-rem-sf-pf-done` has no realized entries.

The unsuccessful local ambient-square split was never delivered and is absent from
this packet. The single rational square includes its ordinary/derived compatibility
argument, rather than leaving an additional ambient hole.

## Where the brief, the DAG or earlier work was wrong

The existing declarations provide the scalar associator and individual normalized
scalar/automorphism comparisons, but none states their joint composition equation.
The parent's old step 4 already identified this missing square. The delivery states
that step explicitly and completes the Weil lifting construction from it.

I attempted the rational descent by a proved generic functor-diagram cancellation
argument and a proved integral restriction argument. Concrete normalization matching
expanded the scalar-localization Hom module structures and exceeded the compile-time
limit. Profiling and local irreducibility annotations for the large coefficient and
linear/category structures did not resolve it. The delivered split records the
whole genuine compatibility step, with the conjugation/cancellation proof in words;
it does not change a definition or raise the compile-time limit.
For the delivered lift, profiling identified kernel comparison of the expanded Weil
wrappers as the bottleneck. Applying the lifting lemma to the explicit coefficient
comparisons reduced the final item compile to 27.2 seconds.

The parent's source path names `def-wf-weil-category.md`, absent from the current
blueprint snapshot. The current blueprint's
`sec-six-functors-basics/sk-def-sf-admissible/def-weil-weil-sheaf-complex.proof.md`,
paragraph "Extension of scalars", records the canonical inverse-image/scalar
comparison. The original parent DAG statement and all Lean signatures are preserved.
This delivery does not identify the raw PBC model with the newer condensed model.

Searches used LeanFinder, Loogle, LeanSearch, Mathlib source, both library roots,
DAG nodes and the current blueprint. Mathlib `Endofunctor.Algebra.isoMk` supplies
the categorical lift. Generic mates laws do not directly state the normalized
PBC comparison square. No duplicate statement was found.

## New nodes

`lem-sf-pbc-rational-automorphism-coherence`, attached to
`Sheaf.Paper.PbcRationalAutomorphismScalarCoherence` and its sole theorem.
Only the parent node's proof, proof dependencies and proof origin change.
No change record is needed: existing statements, definitions, attributes,
instances and public imports are unchanged. New helpers are private and proved. Local irreducibility annotations keep the large
coefficient linear and localization structures folded during proof elaboration.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
