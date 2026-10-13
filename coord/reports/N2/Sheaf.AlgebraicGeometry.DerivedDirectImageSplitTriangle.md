## What changed

Proved `AlgebraicGeometry.RingedSpace.derivedModuleDirectImage_termwise_split_ses_triangle`
in `Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle`, with its existing signature,
visibility, definitions and public imports unchanged. Added only proved private helpers:
`directImageComparison`, `directImageComparison_app`,
`directImageComparison_naturality`, and `directImage_boundary`.

The comparison is the right-derived unit transported through the homotopy quotient and
localization isomorphisms. Its inverse on K-injectives is the existing comparison iso.
The boundary proof uses the canonical mapping cone, naturality of this comparison at
`descShortComplex` and the cone's third map, and cancellation after localization.
It does not assume the cone is K-injective. Degreewise splittings are mapped directly,
then used to prove image short exactness. `Triangle.isoMk` and
`triangleOfSES_distinguished` finish the triangle and distinguishedness clauses.
Updated the item's node proof, proof dependencies and proof origin to this route.

Searches actually run: LeanFinder for additive preservation of the connecting morphism
returned `CochainComplex.mappingCone.map_δ` and `ShortComplex.Splitting.map`;
Loogle for `ShortComplex.Splitting.map` returned an unknown-identifier message;
grep for `triangleOfSES|homOfDegreewiseSplit` found the cone/SES APIs. Read their pinned
Mathlib source signatures and proofs. The local Stacks source file named by the node
is absent on this machine; read the primary-source pages
https://stacks.math.columbia.edu/tag/0152 and https://stacks.math.columbia.edu/tag/079V.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.RingedSpace.derivedModuleDirectImage_termwise_split_ses_triangle`
(node `lem-pc-derived-functor-termwise-split-ses-triangle`).
No holes added, no split-off statements, and no `sorry` remains in the delivered module.
This is a proof, not a decomposition. Existing imported resolution theory is unchanged.

## No longer needed

The proof no longer needs nodes
`lem-weil-pbc-degreewise-split-connecting-morphism` and
`lem-weil-pbc-degreewise-split-derived-triangle`.
They are Mathlib leaves, so no corresponding project statement module is removed.
Their explicit `pi d s` construction and distinguished split-triangle argument are
bypassed by the canonical cone calculation. No import was removed: the two original
public imports are needed by the existing declarations and statements. No new import
was necessary because their transitive Mathlib imports already provide the cone APIs.
The remaining node dependencies are the ringed-space derived direct image,
K-injectivity, the canonical SES triangle, and triangulated isomorphism closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature defect was found. The DAG's planned splitting-formula
route is unnecessary: naturality of the unit on all complexes lets the proof use the
canonical cone directly. This changes only the node-level argument, and the unit's
statement and route remain untouched (its `realized` fields do not name this node).
No definition or public interface changed, and no forced adaptation was needed.

## Second reading by N2

1. Interface: PASS. Read the complete delivered module and diffed it against the
repository version. All three existing definitions are byte-for-byte unchanged;
the complete existing theorem signature, including universes, `hS`, degreewise
`Nonempty Splitting`, all three K-injective instances, and every conclusion, is
byte-for-byte unchanged. Imports and public visibility are unchanged. The only
Lean additions are four private helpers, scoped elaboration options, and the proof.
No change record or forced adaptation is needed.

2. Proof and trust: PASS. Compiled the delivered module with `lcompile.py` without
errors or warnings (36.1 seconds). Compiled a scratch copy with `#print axioms`
for all eight declarations, including the private helpers (40.1 seconds): each
uses only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The module contains no `sorry`, forbidden axiom or implementation override, or
hollow definition. `directImageComparison` is an explicit composite of the unit
and natural isomorphisms, defined on all complexes. The only chosen splittings
come from the theorem's supplied hypothesis, not an unproved existence theorem.

3. Split statements: PASS, vacuous. No holes or public statements were added.
Read each private helper's type and proof: comparison at K-injectives is the
inverse of the existing iso; naturality follows by iso cancellation; the boundary
helper assumes exactly image short exactness, not K-injectivity of the cone.
The zero sequence and chainwise split sequences cause no exceptional cases:
the image splitting is mapped directly, and cone quasi-isomorphism cancellation
uses short exactness alone. No degenerate object or degree is excluded.

4. Shortest route and pruning: PASS. Independently searched LeanFinder for
naturality of a right-derived unit and mapping-cone boundary compatibility;
Loogle for `CategoryTheory.NatTrans.naturality`; and project source with `rg` for
comparison and cone-boundary declarations. Read the pinned Mathlib proofs of
`mappingCone.map_δ`, `mapHomologicalComplexIso_hom_descShortComplex`,
`descShortComplex_triangleOfSESδ`, and `triangleOfSES_distinguished`.
Mathlib's `DerivedCategory.map_triangleOfSESδ` requires an exact functor on
objects, which general module direct image is not, so it cannot replace this
argument. The upstream `rightDerivedFunctorObjQIso` has no boundary naturality
lemma. Both public imports are needed in existing signatures/definitions:
ringed-space direct image and canonical SES connecting maps/triangles.
The two omitted old proof dependencies are exactly the two nodes listed above;
both are Mathlib leaves, so no project module is pruned. Read the unit record
`sk-thm-picard-semicon`: its `realized` statement and step arrays are empty and
neither names this item or either bypassed node. Its route is unchanged.

5. DAG correspondence: PASS. The node diff changes only `proof`, `proof_deps`,
and `proof_origin`. Its four steps follow the actual proof: mapped splittings;
unit naturality; cone boundary comparison with invertible `Q(F.map d)`; and
`Triangle.isoMk` followed by isomorphism closure of distinguished triangles.
The statement and Lean record are unchanged. The union of step uses equals
`proof_deps`, and the agent origin accurately identifies the new calculation.

Changes by the second reader: added this review and independent validation
record only; no Lean or node repair was necessary. The preserved original
theorem docstring describes the older splitting-formula route; the actual cone
route is documented in the node and this report. No holes added or split off:
one original hole closed, one of one, and zero project modules pruned.
