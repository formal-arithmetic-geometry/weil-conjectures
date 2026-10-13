## What changed

Proved `AlgebraicGeometry.exists_tensor_model_algebra_stage` with its signature and
visibility unchanged. Added proof-only imports of
`Sheaf.RingTheory.TensorModelComparisonDiagram` and
`Sheaf.RingTheory.FilteredPushoutBijectiveStage`.

Added the fully proved assembly theorem
`AlgebraicGeometry.exists_tensor_model_comparison_diagram` in a new module. Its
private helpers prove finite presentation of a tensor map and assemble the
comparison system for the chosen colimit. The public theorem transports the
specified cocone to that chosen colimit using its unique cocone-point isomorphism,
then transports the right-factor identity back. It uses the existing declarations
in `ComparisonMapFiniteStage`, `ComparisonTensorCocones`, and
`DirectedTensorCoconesColimit`, with finite-presentation facts from Mathlib.

The target applies the existing eventual-bijectivity theorem to this coherent
system, conjugates the bijective component by the stage equivalences, defines its
right restriction as qk, proves the P-Q-Bk scalar tower by tensor balancing, and
transports the canonical tensor pushout along the resulting Ak-algebra equivalence.
Updated both DAG records to describe these proofs.

Both modules compiled together without errors or warnings through lcompile.py.
The proofs follow Stacks Tag 02JO (proof of (3), construction of Ψ) and Tag 05N9,
read online at https://stacks.math.columbia.edu/tag/02JO and
https://stacks.math.columbia.edu/tag/05N9 on 2026-10-13.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_tensor_model_algebra_stage`
(node `lem-pc-tensor-model-algebra-stage`).

Also proved the new assembly theorem
`AlgebraicGeometry.exists_tensor_model_comparison_diagram`
(node `lem-pc-tensor-model-comparison-diagram`) and both private helpers.
No sorry remains in either delivered module. No holes were added or split off.
The proof uses existing dependency declarations, whose outstanding proofs remain
with their own nodes; this delivery does not claim that the entire import closure
is axiom-free.

## No longer needed

No existing import was removed: all three public imports of the target support
its unchanged signature or its pushout proof.

The old direct dependency `lem-weil-pbc-colimit-category-fp-algebras`, module
`Sheaf.RingTheory.ColimitCategoryFpAlgebras`, is no longer needed on this route.
Its proposed descent of the inverse and two identities is replaced by the generic
filtered-pushout bijectivity theorem, which uses Mathlib's finite-presentation
factorization and eventual-equality results. This is an edge removed from this
proof, not a claim that the module is unreached from all project targets.

The other four old direct edges are now represented below the assembly node:
`lem-weil-pbc-directed-colimit-base-change-elementwise` through
`DirectedTensorCoconesColimit`,
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit` through
`ComparisonMapFiniteStage`, and
`lem-weil-pbc-finite-presentation-base-change-composition` and
`lem-weil-pbc-finite-presentation-over-finite-type-algebra` through the explicit
Mathlib finite-presentation argument. These four edges were removed from the
item's direct `proof_deps`; their mathematical work remains in the route.

`FinitePresentationModelStage` and `FinitePresentationComparisonSystem` are not
imported by this delivery. Their shorter result interface drops the right-factor
limit identity that this target requires; the proof instead assembles the
comparison system from declarations that retain its canonical cocone legs.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation was needed. The original DAG's
argument is mathematically sound. Its inverse-descent step is implemented through
the existing generic filtered-pushout bijectivity theorem, keeping the construction
and unit route. The chosen-colimit interfaces require an explicit transport from
the target's arbitrary colimit cocone; setting a HasColimit instance alone does
not make its chosen point definitionally equal to the prescribed cocone point.

The generic comparison-system and filtered-pushout declarations are tools from
`sk-thm-p1`, used within the tensor-model argument; they do not replace the
semicontinuity unit's proof route. The new node inherits the target's unit and
chapter. Edge cases checked in the construction: the tail contains its starting
index, common upper bounds stay in it, no injectivity or nontriviality assumption
is introduced, and scalar compatibility follows from tensor balancing, including
zero rings and empty presentations.

## New nodes

`lem-pc-tensor-model-comparison-diagram`, module
`Sheaf.RingTheory.TensorModelComparisonDiagram`: a proved assembly theorem giving
coherent finitely presented comparison maps and their two colimit cocones, together
with left-inclusion and right-factor compatibility. It asserts bijectivity only
of the colimit comparison, not any finite-stage component. The target still must
prove eventual bijectivity and the algebra pushout using these data. Its node
records the source, actual searches (LeanSearch unavailable), construction steps,
and verbatim Lean signature. No change record is needed: no existing signature,
definition, visibility, or public import changed.

## Second reading by D3

1. Compared both delivered modules with the repository versions. The target theorem
signature is byte-for-byte unchanged; the new comparison theorem is a separate node.
No target hypothesis was added, removed, or weakened.
2. Compiled both modules together with `lcompile.py --all`; compilation is clean and
there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
constructs in the delivered sources. Axiom probes show only inherited `sorryAx` from
open imported declarations, together with the permitted standard axioms.
3. Checked the new node against its Lean declaration and its source proof. The
comparison theorem is strictly an intermediate assembly result: it does not assert
an invertible finite-stage component. Its hypotheses and both cocone compatibility
clauses match the declaration exactly. Searches found no existing declaration with
this statement.
4. Read the proofs top-down. The target uses the comparison assembly, the existing
filtered-pushout eventual-bijectivity theorem, and explicit tensor balancing and
pushout transport. The comparison module uses the existing finite-stage comparison,
tensor cocone, directed tensor colimit, and finite-presentation declarations. The
directed upper-tail route and the unit's realized route are preserved; edge cases
include zero rings and empty presentations.
5. Verified DAG proof/proof_deps/proof_origin fields against the actual imports and
proof calls. The removed old colimit-category dependency is recorded under
`## No longer needed`; no additional pruning was found.

I added this review and made the report enumerate all five old direct dependency
edges explicitly. No Lean proof or statement required repair.
