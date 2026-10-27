## What changed

The public statement and three public imports of
`Sheaf.SixFunctors.ProEtale.InternalKoszulFiniteAcyclicity` are unchanged.
Its proof now uses the already proved finite-level K-flat cone augmentation in
`Sheaf.Paper.CompletionTriangleComparison`, accessed through a proof-only
`import all`. A private proved `map_cone_hom_ext` maps the cone identity
decomposition through any additive functor. The supplied map is identified with
the mapped cone augmentation on both cone summands: `hu` fixes the unshifted
summand, and `hz` at `(q+1,-1)` kills the shifted summand. Exact transport preserves
the augmentation's quasi-isomorphism, and cancellation of the source chain
isomorphism finishes the argument.

The proof-only import `InternalKoszulConeCoordinates` contains the remaining
finite algebraic comparison. Its hypotheses include neither K-flatness nor a
quotient target or augmentation. Its conclusion is a chain isomorphism with two
inclusion formulas. This leaves the chain-coordinate computation to be proved,
while removing all homology, K-flat replacement, quotient augmentation, and
uniqueness arguments from the remaining obligation. It is strictly a source
comparison, not the original quasi-isomorphism statement under another name.

The original DAG proof is updated to the actual cone argument. The new node's
proof records the local associated-uniformizer argument and finite dual tensor
coordinates. Zero complexes, unit choices of generator, and the empty scheme
have the same formulas. No existing statement, definition, target or consumer
changes. No source-library module is edited.

## Proved and sorry left

Closed the existing body hole of
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_finite_augmentation_quasiIso`
(node `lem-sfb-internal-koszul-finite-acyclicity`), by a complete Lean proof from
the coordinate comparison and the existing proved cone augmentation.
There are zero holes left in the item module.

Added exactly one named theorem hole:
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_uniformizer_cone_coordinates`
(node `lem-sfb-internal-koszul-cone-coordinates`), in the new module
`Sheaf.SixFunctors.ProEtale.InternalKoszulConeCoordinates`.
Its entire body is `:= by sorry`; its docstring gives the source and full proof
in words. No definition or private declaration contains a hole. Both files have compiled:
the coordinate statement in the sandbox import-order compile and the complete
augmentation proof in a profiled single-file compile (24.5 seconds). The final
packet removes the temporary profiling settings and fixes its sole long line;
the delivery tool verifies that version again.

Thus one old hole is closed and one strictly smaller hole is added. This is a
decomposition, with net hole reduction zero, rather than a completed proof of
the mathematical obligation.

## No longer needed

No original import is removed: all three public imports are used by the original
statement. No module is withdrawn.

The parent proof no longer uses
`lem-weil-pbc-regular-sequence-koszul-regular`
(`WeilConjectures.RingTheory.RegularSequenceKoszulRegular`): the existing proved
K-flat cone augmentation replaces a new regular-sequence resolution proof.
The direct parent dependencies
`det-prop-integral-criterion-constant-coefficients`,
`def-sfb-integral-constant-model-realization`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`def-weil-pbc-ringed-ideal-generators`,
`def-weil-pbc-ringed-koszul-system`, and
`def-sfb-internal-completion-section-transport`
are removed from its proof-dependency list. Some remain statement dependencies
or occur in the new coordinate node or the existing coefficient construction;
this is not a claim that their modules are globally unused.

No finite tower transitions, Roos compatibility or inverse-limit calculation
is required by this proof or the new comparison.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but unnecessarily reproves the
finite K-flat cone-to-quotient augmentation already established by the private
`CoefficientCone.coneToTensor_quasiIso` helper. Its arbitrary-K-flat case uses
a K-flat replacement and cone naturality, so no termwise-flat hypothesis is
needed here. The canonical principal reduction data and completion-triangle
module are used as existing tools; they do not replace the blueprint unit's
route, whose Reduction paragraph already uses this same uniformizer cone.

Searches through leanfinder, leansearch, loogle and grep found generic cone and
total-tensor APIs, but no identification of the exact singleton dual tensor
with this transported uniformizer cone. Searches of the imported blueprint
found no separate statement of the new comparison. The finite signed Koszul
coordinates, negative Koszul duality and strict scalar comparisons are relevant
existing pieces of its proof, but do not themselves state the displayed chain
isomorphism with both required inclusions.

## New nodes

`lem-sfb-internal-koszul-cone-coordinates`, in
`dag/nodes/sec-six-functors-basics/`, realizes the finite chain-coordinate
calculation in the Reduction paragraph of `det-thm-sf-pf-adic-open`. It retains
only the chain isomorphism of the uniformizer cone with the singleton dual
Koszul tensor, normalized on the unshifted summand and factoring the shifted
one. It has no quotient augmentation, acyclicity, K-flatness, transition or
inverse-limit conclusion. Its new module has exactly one public theorem.
The new node uses negative Koszul duality and strict scalar Koszul comparison
as generic finite-algebra tools, and the internal section tensor comparison as
an exact coefficient-transport tool. These black boxes supply precisely the
coordinate identifications that the blueprint Reduction requires; no alternative
unit route is substituted. Any required tool-use approvals are left to the
maintainer. No existing interface is repaired, so there is no change record.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
