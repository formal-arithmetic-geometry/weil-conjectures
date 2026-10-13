## What changed

Completed the existing sandbox reduction of
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_comp`, preserving its signature.
The proof applies injectivity of the scalar Ext equivalence, coefficient naturality,
exact-functor composition comparison, and Yoneda associativity to the normalized
unit and coefficient coherence identities. Its three additional imports are proof-only. The two instance helpers in the item
are private, so they do not add public declarations to its interface.

The new module `Sheaf.AlgebraicGeometry.ScalarInverseImageCompositionCoherence`
constructs `scalarInverseImageCompIso` concretely using `Adjunction.leftAdjointUniq`.
Its public coherence theorem isolates two degree-zero sheaf-morphism identities,
with a complete proof in words and a matching new node. Updated the item's node
proof, proof dependencies and proof origin to describe the actual argument.
No existing signature, definition or visibility changed; no other modules were adapted.
The cube unit and its realized steps are unchanged.

The earlier sandbox also added coefficient naturality as a new postponed statement.
That identical declaration and node now exist in the repository, and the declaration
has been proved by S3 following M1's statement delivery. Removed both duplicate
sandbox files and their compiled artifacts. The proof now imports the existing theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_comp`
(node `lem-sc-scalar-cohomology-pullback-composition`). No sorry remains in the item.
This is a decomposition: one upper hole closed and one strictly smaller hole added,
so the net number of holes is unchanged.

The sole added hole is
`AlgebraicGeometry.Scheme.Modules.scalarInverseImageCompIso_coherence`
(node `lem-sc-scalar-inverse-image-composition-coherence`). It states two equations
of sheaf morphisms, without Ext, cohomology, or a degree parameter. Its proof is
exactly `:= by sorry`. The combining proof uses both equations and the existing
`scalarCohomologyExtEquiv_map` and `Abelian.Ext.exactFunctorCompositionComparison`.
Neither existing dependency theorem contains a direct sorry. Other pre-existing
holes in their dependencies are unchanged.

The morphism identities include empty schemes, zero coefficients and identity
arrows: they use adjunction-unit identities and extensionality, without cancellation
of sections or nonzero hypotheses. The coefficient naturality theorem includes
zero coefficient morphisms, and the Ext algebra includes degree zero.

## No longer needed

No original Lean import is removed: the sole public import defines the statement's
operations. No existing module is claimed to leave the targets' import closure.

Removed the planned proof dependency `lem-pc-module-pullback-identity-composition`
from this item's proof dependencies. Its unnormalized existence statements
`nonempty_tensorPullbackId` and `nonempty_tensorPullbackComp` are not applied.
The concrete normalized `scalarPullbackCompIso`, defined in the operations module,
is still used; `Sheaf.AlgebraicGeometry.TensorPullback` is not pruned from the closure.

Removed the duplicate sandbox coefficient-naturality module and node, using their
existing repository versions instead. This removes one proposed new hole, without
removing the necessary coefficient-naturality import.

## Where the brief, the DAG or earlier work was wrong

The original plan supplied tensor-pullback existence statements but did not state
the scalar coefficient/unit coherence or naturality needed for the Ext argument.
The previous sandbox provided a valid combining proof and separated both steps.
Coefficient naturality has since become an existing proved dependency; retaining
its sandbox version would overwrite that proof with a sorry and is unnecessary.
The earlier item also exposed two named local instance helpers; made those private
after the delivery check identified them as unnecessary public interface additions.

The earlier worker's recorded searches and source excerpts were retained in the
sandbox. Local searches of both library roots confirmed the existing naturality
proof and found no existing scalar inverse-image coherence theorem. The generic
Ext comparison theorem is already proved and supplies only the exact-functor
comparison step; it does not bypass a blueprint unit.

The new coherence node follows the existing scalar-square/Kunneth chain to the
cube theorem. The unit record `sk-prop-av-cube` has no realized node assignments,
and no unit statement or step is altered. Source normalization follows Stacks
Tags 008I (pullback composition) and 0097 (module pullback composition).
The old item's resolution-source reference to Tag 01FD is inaccurate: it is a
Cech refinement lemma; coefficient-resolution naturality is explained at Tag 01FB.

## New nodes

`lem-sc-scalar-inverse-image-composition-coherence`, module
`Sheaf.AlgebraicGeometry.ScalarInverseImageCompositionCoherence`, records the
concrete comparison of inverse-image left adjoints and its constant-unit and
coefficient identities. It is strictly the morphism-level part of the argument.
Its statement uses the existing normalized maps, its docstring explains the
sectionwise adjunction proof, and its source is Stacks Tags 008I and 0097.

No change records are required: all existing interfaces are unchanged.

## Second reading by S4

1. Compared the delivered item with the repository using diff and checked the existing
   theorem signature byte for byte. It is identical. Its original public import and
   declarations retain their visibility; the three new imports are proof-only. No
   existing definition or target statement changes, and no adaptation is delivered. Pass.
2. Compiled both modules in import order with lcompile.py. Reviewed every proof step:
   coefficient naturality exposes the Ext expression, exact-functor comparison transports
   the class, and both coherence equations finish it by Yoneda associativity. The sole
   new sorry is the reported public coherence theorem; the comparison is a concrete
   left-adjoint-uniqueness construction. No prohibited declaration or hollow definition
   occurs. Explicit axiom probes are recorded below.
3. Read the normalized inverse-image, constant-unit, coefficient and tensor-comparison
   definitions, including the coefficient map's sectionwise adjunction characterization.
   The remaining coherence equations follow from those unit normalizations; equality of
   all sections determines the coefficient adjoint uniquely. They have no Ext class or
   degree parameter and are strictly the sheaf-morphism part of the argument, rather
   than a renamed cohomology theorem. Empty schemes and zero coefficients introduce
   only unique zero maps; identity arrows satisfy the same adjunction unit equations.
   Independently searched with Loogle, LeanFinder and grep using different queries,
   and read the upstream constant-sheaf comparison. Found generic ingredients but no
   duplicate scalar composition theorem. Read the retained Stacks source proofs of
   pullback composition (Tags 008I and 0097). Pass as a decomposition, with one new hole.
4. All three proof imports are used explicitly. The original operations import is
   required by the signature. The report lists the only removed old proof dependency,
   lem-pc-module-pullback-identity-composition; its existence statements are not used.
   No module is claimed pruned from the target closure. Checked sk-prop-av-cube: its
   realized statement and step arrays are empty and unchanged. This generic functoriality
   argument does not replace any unit step. Pass.
5. Checked both DAG nodes against the Lean. The item's proof steps and dependency union
   match the naturality, exact-functor comparison and coherence applications. The new
   node has its source, complete proof plan, searches, creation and blueprint provenance,
   chapter/unit and verbatim Lean statement. Corrected stale proof-origin notes that
   referred to two residual theorems or to resolution work inside the morphism lemma. Pass.

Changes in the second reading: replaced the named compositionCoherenceMonoidal helper with local instance
registration of the existing Sheaf.monoidalCategory, corrected
the two proof-origin notes, added independent search evidence to the new node, and
recorded this review. No mathematical statement or proof body was changed. The
remaining coherence proof needs substantial adjunction/sectionwise elaboration and
was not closed in this reading. One original hole is filled and one lower hole is
added: this remains a decomposition with net zero holes closed.

Explicit scratch-copy #print axioms checks passed: scalarInverseImageCompIso uses
only propext, Classical.choice and Quot.sound. scalarInverseImageCompIso_coherence
and scalarCohomologyPullback_comp additionally use sorryAx, as expected from the
reported residual theorem and existing open dependencies; neither introduces any
other axiom. Both final modules compile without warnings or errors.
