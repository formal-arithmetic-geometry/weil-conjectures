## What changed

Replaced the sole sorry in
Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback with a complete Lean Ext
calculation. The declaration and its visibility are unchanged. Added a proof-only import of
Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafUnitPullback and its new statement module.
The original public import and exact-functor comparison import remain necessary.

The calculation expands both cohomology maps, moves precomposition through exact
inverse image, uses the generator equality, and applies exactFunctorCompositionComparison
for the two factorizations of the open pullback square. Precomposition and postcomposition
with inverse comparison components cancel the comparison isomorphisms. Ext associativity
then produces precisely the coefficient transport in openCohomologyPullback.

The remaining generator equality is isolated as a morphism equality with only g and W.
It has no arbitrary coefficient sheaf, degree, Ext class, resolution or cocycle, and is
strictly the second step of the original plan. Updated the parent node's proof and
proof_deps to match the calculation and added the generator node. No existing definition,
statement, signature or visibility changed, and no forced adaptations were needed.

Both sandbox modules compile through lcompile.py in dependency order. Equal opens,
the empty open, identity g and degree zero impose no extra assumptions: the generator
statement uses the same terminal-object adjunctions in these cases, and the Ext calculation
uses zero_add/add_zero without any positive-degree assumption.

## Proved and sorry left

Closed original hole:
AlgebraicGeometry.Etale.etaleOpenObjectCohomologyMap_pullback
(node lem-weil-pbc-etale-open-object-cohomology-pullback).
There are no sorries left in the assigned module.

Added hole:
AlgebraicGeometry.Etale.etaleOpenFreeSheafUnit_pullback
(node lem-weil-pbc-etale-open-free-sheaf-unit-pullback), in its own new module.
Its proof is exactly by sorry, with source and complete natural-language argument.

This is a decomposition: one original hole closed and one strictly smaller hole added,
net zero. The arbitrary-degree Ext calculation is proved; the concrete degree-zero
identity-generator compatibility remains to be formalized.

## No longer needed

None. No original import or transitive module is pruned. The parent's direct use of
EtaleOpenCohomologyComparison is moved to the generator node, where its sectionsEquiv
construction is still needed. The free-sheaf pullback definition is still used in the
statement and in the remaining generator lemma. Every original unit realization remains;
the decomposition stays below the unit level and preserves the original two-step route.

## Where the brief, the DAG or earlier work was wrong

The missing EtaleOpenFreeSheafPullback compiled dependency reported by the three earlier
attempts is now available. The unchanged module compiled before proof edits. The earlier
scratch Ext calculation needed additional degree-zero composition splitting and a
precompose/postcompose cancellation argument for the first comparison; these are now
written and checked in Lean.

Stacks Tag 03F3 supplies localization of cohomology. Tags 01F8/01FB concern derived
functoriality on ringed spaces; they do not state the concrete identity-generator equality.
The new node explicitly labels its proof as an agent-written calculation using the
library's ConstantSectionAdjunctPullback and OpenRestrictionPullbackUnit statements.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, pinned Mathlib
source searches and the whole blueprint search found no existing concrete generator
pullback statement. Nested-open generator coherence is already proved, but does not
cover a general scheme morphism g.

## New nodes

lem-weil-pbc-etale-open-free-sheaf-unit-pullback, in
 dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-open-free-sheaf-unit-pullback.json,
states precisely the identity-generator morphism equality used by the Ext calculation.
Its module is Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafUnitPullback. The node records the
constant-sheaf and free-abelian Yoneda adjunction calculation and the open restriction
unit compatibility, its inherited chapter/unit/blueprint ancestry, and all three search
kinds. There are no change records because all existing interfaces are unchanged.

## Second reading by H4

1. I compared the delivered `EtaleOpenObjectCohomologyPullback.lean` with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof body and a proof-only import were added. The new unit-pullback declaration is isolated in its own module and does not alter an existing interface.

2. I compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The assigned theorem has no `sorry`, axioms, unsafe declarations, or hollow definitions. The split-off unit theorem is the sole intentional `sorry`, and its source, proof sketch, and node are present.

3. The Ext calculation proves the target by expanding both maps, applying the exact-functor composition comparison, and cancelling inverse comparison components. The remaining generator compatibility is a strictly smaller morphism equality with no coefficient, degree, Ext class, resolution, or cocycle. Its statement is true in edge cases including empty opens, identity maps, and degree zero.

4. The delivered DAG proof and `proof_deps` match the declarations and imports used by the Lean proof. The new node records its source, route, searches, unit and chapter ancestry, and Lean declaration. No existing proof dependency or import became unused, so no pruning is claimed.

5. The unit route is preserved: the parent proof still uses the exact-functor comparison step, while the generator step is represented by the new node and imported theorem. No target statement or definition was changed, and no additional adaptation or change record is required.

I changed only this report section after the first preflight; no Lean code or DAG content was altered during second reading.
