## What changed

Proved `AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackSquare` with its
signature unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition`.
Two proved private helpers establish naturality of `canonicalSinglePullbackMap`
and compatibility with equality transport. The main proof applies pairwise
composition twice, cancels only composition isomorphisms, transports along the
square equality, and then applies naturality to the arbitrary module morphism.

Added one smaller public statement in its own module:
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition`.
It treats three schemes and two composable morphisms, without a square, a second
module, or an arbitrary module morphism. Its source and full remaining argument
are in its docstring and node. Updated the square node's proof and proof
dependencies to match the Lean reduction.

The square module compiled cleanly with `lcompile.py` in 34.8 seconds.
The composition module also compiled. No existing definitions, signatures,
visibility, or public imports were changed. No forced adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackSquare`
(node `lem-pc-canonical-single-pullback-square`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition`
(node `lem-pc-canonical-single-pullback-composition`). This is a decomposition:
one upper hole closed and one strictly smaller hole added, not a net reduction
in holes. The new theorem's proof is exactly `:= by sorry`.

Both private helpers are proved. The composition lemma is used twice by a real
Lean calculation; the final theorem is not an application of a renamed square.
Existing imported holes are unchanged.

Edge cases: none of the arguments invert a single-module comparison or assume
flatness, invertibility, nonzero modules, or nonempty schemes. Naturality works
for zero morphisms and zero modules. Equality transport is proved by equality
elimination, including reflexive equalities. Pairwise composition uses the same
leftDerivedLift factorization for identity morphisms and arbitrary schemes.

## No longer needed

None. No original import was removed. The existing composition, tensor-pullback
adjunction, and canonical single comparison nodes remain needed. The pairwise
composition lemma isolates a step of the original route; it does not bypass a
blueprint unit. The unit's `realized` lists are empty, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The planned single-module
composition calculation has no existing theorem with its pinned signature; it
is now isolated as the pairwise composition node. Searches found only generic
single-complex, adjunction, and derived-lift tools. LeanSearch returned an
Internal Server Error, recorded as unavailable rather than as no match.

`blueprint_refs.py ancestor lem-pc-canonical-single-pullback-square` returned
`None`: the existing created-item ancestry is broken at module-name entries.
The new node retains a null ancestor and explicitly identifies the original
square proof's pairwise leftDerivedLift step and its existing ancestry chain.
A whole-blueprint search for "single pullback" returned no matching node.

The library exposes module sheaves as both `Scheme.Modules` and
`SheafOfModules (moduleRings ...)`. These are definitionally equal, but generic
simplification sometimes refuses to unfold their category instances. The proof
uses explicit local functors and equations, and a typed mapped-identity equation,
to make cancellation precise; no library interface change is needed.

## New nodes

`lem-pc-canonical-single-pullback-composition`, in
`dag/nodes/sec-picard-framework/lem-pc-canonical-single-pullback-composition.json`,
states that the chosen derived composition followed by the composite single
comparison equals the two successive single comparisons followed by ordinary
pullback composition. It is a strict part of the original square argument.
The proof records evaluation of `leftDerived_fac_app`, naturality on single
complexes, and the mate calculation identifying tensor and ordinary composition.
Its dependencies are the existing canonical composition, canonical single
comparison, and tensor-pullback adjunction nodes. All three required kinds of
Mathlib search were actually run and logged. There are no change records.

## Second reading by U3

1. PASS: diffed both delivered modules against the repository. The existing
   theorem signature is byte for byte identical, including universes and the
   shared derived-category assumption. No definition, visibility, or public
   import changed. There are no forced adaptations or statement changes.
2. PASS: compiled both modules in import order with lcompile.py (12.9 and
   44.0 seconds). Independently compiled a scratch copy with #print axioms
   for both private helpers, the square theorem, and the composition theorem:
   only propext, Classical.choice, Quot.sound, and sorryAx occur. sorryAx is
   expected from the named composition hole and existing open dependencies.
   The square and helpers contain no sorry; the new theorem has exactly one
   whole-proof sorry. No forbidden declaration or hollow definition was added.
3. PASS: the new composition statement is the pairwise factorization step,
   strictly part of the square argument, and is used for its two paths in a
   genuine calculation. Checked its orientation against the pinned
   leftDerivedLift factorization in exists_derivedPullbackComposition and
   pullbackComp's adjunction mate. Its docstring and node give the complete
   remaining argument. Identity morphisms, zero modules, and empty schemes
   need no comparison to be inverted; no flatness assumption is missing.
   Independent LeanFinder search for compatibility of the left derived counit
   with composition and degree zero embedding found derived_counit and
   derivedε_fac_app, not this theorem. Loogle search for leftAdjointUniq found
   its counit and transitivity equations. Further rg searches of Lean and
   Mathlib found leftDerived_fac_app and conjugateEquiv_pullbackComp_inv,
   but no existing pinned single-pullback composition identity. Closing this
   hole requires the documented single-complex and adjunction calculations,
   rather than a short application of an existing theorem.
4. PASS: inspected the cancellation, equality transport, and naturality
   calculations top down. Only derived and ordinary composition isomorphisms
   are cancelled. The public comparison import supplies the statement's
   definitions; the new composition import is correctly proof-only. All old
   proof dependencies remain used, so No longer needed is complete (none).
   The unit sk-thm-picard-f-representable has empty realized lists; the change
   refines the existing below-unit argument and preserves the unit route.
5. PASS: the existing node changes only proof, proof_deps, and proof_origin.
   Those fields follow the Lean calculation and retain its old dependencies.
   The new node's statement and Lean record match the composition theorem;
   its source, proof steps, dependencies, searches, creation, and ancestry
   fields are present. No new definition or arbitrary existence witness is
   introduced.

Changed in second reading: restored the existing square theorem's docstring
verbatim, retaining the accurate expanded reduction in the node and report.
No proof repair was needed. One original hole closed and one smaller hole
added: this remains a decomposition with net zero holes, not a complete
axiom-free proof of the square.
