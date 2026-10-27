## What changed

Filled three proof bodies in
`lean/Sheaf/AlgebraicGeometry/StablePointedModuliGroupoids.lean`, preserving every
statement, definition, instance body, docstring, and import.

* `AlgebraicGeometry.StablePointedModuli.hom_operations`: construct the identity
  pullback square and horizontally paste the two given pullback squares. The
  labelled-section equations follow by associativity and the two marking equations.
* `AlgebraicGeometry.abelianLevelBaseChange_isIso`: nonzero ell makes
  `ULift (ZMod ell)` finite, hence additive torsion. Apply the existing proper
  base-change theorem for torsion coefficient rings, identify its transformation
  with `derivedBaseChangeMapPlus`, and use preservation of isomorphisms by each
  functor in the defining composite.
* `AlgebraicGeometry.AbelianLevelModuli.pullback_frame_condition`: unfold the
  explicitly constructed frame and pullback arrow; the constant-sheaf comparison
  cancels its inverse, leaving precisely the specified exchange morphism.

The first proof handles zero markings without a special case. The second uses
only ell nonzero, exactly its existing hypothesis, and does not require primality
or invertibility on the base. The third is the identity of the actual chosen maps,
not an identification through an arbitrary isomorphism.

Searches: LeanFinder for identity and pasting of cartesian squares, and Loogle
for `IsPullback.paste_horiz`, both located Mathlib's horizontal pasting lemma.
Read its signature and the identity-square constructor. Local searches across
Mathlib, WeilConjectures and Sheaf located the proper base-change theorem,
finite additive torsion, the existing derived pasting laws, and constant-sheaf
composition coherence. No alternative moduli theorem was used.

## Proved and sorry left

Closed 3 of the 5 original holes:

* `AlgebraicGeometry.StablePointedModuli.hom_operations`.
* `AlgebraicGeometry.abelianLevelBaseChange_isIso`.
* `AlgebraicGeometry.AbelianLevelModuli.pullback_frame_condition`.

Added 0 holes and split off 0 statements. Two original holes remain untouched,
both attached to `def-sfb-stable-pointed-moduli-groupoids`:

* `AlgebraicGeometry.StablePointedModuli.pullback_properties`: stability,
  normalized-component special-point conditions and scalar-valued Zariski genus
  must be transported through iterated geometric-fibre isomorphisms.
* `AlgebraicGeometry.AbelianLevelModuli.hom_operations`: the canonical derived
  exchange pasting and constant-comparison laws must be transported through the
  degree-one homology and classical right-derived comparison isomorphisms.

This is a partial proof delivery, not a decomposition and not a claim that the
remaining two results are proved. No custom axiom or new declaration was added.

## No longer needed

None. No imports, declarations, modules, or DAG dependencies were removed.
The node is a definition node with empty proof and proof_deps; its statement
and dependencies remain unchanged. Its existing proper-base-change dependency
is used directly. All blueprint unit steps are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The five named proof obligations are
attached together to the existing definition node rather than separate proof
nodes. This delivery preserves that attachment and changes only three proofs.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
