## What changed

Completed `derivedCoupleMorphismStep` in
`Sheaf.CategoryTheory.DerivedCoupleFunctoriality`. Construct the cycle map with
`kernel.map`, the derived E map with `cokernel.desc`, and the derived D map with
`image.map`. Prove the alpha, f and g squares by the universal-property equations
and mono/epi cancellation. Unfold only `derived` to use the selected
`DerivedMaps` commutation equations. Simplify the identity functor in the
bidegree transport used by the g square. No existing signature, definition,
visibility, import, or declaration attribute changes; no helper is added.

## Proved and sorry left

Holes closed: `CategoryTheory.BigradedExactCouple.derivedCoupleMorphismStep`
(the sole original hole, associated with node
`lem-sp-derived-couple-functoriality`). This completes the local proof of
`CategoryTheory.BigradedExactCouple.derivedCoupleFunctoriality` through its
existing page induction and limiting-subobject descent.

Holes added: none. Split-off statements: none. No sorry remains in this module.
The existing `nextMorphism` choice is determined uniquely: its D map is fixed
by the monic derived inclusion; its E map is fixed by the epimorphic derived
projection and the kernel map, itself fixed by the monic kernel inclusion.
It therefore chooses no arbitrary witness of mere existence.

## No longer needed

None. The existing proof dependencies `def-sp-exact-couple` and
`def-sp-convergence` are both used. Both original imports remain necessary:
`ExactCoupleConvergence` supplies statement data and the convergence proof;
`ExactFunctorHalfPlane` supplies the existing elementary `transport_square`
used in the one-step construction and finite transport. No modules are pruned.
The three conversion helpers proposed by the first reader are removed before
delivery; they were never library dependencies.

## Where the brief, the DAG or earlier work was wrong

The first reader attached the one-step proof docstring to a conversion helper,
used conversion equalities in place of the selected structure maps'
commutation equations, and omitted `Functor.id_map` simplification in the final
g transport. That version failed compilation. Its conversion helpers also
unnecessarily expanded an obsolete `ofShifted` representation; the current
published construction reduces directly with `dsimp only [derived]`.
The final proof retains the valid kernel/image/cokernel construction.
The DAG's existing proof route already describes the final argument correctly.

## Second reading by Q1

1. Compared the entire delivered module with the shared version using `diff`.
   The final diff replaces only the body `sorry` of `derivedCoupleMorphismStep`.
   All existing signatures and definitions are byte-for-byte unchanged. The
   original one-step docstring is again attached to its own theorem. Pass.
2. Read the kernel map, boundary compatibility, cokernel descent, image map,
   and all three cancellation arguments, as well as the unchanged page and
   limiting-subobject arguments. Compiled the final module and checked axioms
   in a scratch copy: the one-step theorem, both public helper theorems, and
   `derivedCoupleFunctoriality` use only `propext`, `Classical.choice` and
   `Quot.sound`, with no `sorryAx`. No forbidden declaration or data hole
   occurs. The final file compiled without warnings in 4.5 seconds. Pass.
3. No statement is split off and no helper remains. The universal-property
   construction covers s = 0, arbitrary integer bidegrees, zero maps and zero
   objects without additional assumptions. Searched the shared category-theory
   sources for existing couple morphism/functoriality results and derived-map
   conversions; retained Mathlib's kernel, cokernel, image, and cancellation
   APIs rather than introducing a substitute theorem. Pass.
4. Followed the existing top-down route: one derivation, page induction,
   finite-cycle/boundary transport, and GLB/LUB descent at infinity. Both imports
   and both old proof dependencies remain used, so the pruning list is empty.
   The attached unit `sk-prop-av-pqf-finite` has empty `realized` entries and is
   unchanged; this auxiliary proof removes no realized unit or step. Pass.
5. Read `lem-sp-derived-couple-functoriality` and its proof, proof_deps and
   proof_origin. They describe precisely the kernel/image/cokernel construction,
   chosen DerivedMaps equations, dependent page induction and limiting descent
   used here. No new node or metadata correction is needed. Pass.

Second reading changed: removed all three conversion helpers and their heartbeat
increase, restored the original docstring placement, used the actual alpha/f/g
commutation equations after unfolding `derived`, and simplified the identity
functor in the final transport. No statement or definition changed.
