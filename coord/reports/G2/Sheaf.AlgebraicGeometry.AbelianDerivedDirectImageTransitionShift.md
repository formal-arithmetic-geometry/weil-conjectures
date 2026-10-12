## What changed

Proved `AlgebraicGeometry.Etale.abelianDerivedDirectImageTransition_shift` in
`Sheaf.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift` without changing
its signature or either existing definition. Added proof-only imports of
`Sheaf.AlgebraicGeometry.DerivedAdjunctionCommShift` and
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.

Four fully proved private helpers handle the elementary categorical calculation
and the restriction of exact-functor comparison isomorphisms to bounded-below
objects. The transition is factored through a natural transformation assembled
from the actual unit, counit and pullback comparison; its shift identity and the
naturality of the right-adjoint shift comparison give the result for arbitrary
coefficient morphisms and integer shifts. Updated the node's proof and proof
dependencies to match this argument. No unit statement or step is bypassed;
`sk-lem-failure-field` has no realized statement or step involving this helper.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.abelianDerivedDirectImageTransition_shift`
(node `lem-sbc-abelian-derived-transition-shift`). Added zero holes and zero new
modules. No `sorry` remains in the delivered module. All four private helpers
are proved in full.

The proof uses the existing theorem
`AlgebraicGeometry.Etale.derivedPlus_upperStarLowerStar_commShift`
(node `lem-weil-pbc-derived-adjunction-commshift`), whose proof is still `sorry`
in its own module. This is an existing dependency, not a new hole or an
axiom-free proof of the whole import closure.

## No longer needed

No existing import was removed: the original public import supplies the
statements and definitions. Both added proof-only imports are used.

Removed the proof dependency `def-sbc-abelian-higher-direct-image-map`, module
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap`: the proof uses the
transition's own concrete definition and does not need higher cohomology or
single-complex comparison maps. That node remains a statement dependency and
may still be needed elsewhere; no claim of global unreachability is made.
No other planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The node's proof plan works.
Its reference to the higher-direct-image map was unnecessary as a proof
dependency: this identity is a calculation on arbitrary derived objects.
No definitions, statements, universes or visibility of existing declarations
were changed. No forced adaptations or new nodes are needed.

## Second reading by G2

1. PASS: compared the complete module with the repository version. Both existing
   definition bodies and the theorem signature are byte-for-byte identical.
   Existing visibility and the public import are unchanged. The only Lean
   additions are two proof-only imports, four proved private helpers and the
   replacement of the theorem's `sorry` by its proof.
2. PASS: compiled the delivered file through `lcompile.py` without errors or
   warnings (5.8 seconds). Scanned for forbidden declarations and holes: none.
   Compiled a scratch copy with `#print axioms` for both definitions, all four
   helpers and the theorem. The definitions and helpers use only `propext`,
   `Classical.choice`, `Quot.sound`; the theorem also uses `sorryAx`, from the
   existing derived-adjunction shift theorem identified above. No object is
   chosen from an unproved existence theorem.
3. PASS: no statements or holes were split off. Read each private helper: the
   general transition identity follows from shift compatibility of the whiskered
   unit, comparison and counit, then naturality at the coefficient morphism.
   The three restriction calculations use the faithful inclusion and the actual
   specified comparison maps. They impose no restrictions on shifts or objects;
   zero shifts, negative shifts, zero complexes and zero coefficient maps are
   covered by the same argument. Independent search with Loogle
   `"CommShift", "whiskerRight"` found the generic whiskering instance already
   used; searches of `lean/Sheaf`, upstream shift modules and Mathlib's shift
   adjunction module found no existing bounded-below comparison instance or
   transition identity that replaces these calculations.
4. PASS: the proof uses existing unbounded exact-functor comparison instances
   and elementary categorical calculation, with the planned open
   derived-adjunction compatibility theorem. Both added imports are used and
   correctly private to the proof. Compared old and new `proof_deps`: the sole
   removed dependency is `def-sbc-abelian-higher-direct-image-map`, already
   reported under `No longer needed`. Read `sk-lem-failure-field`: its realized
   statement and step lists are empty, and this proof changes no unit route.
5. PASS: the only changed node fields are `proof`, `proof_deps`, `proof_origin`.
   Read the three proof steps against the Lean proof: they describe respectively
   the two adjunction instances, restriction of exact-functor comparisons and
   the whiskered natural-transformation calculation. `proof_deps` is exactly
   the union of their cited nodes. The Lean statement record is unchanged.

Second reading changed only this report: added the independent checks and
explicit axiom results. No proof or node repair was necessary.
