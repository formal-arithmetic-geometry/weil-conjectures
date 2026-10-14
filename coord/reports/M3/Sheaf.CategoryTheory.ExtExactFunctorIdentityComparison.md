## What changed

Replaced the proof of `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` in
`Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison` by a direct application of Mathlib's
`LocalizerMorphism.equiv_smallShiftedHomMap`, taking its localized functor to be the actual
identity. The comparison is induced termwise by `e`, followed by
`Functor.mapHomologicalComplexIdIso`. Shift compatibility is checked componentwise, the
single-complex source component is identified with `e.hom.app`, and its target inverse
component cancels. This proves the unchanged statement without the composition comparison.
The existing private localization helper is retained unchanged: a downstream module imports
it using `import all`. Existing docstrings and all signatures and visibility remain unchanged.
Updated the item's DAG proof and proof dependencies to match the implementation.

Validation: the original module compiled cleanly in 2.3 seconds; the replacement compiled
cleanly in 2.1 seconds using the required lcompile.py single-file command. Delivery dry run
also checks the axioms of every declaration. No other library module is adapted.

## Proved and sorry left

`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` is proved directly from Mathlib.
The dispatched source already contained zero `sorry`s: this is the queued upstream-review
repair in `coord/repairs.txt`, not a new hole closure. Holes closed: zero. Holes added: zero.
No `sorry` remains in the delivered module, and none is added elsewhere. The existing private
`commShift_of_localization` proof remains unchanged.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison` and
removed `lem-weil-pbc-ext-exact-functor-composition-comparison` from this node's `proof_deps`.
Neither `mapExactFunctor_comp_mk₀_eq` nor `exactFunctorCompositionComparison` is used.
The former local proof that `mapExactFunctor (𝟭 C)` fixes every Ext class is unnecessary:
`ShiftedHom.id_map` applies directly after the localization calculation.
The composition-comparison module and its source-only transitive dependencies are no longer
needed through this item's import path; other modules may still reach them independently.
The remaining public Mathlib import is needed by the statement and the proof. This auxiliary
node is not a unit statement or realized unit step, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic brief says this module still has `sorry`, but the dispatched file already has a
complete proof and is listed as an upstream duplicate repair. The review specifically suggests
`mapExactFunctor_eq_of_iso` plus `mapExactFunctor_id`. Neither name is in the pinned Mathlib
or WeilConjectures sources: local rg and msearch grep found neither, and Loogle reported the
first name unknown. LeanFinder returned mapExactFunctor_hom and related basic map lemmas.
The available general localization comparison is sufficient: specializing it to the actual
identity functor supplies both the transport and identity calculation without restating an
Ext theorem or importing our general composition comparison.

The original proof plan's composition-comparison step was therefore avoidable. The new proof
still follows the existing docstring's localized-complex naturality argument and the stated
source: [Stacks 015F](https://stacks.math.columbia.edu/tag/015F) says an exact functor is computed
termwise on every complex, and [Stacks 06XQ](https://stacks.math.columbia.edu/tag/06XQ) defines
Ext by shifted morphisms between the corresponding degree-zero complexes. These sources were
checked online because this clone does not contain literature/stacks-project/derived.tex.
No statement, definition, target, or unit record was changed; no new nodes were needed.

## Second reading by M3

1. Interface preservation: PASS. Diffed the sole delivered Lean module against the
   read-only repository version. Both existing declaration signatures, visibility,
   docstrings, and options are byte-for-byte unchanged. Only the main proof and its
   private proof import changed; no definitions or target statements changed. The
   node diff changes only `proof`, `proof_deps`, and `proof_origin`.
2. Proof validity: PASS. Independently compiled the delivered module with lcompile.py
   (2.3 seconds, no errors or warnings). Compiled a scratch copy with `#print axioms`
   for `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` and the existing
   private `commShift_of_localization`: both depend only on `propext`,
   `Classical.choice`, and `Quot.sound`. There is no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or new data construction. Read the comparison formula in
   pinned Mathlib `LocalizerMorphism.equiv_smallShiftedHomMap`: the source comparison
   is hx, the shifted target comparison cancels by hy, and identity mapping leaves
   x.hom. The component proof covers degree zero and all other integer degrees.
3. Split-off statements: PASS (none). No new declarations, holes, or nodes were added.
   The local hx and hy facts are proved and are genuine component identification and
   cancellation steps, not restatements of the item. Checked pinned Ext.Map and searched
   independently with msearch grep for `mapExactFunctor_comp_mk₀_natTransApp`,
   `id_mapExactFunctor`, and `mapExactFunctor_eq`; none is available in this pin.
4. Route and pruning: PASS. The direct Mathlib localization comparison avoids our
   composition-comparison theorem and a separate identity-action argument. The only
   remaining import supplies the public statement's Ext operations. The complete old
   proof-dependency difference is the composition-comparison node already listed in
   No longer needed. Neither this node nor that removed dependency occurs in any
   dag/units realized route; sk-thm-p1 is unchanged. Retained the private localization
   helper because HigherDirectImageRawPullbackIdentity imports all of this module
   and explicitly uses it. No additional pruning is justified.
5. DAG agreement: PASS. The three proof steps describe δ, hx/hy, and the final Ext.ext
   calculation in the delivered code. The remaining dependencies describe the exact
   functor construction and Ext operations used from Mathlib. proof_origin names the
   actual route. No node statement, unit, Lean signature record, or source changed.

Second reading changed only this report by recording the independent checks; no Lean
or DAG repair was needed. This delivers one completely proved comparison theorem as
an upstream-route repair, with zero baseline holes closed and zero holes added.
