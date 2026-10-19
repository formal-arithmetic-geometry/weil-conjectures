## Worker report

The statement is `CategoryTheory.SimplicialLatching.simplicialLatchingMap_spec` in
`lean/Sheaf/AlgebraicTopology/SimplicialLatchingDegenerateSubset.lean`.
This replacement report describes the maintainer-corrected final module. The original
worker and group second-reader report remains in the immutable snapshot.

The final module reuses the already landed declarations in
`Sheaf.CategoryTheory.TensorCoendSkeletalPushouts`:
`CategoryTheory.TensorCoendSkeletal.LatchingIndex`, `latchingDiagram`, `latching`,
`latchingCocone`, `latchingTo`, and `latchingMap` (source lines 159–204).
These are concrete constructions, not an assumed latching theorem. Their record is
in `lem-coef-tensor-coend-skeletal-pushouts.lean.declarations`. No new helper,
definition node, dependency repair, or additional theorem hypothesis is needed.

Clause audit:

* `T T' : SSet.{u}`, `n : ℕ` give arbitrary small simplicial sets and every degree.
  `SSet` is the recorded simplicial-set dependency's Mathlib notion.
* `LatchingIndex n` is the opposite of the full subcategory of `Under [n]`
  consisting of epimorphic legs with target length strictly below n. An arrow
  σ → τ therefore has a map ρ from the target of τ to that of σ and relation
  τ ≫ ρ = σ. It is automatically surjective because σ is surjective.
* `latchingDiagram T n` sends an object to its full lower simplex set and an
  arrow to `T.map ρ.op`. `latching T n` is its chosen set colimit.
* `latchingTo T n` is `colimit.desc` of the cocone with legs `T.map σ.op`.
  `Function.Injective` and the exact `Set.range` equality give the requested
  identification with `T.degenerate n`, including its induced bijection.
* The third conjunct specifies every structure leg on every lower simplex.
* The next conjunct gives naturality with the actual induced colimit map
  `latchingMap φ n`, for every simplicial map φ. The `Set.MapsTo` conjunct
  identifies the map of degenerate subsets as the restriction of φ_n.
  Together these give naturality of the bijections with the degenerate subsets.
* The final implication says explicitly that at n = 0 the indexing category,
  the latching colimit, and the subtype of degenerate simplices are empty.

The two statement dependencies are Mathlib leaves: `SSet` in Basic.lean,
`SSet.degenerate` in Degenerate.lean, and `Cocone`, `IsColimit`, `colimit`,
`colimit.ι`, `colimit.desc` in Limits.Cones/IsLimit/HasLimits. The proof dependency
`lem-weil-pbc-simplicial-set-nondegenerate-decomposition` is also a Mathlib leaf:
`SSet.exists_nonDegenerate`, `unique_nonDegenerate_dim`,
`unique_nonDegenerate_simplex`, `unique_nonDegenerate_map`. The proof docstring
spells out the six node steps, including image factorization, descent of an
arbitrary compatible cocone, uniqueness, comparison, and naturality.

Searches in the immutable node record cover LeanSearch, LeanFinder, Loogle, and
grep. The independent maintainer source searches additionally used `latching`,
`Latching`, `degeneracy.*colimit`, `colimit.*degeneracy`, `degeneracy part`,
`degenerate subset`, `proper surjections`, and `nonidentity epimorphisms` over
Mathlib, WeilConjectures and the group clone's lean/Sheaf. Mathlib's Splitting
coproduct and NonDegenerateSimplicesColimit diagram are different. The group
clone search did find the existing proper-surjection construction named above;
the replacement uses it instead of introducing another copy. No exact existing
theorem with all of this item's conclusions was found.

## Second reading by Q20

The original group's independent reading, preserved in the snapshot, checked the
node, source, statement dependencies and theorem clauses, including the reversed
indexing arrows, arbitrary-map degeneracy, all simplicial maps, and degree zero.
It reported a successful scompile.py compile. The maintainer's further independent
reading confirms the mathematical statement and repairs H4/H8 below.

The final module has only one postponed proof, the named theorem's `sorry`.
There are no new data definitions, no local theorem proofs, no pro-etale
substitute, no additional assumptions, and no implicit free variables (the file
sets `autoImplicit false`). All quantities remain universe-polymorphic in u.
The indexing category is small in universe zero; Type u has the needed colimits,
including u = 0. Empty simplicial sets, n = 0, n = 1 (only the degeneracy to
[0]), composites of surjections, and maps collapsing nondegenerate simplices
are covered. No characteristic, nonemptiness, or finiteness assumption on T is
introduced.

## Maintainer corrections and compiler evidence

H4: remove the duplicate latching category, diagram, colimit and canonical maps;
use the already landed TensorCoendSkeletal construction. Its opposite-under
category encodes exactly the same triangles. This is reuse of concrete helper
data and does not assume the tensor-coend theorem or add that theorem as a
mathematical hypothesis. The TeX statement and all DAG dependency fields stay
unchanged. The Lean record names the final signature verbatim.

H8: the original helper docstrings lacked source/blueprint markers, and its helper
names were absent from lean.declarations. Removing those duplicate helpers removes
these defects; the sole new declaration has the source, blueprint marker and a
full step-by-step proof docstring. The module also has the standard public module
header and explicit auto-implicit check.

Both the immutable original module and the replacement were compiled individually
with `/home/ubuntu/weil-launcher-nt/scompile.py Q20
lem-coef-simplicial-latching-degenerate-subset <file>` on 2026-10-17. The installed
wrapper currently uses server confirmation, rather than the older local-only
implementation described in the brief. Both sandbox and library-path checks
passed without errors or warnings. The replacement's imported side overlay
TensorCoendSkeletalPushouts also compiled (4.1 s). Final replacement sandbox and
library checks took 1.8 s and 2.0 s, respectively, in private overlay
`nt-local-compile-2ph0v6hd`. No global build, project edit, Git mutation, direct
SSH command, delivery, or landing was performed by this review.
