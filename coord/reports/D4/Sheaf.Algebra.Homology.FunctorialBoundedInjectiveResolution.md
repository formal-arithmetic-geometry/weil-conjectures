## What changed

Completed `CochainComplex.exists_functorial_bounded_injective_resolution_of_object_resolution`
in `Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution`. Extend the supplied
object resolutions by zero and apply them degreewise to the complex. The canonical total
complex and total maps give one replacement functor independent of a chosen lower bound.
Finite diagonal biproducts prove injectivity and preservation of every lower bound.
A private comparison argument truncates columns when checking each homology degree and
applies the source library's proved finite-column comparison theorem.

All existing public signatures, visibility, public imports, and declaration docstrings are
unchanged. All new helpers are private. The two item nodes record the actual proof routes.
The change record `coord/changes/functorial-injective-resolution-proof-scopes.md` describes
private proof scopes which the static preflight conservatively classifies as an interface
change. There are no new nodes, forced adaptations, or target changes.

The draft also completed `Sheaf.Algebra.Homology.FunctorialObjectResolution`. The second
reader checked that proof and its axioms, but the dry run refused its inclusion because
E1 now holds that module (server claim checked directly). It is not a forced adaptation:
the original compiles unchanged against this delivery. Its reviewed source and node are
preserved under `withheld/` in this sandbox and are excluded from the delivery.

## Proved and sorry left

Closed one existing hole:

- `CochainComplex.exists_functorial_bounded_injective_resolution_of_object_resolution`
  (`lem-weil-pbc-functorial-bounded-injective-resolution-totalization`).

No hole is added or split off, and no `sorry` remains in the delivered module. This is a
complete proof of the supplied-object-resolution totalization theorem, not a decomposition.

The upper `CochainComplex.exists_functorial_bounded_injective_resolution` retains its
existing assembly proof. Its existing dependency
`CochainComplex.exists_functorial_object_injective_resolution`
(`lem-weil-pbc-functorial-object-resolution`) remains open in E1's module, which this
delivery does not change. Consequently the assembly theorem still depends on `sorryAx`;
the newly closed totalization theorem uses only the three permitted standard axioms.

## No longer needed

Removed the item's proof-only imports:

- `Sheaf.Algebra.Homology.FirstQuadrantAugmentation`
- `Sheaf.CategoryTheory.DoubleComplexTotal`

The second reader also removed the redundant proof-only import
`Mathlib.Algebra.Homology.Embedding.ExtendHomology` introduced in the draft. Its required
API is supplied by the remaining imports. Removal tests confirm `Int.Interval` remains
necessary for finite diagonal indexing.

All old direct dependencies removed from the totalization node are accounted for:

- `lem-sc-first-quadrant-column-augmentation`: replaced by finite-column comparison,
  without reindexing the bicomplex to natural degrees.
- `def-sp-double-complex-total`: the proof uses Mathlib's canonical totalization directly.
  This node remains an indirect dependency of finite-column comparison.
- `def-sp-abelian`: removed as a redundant direct proof edge. The unchanged `[Abelian C]`
  hypothesis and statement dependencies retain the setting, also recorded by the two
  totalization/comparison dependencies. No assumption is removed.

The proof instead uses `lem-sc-integer-finite-column-total-comparison` and
`lem-weil-pbc-total-bounded-below`. No module is withdrawn or claimed to be pruned globally;
other parents may still import the two removed modules.

## Where the brief, the DAG or earlier work was wrong

The first-quadrant augmentation route can be replaced by finite column truncation and
the source library's complete finite-column comparison proof. The existing
`Sheaf.Algebra.Homology.BoundedBelowTotalComparison` theorem assumes countable coproducts,
which are absent here. The local comparison proof uses only the totals supplied by finite
diagonals and introduces no such assumption.

No statement was found false. The hypothesis that `E(0)` is zero follows from preservation
of zero morphisms; it is retained unchanged.

The draft report's assertion that D4 holds the object-resolution dependency became stale.
The required dry run rejected that additional proof work because E1 holds it and its
adaptation is not forced. The second reader corrected the delivery scope and all counts;
the reviewed proof is preserved separately rather than modifying E1's module.

## Second reading by D4

1. **Visible interface: pass.** Read both draft modules and their complete diffs. Compared
   exact source bytes of all three existing theorem signatures, their docstrings, and the
   public import lists: unchanged. All added declarations are private. After the ownership
   rejection, excluded the object-resolution module and its node. The delivered file only
   changes the item's proofs, private helpers, and proof-only imports. No target or public
   definition changes, and no forced adaptation remains.
2. **Proof and construction: pass.** Both draft modules compiled together without warnings
   or errors in 6.7 s and 4.8 s. Scratch `#print axioms` checks initially confirmed all three
   public theorems use only `propext`, `Classical.choice`, and `Quot.sound` against the draft
   dependency. Final verification uses the shared object-resolution module instead: the
   newly proved totalization theorem is independent of its open hole; the assembly theorem
   still depends on that existing hole. That scratch compilation passed in 5.8 s and its
   explicit axiom output confirmed exactly these dependencies. Read every private helper,
   augmentation naturality,
   the finite diagonal coproduct identification, and the comparison proof. There are no
   sorries, forbidden declarations, or hollow definitions in the delivered file. Data comes
   from canonical extensions, totalization, and coproduct universal properties, without
   selecting arbitrary witnesses of unproved existence theorems.
3. **Split statements and edge cases: pass.** No split statement or new node is delivered.
   Checked zero complexes, zero morphisms, negative lower bounds, and empty diagonals n<a.
   The truncation cutoff x=n-b+1 preserves all three terms n-1,n,n+1 computing homology,
   including x<a. The private lemmas are fully proved, strictly smaller subarguments.
4. **Shortest route, imports, and unit: pass after pruning.** Independently searched the
   shared library, upstream homological algebra, and Mathlib for bounded-below comparison,
   finite columns, recursive resolution functors, and functorial injective resolutions.
   Read the existing finite-column theorem and the stronger-assumption bounded-below API;
   no shorter applicable public theorem was found. Removed the redundant extension import
   and confirmed the interval import is necessary. The pruning list accounts for every old
   direct dependency removed. Checked `dag/units/sk-thm-properbasechange.json` `realized`:
   neither this item nor the pruned augmentation node realizes a unit step. The unit route
   is retained.
5. **DAG agreement: pass.** Compared the two delivered JSON nodes with the shared versions:
   only `proof`, `proof_deps`, and `proof_origin` differ. The totalization node records
   finite diagonals and finite-column comparison; the upper node records object resolution
   followed by totalization. Step dependency unions match `proof_deps`, and their recorded
   Lean declarations exist. The upper route does not claim the object theorem is proved.

Second-reading changes: removed one redundant delivered proof import, completed the direct
dependency pruning account, and withheld the separately held dependency and its node after
the tool's ownership rejection. The item's proof bodies and DAG routes needed no repair.
One existing hole is closed, zero are added, and zero are split off.
