## What changed

Replaced the sole sorry of
`AlgebraicGeometry.perfect_hom_mayerVietoris_geometric_columns_even_three`
with a complete proof from one smaller, single-open comparison statement.
All existing signatures and public imports are unchanged. Added proof-only imports
of `Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.Types.Filtered`, and
`Sheaf.AlgebraicGeometry.PerfectHomOpenColimitLocalComparison`.

The private helpers prove a product-colimit presentation using common-stage
representatives, split shifted biproduct Hom explicitly, and transport the product
of two local comparisons to the canonical column comparison. The inverse splitting
uses shifted inclusions and addition; the source equivalence is uniquely pinned
on the colimit inclusions. Naturality of the splitting is proved both for transitions
and for apex legs using A.map_hom₂. No arbitrary object is chosen from an unproved
mere existence statement.

The remaining single-open colimit recognition step is isolated in its own module
and node. It is independent of the Mayer–Vietoris family, the second open and the
biproduct/product argument. One application on U and one on V finish the item;
this is a genuine decomposition, not a renaming of the original statement.

The source places read are Stacks Tags
[09RE](https://stacks.math.columbia.edu/tag/09RE) and
[08BW](https://stacks.math.columbia.edu/tag/08BW).
The unit's realized fields are empty; the Mayer–Vietoris route is retained.
Empty opens, zero Hom groups, a singleton index preorder, and non-antisymmetric
directed preorders require no excluded cases. The group forgetful functor is used
with a shrunk filtered-colimit size, retaining universes u and w independently.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.perfect_hom_mayerVietoris_geometric_columns_even_three`
(node `lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-three`).
No sorry remains in the item's module.

Added exactly one lower hole:
`AlgebraicGeometry.perfect_hom_open_colimit_local_comparison`
(node `lem-pc-perfect-hom-open-colimit-local-comparison`), in
`Sheaf.AlgebraicGeometry.PerfectHomOpenColimitLocalComparison`.
Its proof is exactly `by sorry`; its docstring and node give the complete argument
from the already stated `perfect_hom_open_stage_presentation` plus preservation
of filtered colimits by the group forgetful functor. No definitions contain holes.
This is a decomposition: one hole closed, one added, net zero; the substantial
biproduct splitting, naturality and product-colimit transport are now proved.

Both delivered modules compiled together in import order without errors or
warnings (approximately 5 seconds for the lower statement and 9 for the item).

## No longer needed

No original imports were removed. Removed the proof dependency
`lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even`
(module `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEven`):
its theorem assembles columns 0 and 3 by using this item, so importing it here would
be circular. It remains a caller of this theorem, not a dependency of its proof;
no claim is made that the parent module is globally unreachable.
The canonical column comparison is recognized directly; the planned stage-colimit
continuity theorem and any bijectivity or continuity assertions are not used.

## Where the brief, the DAG or earlier work was wrong

The original node's proof applied the parent even-column theorem, but that parent
already applies this fixed-column theorem. The route was circular and could not
be implemented by importing its recorded dependency. The node now records the
single-open comparisons and the actual product/colimit assembly.

The source for PerfectHomOpenStagePresentation is present and its node records a
landing, but its olean is absent both locally and in the published server build.
The attempted full proof from it and the first delivery dry run failed solely at
that missing import. The generic local-presentation constructor and all the
product glue compiled separately. The final delivery leaves just the single-open
colimit recognition step for the next worker, rather than copying or restating the
unavailable stage-presentation declaration. The new statement genuinely adds the
colimit packaging and is distinct from both that declaration and the original item.

## New nodes

`lem-pc-perfect-hom-open-colimit-local-comparison` recognizes the canonical
abelian-group Hom colimit comparison for one compact open as a pinned local
comparison. Its complete proof uses the existing stage/apex presentation, shrinks
filtered-colimit preservation, and checks the pinning equation on stage inclusions.
It asserts neither invertibility nor continuity and contains no Mayer–Vietoris
family or two-open term. It is sourced to Tag 09RE's open-local comparison, belongs
to the same chapter and unit, and is realized in its own new Lean module.
LeanSearch was unavailable (HTTP 500); LeanFinder and Mathlib grep found no match.
Repository rg found only the definition, the earlier stage theorem and the private
local constructor in the odd-column proof. Blueprint search found no duplicate.
No statement or definition interface changed; there are no change records or
forced adaptations.

## Second reading by D4

1. **Unchanged statements.** I compared the delivered item module with the
repository version. The existing theorem signature is byte-for-byte unchanged;
the new lower theorem has the signature recorded in its node. Verdict: pass.
2. **Proof and declarations.** Both delivered modules compile with
`lcompile.py --all`; the item has no `sorry`, and the only remaining `sorry` is
the named lower theorem. There are no axioms, unsafe declarations, hollow
definitions, or untracked proof holes. Verdict: pass, with the lower theorem
explicitly split off and documented above.
3. **Truth and strength of the split.** The lower statement recognizes the
canonical one-open colimit comparison and supplies exactly the pinned local
comparison needed by the item. It does not assert invertibility or continuity,
and it is independent of the two-open biproduct construction. Verdict: pass.
4. **Pruning and dependencies.** The item no longer imports or uses the
circular parent even-column theorem; its proof uses the recorded single-open
comparison, local-map constructor, Mayer–Vietoris diagram, and triangle-row
presentations. The private product-colimit and splitting helpers are used in the
item proof. Verdict: pass; the removed dependency is listed under
`## No longer needed`.
5. **Unit route and nodes.** The fixed index-3 Mayer–Vietoris route is retained:
single-open comparisons are established first, then the two columns are split
and recombined. The new lower node, its Lean declaration, proof description,
source, and dependency list agree. Verdict: pass.

I changed only this report section; no Lean statements, definitions, or proof
code required repair during second reading.
