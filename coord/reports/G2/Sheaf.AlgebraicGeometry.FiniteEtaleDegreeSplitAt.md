## What changed

Proved `AlgebraicGeometry.Etale.exists_finiteEtale_degree_split_at` with its signature
unchanged. Apply the existing local splitting to `pullback.snd f W.hom`; count its sheets
by the ordinary residue-field fibre; transport the cofan through pullback pasting; reindex
by `ULift (Fin d)`; and preserve the point, clopen immersions, and projection isomorphisms.
The unit's trace-splitting route is preserved.

Added the proof-only import `Sheaf.AlgebraicGeometry.FiberDegreeOfSplitCofan`, containing
a fully proved general fibre-degree computation. Its statement only assumes an affine
map and a finite coproduct cofan whose component structure maps are isomorphisms.
The helper's public import is needed for its statement. Neither existing public import
was changed. Updated the target node's proof, proof dependencies, and proof origin.

Both delivered modules compile without warnings. The helper's `#print axioms` lists only
`propext`, `Classical.choice`, and `Quot.sound`. The target's axiom check still reaches
`sorryAx` through existing library dependencies; no delivered declaration contains `sorry`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.exists_finiteEtale_degree_split_at`
(node `lem-weil-pbc-finite-etale-degree-split-at`).

Also proved `AlgebraicGeometry.Scheme.Hom.fiberDegree_eq_nat_card_of_split_cofan`
(node `lem-weil-pbc-fiber-degree-split-cofan`). No holes were added or split off, and
no `sorry` remains in either delivered module. This closes one original hole rather
than decomposing it into new holes. Existing transitive library holes are unchanged.

## No longer needed

No existing Lean imports were removed: the two public imports support the statement,
and `Sheaf.Paper.FiniteEtaleEtaleLocalSplit` supports the proof. No unused imports were
added. The degree count no longer uses these original proof dependencies:

- `def-weil-algebraic-closure` (`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`);
- `def-weil-geometric-point` (`Mathlib.FieldTheory.IsAlgClosed.Basic` and geometric-point
  constructions in `Mathlib.AlgebraicGeometry.ResidueField`);
- `lem-galois-geometric-fibre`
  (`Scheme.Hom.exists_overIso_sigma_of_isSepClosed` in the already-required
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`);
- `lem-weil-pbc-open-fibre-product` (open pullback comparison);
- `lem-weil-pbc-scheme-coproduct-copies` (the geometric-point counting route).

These are pruned from this node's proof dependencies; their modules are not asserted
to be globally unreachable. `FiberDegree`, `Pullbacks`, and `Limits` remain needed
for other declarations used here. The new helper uses the Mathlib leaf
`lem-sc-etale-fibre-product-base-change-coproduct` as a generic tool; it imports no
unproved module from that unit.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The DAG's algebraic-closure comparison
was unnecessary: the ordinary residue-field fibre already has the product algebra
needed to count sheets. The existing target docstring describes that longer planned
argument; the updated node records the actual shorter proof.

The ancestor command cannot traverse this item's `created.item`, which contains a
module name rather than a node id. The new node inherits the explicitly recorded
blueprint ancestor `lemma-weil-pbc-curve-locally-constant-reduction` and its trace step.
No contract or tool was changed.

Read Stacks Tags 04HN and 03SH (including the paragraph after 03SE) on the Stacks site;
the local literature checkout contains only the tracked citation lists. The general
residue-field computation is written out and fully proved here. Searches were run
through `msearch.py`: LeanFinder, Loogle, grep, and LeanSearch. LeanSearch returned an
internal server error, recorded as unavailable. The other searches gave no exact
fibre-degree count theorem. Blueprint and DAG searches found no duplicate statement.

Edge cases: the helper allows empty `J`, whose product algebra has dimension zero.
The target uses the same equivalence/reindexing for `d = 0`. A point `w` is required,
so empty `W` contributes no case; no assumption that the base is globally nonempty
or connected is introduced. The fibre argument works over arbitrary residue fields.

## New nodes

`lem-weil-pbc-fiber-degree-split-cofan`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-fiber-degree-split-cofan.json`, records
`Sheaf.AlgebraicGeometry.FiberDegreeOfSplitCofan` and its fully proved declaration
`AlgebraicGeometry.Scheme.Hom.fiberDegree_eq_nat_card_of_split_cofan`. This is the
sheet-counting calculation only; it constructs neither an étale neighbourhood nor
the target's reindexed clopen splitting. There are no change records because all
existing signatures, definitions, and public imports remain unchanged.

## Second reading by G2

1. I compared the delivered target module with the repository version. The theorem
   signature and all existing declaration statements are unchanged byte for byte;
   only the target proof, its proof-only helper import, and DAG proof metadata differ.
   Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. They compile without
   errors or warnings; neither file contains `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by`. The helper's proof uses only the permitted standard
   axioms, verified by `#print axioms` in a scratch copy. The target's scratch axiom
   check additionally lists `sorryAx` from existing transitive library holes, as
   already reported above. Verdict: pass.
3. I checked the new helper statement against the fibre calculation and its edge cases.
   It is a strictly smaller, reusable sheet-counting result, allows an empty finite
   index type, and adds no hypotheses beyond affinity, a colimit cofan, and component
   isomorphisms. Searches found no duplicate declaration. Verdict: pass.
4. I traced the proof from the target downward. It uses the existing local splitting,
   the new residue-field degree lemma, pullback pasting, and finite reindexing. The
   route preserves the unit's trace-splitting step. The report records the former
   geometric-fibre dependencies that are no longer used; imports remain minimal.
   Verdict: pass.
5. I checked both DAG nodes against the Lean declarations and proof dependencies. The
   helper node records its source, proof, searches, and Lean module; the target node
   records the shorter residue-field route and its actual dependencies. Verdict: pass.

I changed only this report by adding this second-reading audit; no Lean code or node
statements required repair.
