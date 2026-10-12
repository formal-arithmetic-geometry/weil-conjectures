## What changed

Replaced the sorry proof of `AlgebraicGeometry.baseChange_curve`, preserving its signature
byte for byte. It constructs `IsCurve` using the dimension comparison and Mathlib stability
of separatedness, local finite type, and quasi-compactness. Smoothness, properness and
affineness use Mathlib pullback instances. Connectedness uses the proved upstream
`GeometricallyConnected.of_connectedSpace_of_isSepClosed` and Mathlib geometric-connectedness
base change; the dimension equality gives the dimension-one field of `IsConnectedCurve`.

Added only `Sheaf.AlgebraicGeometry.BaseChangeDimension` with the strict dimension subclaim.
All added imports of the existing module are proof-only. Moved its three dimension imports
into that new module, where they supply the written proof plan. Removed the first worker's
redundant affine import and discarded the new `BaseChangeIsCurve`, `BaseChangeConnected`, and
`BaseChangeAffine` modules and their nodes: their facts are proved directly in the target.
No existing definition, statement, or docstring was changed; no change record is needed.

## Proved and sorry left

`AlgebraicGeometry.baseChange_curve`: its one existing sorry is replaced by a complete Lean
reduction. This does not yet mean axiom-closed: it depends on the one open dimension subclaim.

The only sorry in this delivery is `AlgebraicGeometry.baseChange_dim`, node
`base-change-dimension`, in `Sheaf.AlgebraicGeometry.BaseChangeDimension`. It is a named public
theorem with exactly `:= by sorry`, a source and a complete written proof. There are no hollow
definitions, private gaps or partial tactic proofs containing sorry.

Both delivered files compile cleanly through `lcompile.py --all`. Scratch `#print axioms`
checks are recorded in the second reading below.

## No longer needed

The target no longer directly imports `Sheaf.AlgebraicGeometry.Dimension`,
`Sheaf.AlgebraicGeometry.DimensionAffineOpenCover`, or
`Sheaf.AlgebraicGeometry.DimensionBaseChange`; those proof-plan imports are retained by
`BaseChangeDimension`, so they remain reachable and are not proposed for global deletion.
The unused first-worker `BaseChangeIsCurve`, `BaseChangeConnected`, and `BaseChangeAffine`
imports, modules and nodes are not delivered.

Every old direct proof dependency absent from the target's new `proof_deps`:

- `def-pc-base-change`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-pod-separated-finite-type-base-change`: replaced directly by Mathlib pullback instances.
- `def-weil-finite-type-morphism`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-weil-pbc-open-fibre-product`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-weil-pbc-fibre-product-affine-spectra`: moved to the dimension subclaim's written proof plan; retained transitively.
- `def-weil-surjective-morphism`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-weil-pbc-surjective-base-change`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-pc-dimension-affine-open-cover`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-pc-dim-base-change`: moved to the dimension subclaim's written proof plan; retained transitively.
- `def-pc-dimension`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-pc-scheme-dimension-local-rings`: moved to the dimension subclaim's written proof plan; retained transitively.
- `lem-weil-pbc-proper-base-change`: duplicate properness route replaced by the Mathlib instance already recorded in lem-pc-proper-base-change.
- `def-pc-fibre-product`: Mathlib pullback is used directly; no separate dependency on this conventions node.
- `def-pc-geometrically-irreducible`: connectedness is obtained directly from the upstream geometrically-connected theorem and Mathlib, without this mixed conventions node.

The replaced dependencies `lem-pod-separated-finite-type-base-change`,
`lem-weil-pbc-proper-base-change`, `def-pc-fibre-product`, and
`def-pc-geometrically-irreducible` are pruned from this item's dependency route; no
existing module is claimed globally unreachable. Unit `sk-prop-ext-invariance` and its
`realized` record are unchanged. Its statement and three proof steps are preserved; this
repair is confined to the supporting base-change lemma, below the unit level.

## Where the brief, the DAG or earlier work was wrong

The first worker unnecessarily left curve structure and connected-curve preservation as
new sorry theorems although only dimension was missing. Affineness was already proved, but
the report listed it as sorry. The four proposed nodes lacked self-contained statements,
complete proof steps, recorded searches, chapter/unit fields and verbatim Lean signatures;
the target node's proof still described the old route while its proof_deps listed the new
route. All retained records have been repaired. `dim_base_change`'s second clause cannot be
used for the full statement here: its `IsCurveOverField` hypothesis requires an integral
nonempty dimension-one scheme, whereas `IsCurve` allows empty and disconnected schemes and
zero-dimensional ones. Its first (algebraic) clause is retained in the dimension proof plan.

## New nodes

`base-change-dimension`, `dag/nodes/sec-curve-estimates/base-change-dimension.json`, isolates
only dimension equality. Its statement includes all of the Lean hypotheses, its proof deals
with the empty case separately and reduces the nonempty case to an affine open cover and
finite-type algebra scalar extension. Its Lean signature is recorded verbatim. Real searches
were run through `msearch.py` using LeanFinder, Loogle, grep and LeanSearch (the latter returned
HTTP 500 and is recorded as unavailable). The returned spectrum-dimension and polynomial
lemmas do not supply this scheme theorem. Searches of `lean/Sheaf` and the upstream source
found the algebraic dimension theorem and its integral-curve specialization, but no duplicate
of this possibly disconnected/empty curve statement. No change records.

## Second reading by K1

1. Compared every delivered module with the repository: the sole existing declaration's
   signature is byte-for-byte identical, its existing docstring is untouched, and all added
   imports in that module are plain proof-only imports. The other module is new. No existing
   data definitions or target interfaces changed. PASS.
2. Compiled both files in import order with `lcompile.py --all`: no errors or warnings.
   Scanned for forbidden declarations/attributes and every sorry. The only sorry is the
   named dimension theorem, listed above, with its own node and full proof docstring.
   Scratch `#print axioms` of both delivered declarations and the upstream connectedness
   theorem checked the trust basis; see the appended exact output. PASS subject to the
   explicitly remaining dimension obligation.
3. Checked the dimension subclaim mathematically for empty schemes (both dimensions bottom),
   Spec(k) (dimension zero), disjoint unions (the chart supremum), and dimension-one curves.
   No connectedness or smoothness is assumed or inferred from the curve hypothesis. It is
   precisely one clause of the target, not a renamed copy of the whole target. Searches were
   repeated independently with the queries above. Its complete source-based proof is in its
   docstring and node. Checked Stacks Tags [00P3](https://stacks.math.columbia.edu/tag/00P3),
   [04MU](https://stacks.math.columbia.edu/tag/04MU), and
   [0363](https://stacks.math.columbia.edu/tag/0363). PASS.
4. Replaced the unnecessary curve/connectedness splits by direct proofs and inlined the affine
   proof. Removed duplicate/unused target imports; retained the open dimension theorem's
   three proof-plan imports. Enumerated every old direct proof dependency that changed,
   including those moved into the new subclaim. Read `dag/units/sk-prop-ext-invariance.json`:
   its route and realized fields are unchanged, and its dimensional infrastructure remains
   reachable through the new module. PASS.
5. Rewrote the target node's proof, proof_deps and proof_origin to match the actual reduction.
   Repaired the one retained new node with all required stage-1/stage-3 fields, complete
   mathematical proof steps, their dependency union, genuine searches and exact Lean text.
   Removed the three other unneeded first-worker nodes. PASS.

Second reading changed: reduced three open subclaims to one; proved curve structure and
connectedness directly; inlined affineness; fixed imports, the dimension docstring, node
metadata and the inaccurate report. Delivery dry run and push are run after this reading.

Scratch axiom output:

```text
AlgebraicGeometry.baseChange_curve: [propext, sorryAx, Classical.choice, Quot.sound]
AlgebraicGeometry.baseChange_dim: [propext, sorryAx, Classical.choice, Quot.sound]
AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_isSepClosed:
  [propext, Classical.choice, Quot.sound]
```
