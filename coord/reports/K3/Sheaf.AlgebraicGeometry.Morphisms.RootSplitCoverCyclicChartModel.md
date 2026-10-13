## What changed

Replaced the sole sorry in RootSplitCoverCyclicChartModel by a case split on whether
g belongs to y.asIdeal. The divisor branch applies the new
RootSplitCoverOnDivisorCharts theorem. The other branch applies the new
RootSplitCoverAwayDivisorCharts theorem, taking m=d and all exponents equal to one.
Both imports are proof-only. The existing theorem signature and visibility are
byte-for-byte unchanged. No definition or target statement is changed.
The item's node records the two actual dependencies.

The first worker tried to reuse RootSplitCoverPrescribedCyclicCharts. That module
has since been proved FROM this model. Importing it creates a cycle and cannot
supply an independent proof of the model. The second reading replaced that
circular use by an explicitly open, strictly on-divisor statement. No module
outside this delivery was adapted; no change record is needed.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.root_split_cover_cyclic_chart_model
(lem-sbc-root-split-cover-cyclic-chart-model), one of one original holes.
Added and still open:

- AlgebraicGeometry.Scheme.root_split_cover_on_divisor_charts
  (lem-sbc-root-split-cover-on-divisor-charts), in RootSplitCoverOnDivisorCharts;
- AlgebraicGeometry.Scheme.root_split_cover_away_divisor_charts
  (lem-sbc-root-split-cover-away-divisor-charts), in RootSplitCoverAwayDivisorCharts.

No sorry remains in the item. This is a decomposition, not a complete axiom-free
proof: one hole closed, two added, net minus one. The lower statements are distinct
branches, not copies of the unrestricted theorem. Each has a sourced complete
proof in its docstring and a matching node. There is no definition or arbitrary
witness selected from an unproved existence theorem in any delivered module.

## No longer needed

No baseline import, node, or module is pruned. The original item's proof_deps was
empty. The first worker's added prescribed-chart import was removed because of its
cycle; it was never part of the baseline item's imports or proof_deps. The five
original public imports supply the unchanged statement's scheme, etale, root-algebra,
regularity, and scalar regularity language. The first worker's new off-divisor
proof_deps entry lem-weil-pbc-finite-etale-etale-local-split is also removed; the
shorter proof plan uses the given δ directly. Its module was not imported, so no
baseline module is pruned. The lower off-divisor statement additionally
imports Pi algebra instances for the product's algebra structure.

## Where the brief, the DAG or earlier work was wrong

The first worker read an older prescribed-chart statement as an independent sorry.
The current repository proves it from this very model. Compilation against older
compiled artifacts hid the circularity, which deliver3.py correctly refused.
The proof now explicitly leaves the on-divisor classification open.

The off-divisor branch needs no regularity or cyclic integral-closure arguments.
The source
[Stacks 0EYG](https://stacks.math.columbia.edu/tag/0EYG) distinguishes these two cases;
[04HN](https://stacks.math.columbia.edu/tag/04HN) supplies local splitting. Keeping
φ(g), instead of replacing it by 1, uses S[T]/(T-φ(g))≅S. The on-divisor docstring
spells out the connected cyclic torsor, orbit fields, normal integral closures,
and pointed etale descent rather than invoking the circular prescribed theorem.
The off-divisor helper now uses the supplied splitting directly over the root
cover; no second local splitting or descent of Y is needed.

The fixed unit sk-prop-input-spreading quotes the tame structure inputs in its
trait step; this decomposition retains that route. Its realized fields are empty,
so no realized step is bypassed or changed. The generic finite-etale-local-splitting
node is unnecessary: the supplied δ already
splits the cover over the affine punctured root cover, which is itself an etale
neighborhood of the off-divisor point. This shorter route remains below unit level.

## Second reading by K3

1. Compared the model with its repository version by diff and mechanically checked
   its signature before := byte-for-byte. Only proof text and plain imports change;
   every original declaration and public import is preserved. Verdict: pass.
2. Compiled every delivered module through lcompile.py. The only remaining sorries
   are the two named lower theorems listed above. No axiom, unsafe, opaque, extern,
   implemented_by, hollow definition, or anonymous hole is present. A scratch copy
   with #print axioms confirms that the model and both helpers use only propext,
   Classical.choice, Quot.sound, and sorryAx from the lower holes. Verdict: pass.
3. Checked each lower statement against the two original cases. Off the divisor,
   n>0 makes the finite free root cover faithfully flat; invertible n and g make it
   etale. Its positive free rank supplies a point above y. Choose the affine
   punctured root cover itself as Spec S, transport δ along its basic-open
   localization isomorphism, and apply degree-one evaluation to get the chart. On the
   divisor, regular local strict henselization and its prime divisor
   make the punctured root cover a connected cyclic torsor; orbit descent and normal
   integral closure give the intermediate root charts. The exponents divide n,
   hence are units. Both natural-language proofs and their nodes were read. For d=0
   the chart spectrum is empty; n=1 has only degree-one orbits. A unit g excludes the
   divisor branch, g=0 excludes the off-divisor branch, and the zero ring has no y.
   Searched LeanFinder, Loogle, and Mathlib using different queries, and the library
   with root/cyclic/splitting terms. Read the generic finite etale splitting module
   and the current prescribed-chart proof. No independent exact replacement found.
   Verdict: both statements true, needed, and strictly smaller branches.
4. Checked downward reduction, imports and the fixed unit record. Removed the
   circular prescribed-chart import, simplified the on-divisor branch to a direct
   witness return, and retained all baseline statement imports. No baseline proof_deps
   are dropped; none existed. The first worker's new off-divisor node no longer
   needs lem-weil-pbc-finite-etale-etale-local-split. The fixed tame-chart route is
   retained. Verdict: pass.
5. Read every delivered node against its Lean declaration. Corrected the item node's
   on-divisor proof dependency and the new helper's signature, source, proof,
   searches and blueprint ancestry. The proof_deps of each node is exactly the
   union of its proof steps' uses. Verdict: pass.

Changed: removed circular reuse of RootSplitCoverPrescribedCyclicCharts; added the
on-divisor helper and node with an explicit proof in words; simplified its assembly;
corrected the accounting from one added hole to two; simplified the off-divisor
proof plan to use δ directly and removed its unused local-splitting dependency;
updated DAG and this report.

## New nodes

lem-sbc-root-split-cover-away-divisor-charts, in
lean/Sheaf/AlgebraicGeometry/Morphisms/RootSplitCoverAwayDivisorCharts.lean:
the off-divisor branch, without regularity hypotheses, with d degree-one charts
and unit image of g. The node documents the punctured root neighborhood, transport
of the supplied
splitting, and polynomial evaluation.

lem-sbc-root-split-cover-on-divisor-charts, in
lean/Sheaf/AlgebraicGeometry/Morphisms/RootSplitCoverOnDivisorCharts.lean:
the on-divisor branch, with the original regularity hypotheses and g∈y.asIdeal.
The node documents the strict henselian connected cyclic torsor, orbit cover
classification, and descent to a pointed affine etale neighborhood. This branch
alone cannot prove the original statement for points outside the divisor.
