## Worker report

The module `Sheaf.CategoryTheory.PartialCellularRootDescentExtension` defines the
canonical predecessor inclusion map for a lower subset and states
`CategoryTheory.partialCellularRootDescentExtension` with proof `sorry`.

The theorem binds a universe-level regular uncountable cardinal `τ` (`Fact τ.IsRegular`
and `Cardinal.aleph0 < τ`), a poset `I` with the explicit `<τ`-upper-bound condition
(including the empty subset), a diagram `F`, a colimit cocone `c` and its `IsColimit`
proof, a stage `i`, a well-founded tree index `T` with `HasCardinalLT T τ`, and an
`L`-cellular tree `D` rooted at `c.pt`. The hypothesis `hP` renders presentability of
each source `D.source t`; no presentability of targets, vertices, or roots is assumed.

The lower subset is `E : Set T` with `IsLowerSet E`; `DE` is the supplied tree rooted at
`F.obj i`. `hsource`, `htarget`, and `hcell` identify its specified cell data with the
restriction of `D`, using `eqToHom` transports. `γ` is the supplied natural transformation
to the root-changed restriction of `D`; `γpush` states its objectwise pushout squares,
`γtarget` and `γattach` state compatibility with both target and attaching legs. The
attaching compatibility uses `CellularTree.rootChangeMap` and the new
`CellularTree.predecessorInclusionMap`.

The conclusion supplies `j ≥ i`, a tree `D'` rooted at `F.obj j`, source/target
transport equalities `hs` and `ht`, and natural transformations `α` and `β`. The first
comparison is the prescribed root change from `DE` to `D'|E`; the second compares `D'`
to `D` over the colimit root. The conjunction renders, clause by clause, equality of
all specified cells, objectwise pushout squares on `E` and on `T`, compatibility with
both cell legs for `α` and `β`, and pointwise equality of the composite `α` then `β`
with the supplied `γ` (the canonical iterated-pushout identification).

Dependencies used: `CategoryTheory.CellularTree` from
`Sheaf.CategoryTheory.CellularTree`; `CategoryTheory.Limits.colimit` and
`CategoryTheory.IsFiltered` are the recorded Mathlib matches for
`def-weil-pbc-category-colimit`; `CategoryTheory.CellularTree.rootChangeMap` is the
recorded helper from `Sheaf.CategoryTheory.SmallCellularTreeDescent`.

Edge cases checked in the statement design: `E = T`, `E = ∅`, `T = ∅`, a single cell,
two incomparable cells, and an empty filtered subset. The explicit `hI` admits the empty
subset and the `Set.Iio` predecessor maps work for empty predecessor sets.

Searches made before writing: `leanfinder` for filtered cellular-tree descent (returned
only relative-cell-complex/small-object constructors; no exact match); `loogle` for
`CategoryTheory.IsCardinalPresentable`, pushouts, and filtered colimits (no exact match);
`grep` in Mathlib `CategoryTheory` for cellular-tree/root-descent names (no exact match);
`rg` in `WeilConjectures` and project `lean/Sheaf` (found the shared `CellularTree`,
`rootChangeMap`, and no existing target theorem). The node's recorded searches likewise
found no existing declaration. The module compiled cleanly with `scompile.py`.

## Worker self-check (recorded before independent maintainer review)

This is the resumed worker's self-check of the saved packet; no additional agent
was started. With the node and module open, I found and repaired a mismatch in
all three comparisons: the previous `γ`, `α`, and `β` were natural isomorphisms
before pushout. That incorrectly restricted the supplied partial descent and
strengthened the conclusion. Each is now a natural transformation under its
source root, with the stated `IsPushout` squares. By the universal property of
the chosen pushout, these are precisely isomorphisms AFTER objectwise pushout,
including their specified cocone legs. For example, pushing an identity-root
one-cell tree along a noninvertible root map need not induce an isomorphism
between its unpushed vertices. The previous signature excluded this case.
The informal node is unchanged. I also supplied its complete six-step proof plan
in the theorem docstring, retaining `sorry` as its sole theorem proof.

Clause check against the node: `Category.{v} A` and
`HasColimitsOfSize.{v,v} A` express small Homs and all small colimits in the
fixed small universe `v`, with unrestricted object universe `u`.
`Fact τ.IsRegular`, `hτ`, `hI`, `F`, `c`, `hc`, and `i` give exactly the cardinal,
filtered poset, diagram, fixed colimit, and fixed stage. `WellFoundedLT T`, `hT`,
`D`, and `hP` express the well-founded small tree and presentable cell sources.
`E`, `hE`, `DE`, `hsource`, `htarget`, and `hcell` are the given lower subtree
with the same specified cells. `γ` is natural under the root, `γpush` is its
pushout identification, and `γtarget`/`γattach` preserve the two cell legs.
The induced predecessor maps are the universal-property maps `rootChangeMap`
and `predecessorInclusionMap`, so they cannot be arbitrary maps.

For the conclusion, `j`, `hij`, `D'`, `hs`, `ht`, and the first conjunction
express the later stage, full tree, and unchanged specified cells. Naturality
and the undercategory morphism equations of `α` and `β` preserve every order
arrow and root arrow. The second through fourth conjunctions express the
pushout identification on `E` and both cell legs; the fifth through seventh
express the full pushout identification and both cell legs. The final equality
is the prescribed composite on `E`, with iterated-pushout coherence expressed
on its canonical legs. All transports are through the displayed endpoint
equalities. No endpoint or root presentability is imposed.

Rechecked empty `E`, full `E`, empty `T`, one cell with noninvertible root map,
and two incomparable cells. In particular the empty predecessor colimit is
in the undercategory and retains the root. Retained the original searches and
module; inspected the dependency signatures in `CellularTree.lean` and
`SmallCellularTreeDescent.lean` and Mathlib's cocone/filtered/presentability
interfaces. No new nodes, dependency repair, or informal statement correction
is needed.

Validation after the repair: `scompile.py Q151
lem-coef-partial-cellular-root-descent-extension <module>` compiled both the
sandbox and library-path forms cleanly (14.0 s and 9.4 s). The only postponed
proof is `CategoryTheory.partialCellularRootDescentExtension`.
I reopened [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Lemma A.1.5.11 on printed pp. 806--807, especially its construction data (a)--(c).
Its comparisons are explicitly after root pushout. The node's expanded relative
proof starts that construction at the prescribed lower subtree and uses only
cell-source presentability once the filtered root presentation is supplied.


## Second reading by Q151

Independent maintainer second reading, 2026-10-17, of immutable delivery
3170f10cfead1747495f4d8c5918f08f816adc6d. This reader did not write the delivery
or its earlier self-check. The previous self-check is retained above under its
accurate heading. I read the packet, immutable node and module, both statement
dependency records, the dependency declarations and their docstrings, the source
places, and the worker report.

Clause-by-clause reading:

- The fixed small universe is `v`. `A : Type u`, `Category.{v} A` and
  `HasColimitsOfSize.{v,v} A` allow large objects with small Hom sets and all small
  colimits; no equality of object and Hom universes is imposed.
- `τ : Cardinal.{v}`, `Fact τ.IsRegular` and `hτ` give the uncountable regular
  cardinal. `I : Type v`, its partial order and `hI` give precisely the small
  cardinal-filtered poset. The empty subset is included. `F`, `c`, `hc`, `i`
  retain the specified diagram, colimit cocone and starting stage.
- `T`, `PartialOrder`, `WellFoundedLT`, `hT` and `D` give the small well-founded
  cellular tree and its size bound. `hP` assumes presentability only of each
  source. It imposes no condition on the cell targets, roots or vertices.
- `E`, `hE`, `DE` give the prescribed lower tree. `hsource`, `htarget`, `hcell`
  keep its specified cells. `γ` is a natural map under the initial root;
  `γpush` identifies its root pushout with the restriction of `D`, and
  `γtarget`, `γattach` respect both cell legs. The predecessor comparison uses
  the actual colimit-induced maps, including the root leg.
- `j`, `hij`, `D'`, `hs`, `ht` and the first conjunction give the later stage
  and a full tree with the same cells. `α` and conjunctions two through four
  give the partial comparison after root change, preserving both cell legs.
  `β` and conjunctions five through seven give the full comparison after root
  change, again preserving both legs. Naturality gives every order arrow;
  being morphisms in `Under` gives the root equations. The last equality on
  `E` preserves the prescribed comparison, using the cocone identity for the
  composed root map and uniqueness of maps out of iterated pushouts.

I opened HTT Definition A.1.5.1, Notation A.1.5.2, Remark A.1.5.3 (printed
pp. 799-800) and Lemma A.1.5.11 (pp. 806-807; PDF pages 823-824). The relative
version starts its induction with the supplied lower tree; once the filtered
presentation is supplied, no accessibility of the ambient category or
presentability of its roots is used. Only the next cell source is needed for
the attaching-map factorization. The six-step node and theorem proof plans
supply the tail-colimit calculation and coherent limit-stage construction.
No informal statement correction or citer audit is required.

I read `CellularTree` and its canonical `subsetDiagram`, `subsetObj`,
`subsetMap`, `predecessorCocone`, `predecessorMap`, `IsGood`, and
`SmallCellularTreeDescent`'s `rootChangeMap` in the read-only group clone.
I also read Mathlib's colimit, `IsColimit`, `IsPushout`, `Under.map`,
`IsCardinalPresentable`, `IsCardinalFiltered`, `HasCardinalLT`, and `colimit.pre`
interfaces. `rootChangeMap` uses `colim.map` followed by `colimit.post`; it
does not assume that `Under.map` preserves colimits. The existing helper is
recorded in its owning node's declarations and adds no theorem hypothesis.

Independent `rg` searches for partial cellular extension, predecessor inclusion,
root-change, and tree descent in the group side library, upstream and Mathlib
found the shared interfaces and no exact target theorem. I checked the nearby
presentable-approximation statement and Mathlib `RelativeCellComplex`; neither
states extension of an arbitrary specified partial descent along this fixed
root presentation. The report/node retain the three kinds of discovery-search
records, including an honest LeanSearch service-unavailable result.

Edge cases: empty `T`; empty and full `E`; minimal vertices with empty predecessor
sets; branching/incomparable cells; noninvertible root maps; arbitrary
nonpresentable roots and targets; empty subsets in `hI`. Empty predecessor
colimits are taken in `Under`, hence retain the root. An empty `I` is excluded
by the node itself (filteredness includes the empty diagram), and by both `hI`
and the fixed `i`. No unintended universe restriction was found.

Landing repairs: the original second-reading section explicitly described a
worker self-check, so it did not establish independence (H11); this section
supplies the independent reading while preserving that history. The original
helper contained a local tactic proof of cocone naturality. To meet the strict
pilot no-local-proof gate (H6), its complete replacement uses the existing
`colimit.pre` on the order-preserving predecessor inclusion. This is the same
canonical construction: its coprojection at `s` maps to the coprojection at
`s.val.val`, and the morphism is in `Under`, so the root is preserved. No
postponed data, arbitrary map, new theorem, or new DAG prerequisite is introduced.
The sole theorem proof remains `sorry`.

Reproducibility: `scompile.py Q151
lem-coef-partial-cellular-root-descent-extension <immutable module>` passed both
sandbox and library forms (1.8 s each); the replacement passed again (1.8 s and
2.0 s). Both runs exited 0 with no diagnostics. This installed wrapper announces
server execution and reports a private side overlay; no direct ssh command,
global build or live-file edit was performed. The original and replacement
signatures both equal `lean.statement` verbatim. Both exported declarations
are listed, source/blueprint docstrings are present, all lines are within 100
characters, and `autoImplicit` is false. Full replacement module and this full
replacement report are supplied by the maintainer review. Verdict: FIX; no
mathematical correction is needed.
