## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.stalk_normalization_etale_of_fibre_neighbourhood`
with a complete Lean proof from three new intermediate theorems. The existing signature,
visibility and docstring are unchanged. No existing definition, target, or other module
was adapted.

The proof constructs the local base A, its smooth pullback q, and the open V obtained
by pulling U back to Spec A. It proves pointwise that V is the punctured spectrum using
`Scheme.range_fromSpecStalk`, `Scheme.fromSpecStalk_closedPoint`, injectivity of the
stalk-spectrum map, hs and hmin. It proves equality of the two expressions for the
punctured total-space open from `pullback.condition`.

A proved private helper uses `Scheme.Hom.isPullback_resLE` and base-change stability
to transfer the assumed etaleness to the restriction of n. The fibre point in W is
identified with the local closed point by the same injectivity argument. A genuine
case split on the Krull dimension uses the existing `IsLocalRing.depth_two_of_normal`
in dimension at least two, and discrete extended-natural order in the remaining case.
The resulting purity cases apply to arbitrary finite normal covers, independently of
relative normalization. The normalization-specific certificate supplies just normality
and density; it does not assert etaleness.

Added proof-only imports of the three new modules. The new statement modules retain
proof-dependency imports for the normal-ring tools and flat local depth formula named
in their remaining proof plans. The trait and depth-two route of the blueprint unit
`sk-prop-input-spreading` is preserved.

The compiler initially spent its heartbeat budget repeatedly unfolding the chosen
pullback cone while elaborating unrestricted equality substitution. Explicit typed
`congrArg` and `Eq.mp` transport resolves this: the final assigned file compiles in
seconds, with the standard heartbeat and time limits.

## Proved and sorry left

Closed the original hole by decomposition:
`AlgebraicGeometry.Scheme.stalk_normalization_etale_of_fibre_neighbourhood`
(node `lem-sbc-stalk-normalization-fibre-purity`). There are no sorries left in the
assigned module; its private `etale_pullback_restrict` helper is proved too.

Added exactly three public theorem holes, each with proof exactly `by sorry`, a source,
a full proof in its docstring, a separate module and a new DAG node:

- `AlgebraicGeometry.Scheme.stalk_normalization_normal_and_dense`
  (`lem-sbc-stalk-normalization-normal-dense`), in `StalkNormalizationNormalDense`.
- `AlgebraicGeometry.Scheme.finite_normal_etale_of_trait_neighbourhood`
  (`lem-sbc-finite-normal-trait-purity`), in `FiniteNormalTraitPurity`.
- `AlgebraicGeometry.Scheme.finite_normal_etale_of_depth_two_neighbourhood`
  (`lem-sbc-finite-normal-depth-two-purity`), in `FiniteNormalDepthTwoPurity`.

This is a decomposition, not a sorry-free proof of geometric purity: one upper hole
closed, three lower holes added, net minus two before any closure pruning. The assembly
and localization/base-change glue are proved. No data is selected from any unproved
existence statement, and no definition or private declaration contains a sorry.

Edge cases checked against the statements and proofs: the finite etale scheme P may be
empty or disconnected; normality is stated for each local ring without requiring an
integral source. Density excludes the counterexample of an extra component supported
only on the closed fibre. When A has dimension zero, V is empty and density forces N
empty, so the low-dimensional theorem includes this case. Positive-characteristic
trait bases are allowed; purity uses unramifiedness already supplied by W, not tame
ramification or a group-order assumption. Nonexcellent normal bases are allowed because
finiteness of n is an explicit input, not deduced from a Nagata hypothesis.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.FlatLocalDepthFormula` from the assigned
module, and replaced the direct dependency `lem-weil-pbc-flat-local-depth-formula` by
the depth-two purity node. This is relocation, not pruning: that module and node remain
needed by `FiniteNormalDepthTwoPurity` and are imported there. No original node or module
is claimed to leave the targets' closure. No unit statement or realized step is bypassed.
No other original import was removed; the original public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The recorded proof dependencies supplied only the two commutative-algebra depth inputs.
They did not state normality and density of the concrete localized normalization, or
either scheme-level purity step. Thus the plan was not directly assemblable from its
recorded declarations. The three new statements isolate these genuine geometric parts;
the existing ring-depth results do not themselves prove the scheme-level assertions.

The generic-point-in-U hypothesis is not needed by this conditional proof once normality,
density, finiteness and boundary minimality are available: the dimension-zero empty-cover
case can be retained. The original hypothesis is kept unchanged and explicitly used to record that U
is nonempty; that fact is not needed by the conditional purity assembly. No statement is disputed or weakened.

The local literature checkout is absent on this machine. The sources were read from the
official Stacks pages: [0EYE](https://stacks.math.columbia.edu/tag/0EYE),
[0EYB](https://stacks.math.columbia.edu/tag/0EYB),
[0EY6](https://stacks.math.columbia.edu/tag/0EY6),
[0EYJ](https://stacks.math.columbia.edu/tag/0EYJ),
[035L](https://stacks.math.columbia.edu/tag/035L),
[035K](https://stacks.math.columbia.edu/tag/035K),
[035I](https://stacks.math.columbia.edu/tag/035I),
[0307](https://stacks.math.columbia.edu/tag/0307), and
[0BQL](https://stacks.math.columbia.edu/tag/0BQL).
The normalization normality argument uses that P is normal and locally Noetherian;
relative normalization of an arbitrary source is not automatically normal.

Mathlib searches were performed through msearch.py and recorded in searches.jsonl.
LeanSearch returned HTTP 500 for all three new statements and is recorded unavailable;
LeanFinder and source grep returned only normalization construction/dominance results
or etale-locus facts, not either purity theorem or the full normality/density certificate.
Searches of the whole blueprint for 0EYE, 0EYB and relative normalization normality found
no matching blueprint statement. The ancestor helper printed None because it follows
created.item IDs whereas this stage uses module names; the new ancestry is taken from
the existing item's explicit blueprint.from record, adding the current node to via.

## New nodes

`lem-sbc-stalk-normalization-normal-dense` records normality and density for the actual
stalk pullback of the relative normalization. It drops the boundary and neighbourhood
inputs entirely and has no etaleness conclusion. It follows 035L, 035K, 035I and 0307,
using the existing smooth-normal and etale-normal ring results as tools.

`lem-sbc-finite-normal-trait-purity` records the trait/dimension-zero part for an arbitrary
finite normal cover of a smooth geometrically connected local family. It assumes the
puncture, normality and density directly, and a dimension-at-most-one bound. It follows
0EYE and the trait paragraph of 0EYJ, then identifies the extension by integral closure.

`lem-sbc-finite-normal-depth-two-purity` records the depth-two part for the same general
finite-normal-cover setting, with depth at least two. It applies 0EYB to the union of
the punctured open and W, then identifies the extension by its generic algebra. The
flat local depth formula remains a proof dependency here. The normal-ring and flat-depth
nodes are generic algebra tools; their use preserves the spreading unit's purity route.
No change record is needed because no existing interface was changed.

## Second reading by C1

1. Compared the delivered module with the repository by diff and checked the original
   theorem signature byte for byte, including its visibility, hypotheses and let
   instances. Its docstring is unchanged too. The other three modules are new. No
   existing definition or statement changes and no change record is required. Pass.
2. Compiled all four modules locally in import order through lcompile.py: no errors
   or warnings. Read every proof and scanned the source: the only three sorries are
   the public named theorems listed above, each exactly `by sorry`; there are no
   definitions, forbidden declarations or witness selections in these modules.
   Scratch copies with #print axioms show propext, Classical.choice, Quot.sound and
   sorryAx for the main theorem, only the three permitted axioms for the private
   helper, and the same three permitted axioms plus sorryAx for each new theorem hole. Pass as a decomposition,
   not a proof without sorry.
3. Read the split statements and their docstring proofs against Stacks
   [0EYE](https://stacks.math.columbia.edu/tag/0EYE),
   [0EYB](https://stacks.math.columbia.edu/tag/0EYB) and
   [035L](https://stacks.math.columbia.edu/tag/035L). The first two isolate the
   dimension cases and the third normality/density, rather than restating the
   original item. The fibre-neighbourhood assumption ensures the closed fibre is
   nonempty; its smoothness and geometric connectedness make it integral. Density
   rules out a vertical normal component, and in dimension zero forces the source
   to be empty. Empty and disconnected finite covers and nonexcellent bases do not
   contradict these conditional statements. Each new hole has a matching node,
   source and complete proof in words. Repeated searches using the different terms
   "extension of finite etale covers", "Hartogs", "unramified" and "normal stalk",
   through msearch.py LeanFinder/Loogle/grep and rg on the library. Mathlib's dominant
   normalization map and the upstream isIntegrallyClosed_stalk_normalization are
   partial tools; the latter requires an integral source, while PA may be empty or
   disconnected. Neither supplies the new certificate or either purity case. No
   exact duplicate or split statement closable in a few minutes was found. Pass.
4. Read the main proof from the top: it genuinely proves the puncture identification,
   base-change restriction, closed-point comparison and dimension dichotomy. All
   three new imports are proof-only. The new statement modules use public imports
   for their signatures and private imports for their recorded unfinished proof
   plans. The original FlatLocalDepthFormula dependency is fully accounted for in
   No longer needed as relocated, not pruned. The unit sk-prop-input-spreading and
   its realized fields are unchanged; both trait and depth-two cases remain. Pass.
5. Checked every node's verbatim Lean statement and that proof_deps is the union
   of the uses in its proof steps. Read proof_origin, source, ancestry, creation
   records and all three search records of each new node. The existing node's
   revised proof follows the actual assembly; the new nodes describe the three
   remaining mathematical obligations. Pass.

Second reading changed this report only: added the independent review and its
verification evidence. The Lean proofs and node records required no repair. One
original hole is closed by decomposition, three holes are added, and no module is
claimed pruned (net minus two before closure pruning).
