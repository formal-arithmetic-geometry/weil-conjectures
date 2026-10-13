## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts`
with a compiling reduction to two independent intermediate statements. The original declaration,
its universes, hypotheses, conclusion and public imports are unchanged. Added two proof-only
imports: `StalkNormalizationGenericComparison` and `TraitGenericNormalizationCharts`.

The comparison theorem concerns only localization and generic-fibre identification; it assumes
neither invertibility of the group order nor finiteness of the normalization. The chart theorem
concerns one point of a smooth family over an actual DVR and its generic torsor; it contains no
global base, open model, boundary point or localization comparison. Neither theorem is the
original statement under another name. The main proof maps the invertible group order to the
stalk, transports finiteness across the comparison, constructs the family indexed by points,
proves joint surjectivity, and composes pullback isomorphisms while verifying their equality
over each affine base.

Added the two new modules and their nodes, and updated the original node's proof, proof_deps
and proof_origin. No definition, instance, target or existing statement changes. No adaptations
or change records are needed. The trait step of unit `sk-prop-input-spreading` is retained.

Validation: all three modules compile together through lcompile.py without warnings. The dry
run of deliver3.py is the final mechanical check. Sources read: Stacks 0EYJ, trait and local
reduction paragraphs; 0EYG, pointwise affine etale neighbourhood construction; 0EYH, normalization
and etale base change; 0307, localization of integral closure. Sources are available at
https://stacks.math.columbia.edu/tag/0EYJ,
https://stacks.math.columbia.edu/tag/0EYG,
https://stacks.math.columbia.edu/tag/0EYH and
https://stacks.math.columbia.edu/tag/0307.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_charts`
(node `lem-sbc-stalk-normalization-trait-charts`) by decomposition. There are no sorries left
in the item's module. Added exactly two lower holes:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_generic_comparison`
  in `StalkNormalizationGenericComparison`, node
  `lem-sbc-stalk-normalization-generic-comparison`.
- `AlgebraicGeometry.Scheme.GaloisCover.trait_generic_normalization_chart`
  in `TraitGenericNormalizationCharts`, node
  `lem-sbc-trait-generic-normalization-charts`.

Both are public named theorems with exactly `:= by sorry`, a source and a full argument in
their docstrings. This is one upper hole closed and two lower holes added, not a complete
sorry-free proof and not a net reduction in holes. There is no choice of data in a definition;
the main theorem eliminates the existential comparison only inside its proof.

## No longer needed

None. The original node had no proof dependencies and the original module had no proof-only
imports to prune. Its public imports remain for its existing statement. No old node or module
is claimed as pruned. The new generic chart module uses only normalization, smoothness,
Galois covers, DVRs and AdjoinRoot imports; it does not import global stalk geometry or the
finite-etale category. The comparison module does not import AdjoinRoot or geometrical
connectedness. None of the section-dependent extension or flatness modules is imported.

## Where the brief, the DAG or earlier work was wrong

The item's proof was a single non-elementary paragraph with no proof_deps; there were no
stated tame-ramification or localization comparison interfaces to apply. The two new interfaces
separate its localization argument from the intrinsic trait argument. Existing smooth-base-change
normalization results do not directly give localization to a stalk, since that map need not be
smooth. Existing flatness and section-unramified statements depend on the item or require a
section and cannot prove the charts.

The blueprint ancestor script returns None for this item: its created.item is a module name,
and its own blueprint.from points to the newly created trait-flat node. Following that node's
existing blueprint.from explicitly reaches `sbc-thm-spreading-finite-etale-galois`; the new nodes
record that ancestor and the intervening route. Searches of the whole blueprint for standard
tame, generic torsor and normalization localization found no matching imported statement.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as a successful negative search.
Loogle, LeanFinder and source searches found normalization tools but no exact theorem.

Edge cases checked mathematically: empty local total space requires no chart choices, and the
family type is then empty; empty component sets give the zero product ring; off the closed fibre
one takes e=1 and f=1. Positive residue characteristic is allowed because group order is a unit.
Disconnected generic torsors are handled by stabilizers. Geometrical connectedness is unnecessary
for the two intermediate statements, because their arguments are componentwise. No section,
rational point or splitting hypothesis was introduced. No excellence or completeness of the DVR
is assumed. Finiteness of the comparison's generic normalization is derived in the main proof
from finiteness of n, rather than added as an unproved comparison clause.

## New nodes

`lem-sbc-stalk-normalization-generic-comparison` records the comparison of the concrete stalk
pullback with relative normalization of a generic torsor, over the local total space. Its new
module is `lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationGenericComparison.lean`.
The source argument uses the punctured-spectrum identification and localization of integral
closure. It does not prove any standard chart form.

`lem-sbc-trait-generic-normalization-charts` records existence of a single affine etale standard
root chart at a point of a smooth trait family for a generic G-torsor with invertible group
order. Its new module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/TraitGenericNormalizationCharts.lean`.
Its remaining proof is the intrinsic tame ramification argument from 0EYJ and 0EYG/0EYH;
the global comparison and assembly of a jointly surjective family are proved outside it.

## Second reading by J3

1. Compared the existing module with the repository using diff. The only changes are
   two plain proof imports and the theorem body; the full existing signature and docstring
   are byte for byte unchanged. No other existing module, definition or target changes.
   The existing node changes only proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py without errors or warnings.
   Scratch copies with #print axioms show the main theorem uses only propext,
   Classical.choice, Quot.sound and sorryAx; both lower theorems show the same allowed
   axioms plus sorryAx.
   The only textual holes are the two reported public theorems, each exactly := by sorry.
   There are no definitions choosing unproved data and no forbidden declarations.
   The comparison witness is eliminated inside a proof. Verdict: pass as decomposition,
   with one hole closed and two added; not a sorry-free proof or a net hole reduction.
3. Read both new statements, their docstrings and nodes against Stacks 0EYJ, 0EYG,
   0EYH, 09EB, 0307, 03GE, 03GV and 035I. The comparison is a localization and torsor
   transport assertion, without chart conclusions or group-order assumptions. The
   chart assertion is intrinsic to a DVR family, without the global open model or
   localization comparison. These are independent parts of the original argument.
   At the closed fibre the regular divisor and invertible stabilizer orders give tame
   ramification; the single divisor equation supplies the common f. Away from it,
   e = 1 and f = 1 give split copies. Empty L is vacuous; m = 0 is a valid empty product,
   though a torsor over a nonempty generic fibre is not empty. Disconnected families
   and torsors are treated componentwise. No excellence, completeness or section is
   required. Repeated searches with different terminology found affine localization
   tools and smooth normalization base change, but no exact lower statement in
   Mathlib or either library root. Neither lower theorem can be closed by these tools
   alone in a few minutes. Verdict: pass.
4. Read the main reduction from the top down. It transports the finite structure map
   across beta, maps the group-order unit to the stalk, chooses pointwise charts,
   establishes joint surjectivity, and transports each chart isomorphism over its base.
   These steps are actual Lean proofs. No shorter available scheme comparison or tame
   chart theorem was found. The new imports are plain imports used by the proof; each
   new module's public imports support its statement. No old proof dependency or
   proof-only import existed to remove, so No longer needed is complete.
   The trait route of sk-prop-input-spreading is retained. That unit's repository
   realized record already has an empty statement list and empty lists for its steps;
   this is a pre-existing coordination gap, not a completed realization audit or a
   route change by this delivery. The unit record is outside this delivery's allowed
   files and is left to the maintainer. Verdict: pass, with that metadata gap reported.
5. Checked the node signatures against Lean, new-node sources, creation and blueprint
   records, and the union of uses against proof_deps. The main node records both and
   only the two new dependencies, with the elementary assembly following the code.
   Both lower nodes have the same natural-language argument as their docstrings.
   Verdict: pass.

Second reading changed the new comparison docstring and its node proof to specify an
affine neighbourhood of s, affine opens over it, and the qcqs flat-localization
argument for sections before applying integral-closure localization. This clarifies
an omitted affine-base qualification; no theorem statement or proof body changed.
Added independent search records to both new nodes and this review to the report.
