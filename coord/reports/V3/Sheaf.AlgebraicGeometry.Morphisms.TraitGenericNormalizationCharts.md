## What changed

Replaced the earlier sandbox attempt with a genuine reduction of
`Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts`.
The original theorem's signature and docstring are unchanged. Its two proof-only imports
are now `TraitGenericRootModel` and the existing `NormalizationDenseOpen`.

The new geometric input describes the generic torsor as a dense open of the concrete
product root scheme and asserts normal domain stalks. It does not mention normalization.
The main module proves finiteness of the product root morphism from monicity and finite
products, derives local Noetherianness by smooth/etale/finite ascent, and identifies its
relative normalization by an explicit pair of inverse maps. The private helper
uses the existing dense-open theorem, `normalizationDesc` and `normalization.hom_ext`.
Smooth normalization base change then gives the required chart over Spec R.
The existing finiteness assumption on the normalization is retained, although this route
proves the conclusion without using it. No public data definition or target was changed.

Both modules compile together through lcompile.py without errors or warnings.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Scheme.GaloisCover.trait_generic_normalization_chart`
(node `lem-sbc-trait-generic-normalization-charts`). The proved private helper
`normalization_iso_of_dense_open_model` has no holes.

Added one hole:
`AlgebraicGeometry.Scheme.GaloisCover.trait_generic_root_model`
(node `lem-sbc-trait-generic-root-model`, module `TraitGenericRootModel`).
This is a decomposition: one upper hole closed, one lower geometric hole added,
net zero holes closed. The remaining lemma supplies punctured root models and their
normality, whereas the normalization comparison, integrality, local Noetherianness,
and base-change assembly are proved in Lean. It neither asserts nor assumes the
original normalization-chart conclusion.

The existing dense-open normalization theorem is reused with its existing dependency
chain. No holes were added to that chain.

## No longer needed

No import or dependency of the repository's original module was pruned; its five public
imports are required by its existing statement and are preserved.

Discarded the predecessor's sandbox-only modules `TraitGenericNormalizationNeighborhood`
and `TraitGenericNormalizationRootData` and nodes
`lem-sbc-trait-generic-normalization-neighborhood` and
`lem-sbc-trait-generic-normalization-root-data`. Neither is imported or delivered.
These were never part of the repository baseline, so this is not claimed as ledger pruning.
No additional DAG modules are required by this proof beyond the new root model and the
existing `NormalizationDenseOpen` and its dependencies. In particular
`FiniteNormalDenseOpenIso` and `NormalizationDominantLift` were read but are not imported.

## Where the brief, the DAG or earlier work was wrong

The predecessor's `trait_generic_normalization_root_data` asserted root decomposition on
EVERY chosen affine etale neighborhood. That is false: the neighborhood must be chosen
to obtain the tame local form. [Stacks 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
asserts existence of a suitable etale neighborhood, not the universal assertion.
It also left the elementary existence of an affine open neighborhood as a new hole,
did not update the original node's proof, and wrote its own fictitious second reading.
All these defects have been removed. The actual second reader's section is left to them.

The original DAG had no named proof dependencies for its long geometric paragraph.
The new dependency isolates the local root-model construction; the rest is actual Lean
assembly using existing results. The unit's trait-case route is preserved, with no
section, connectedness or rational point added.

Checked the local model against
[Stacks 0EYG](https://stacks.math.columbia.edu/tag/0EYG) and
[0EYH](https://stacks.math.columbia.edu/tag/0EYH): the generic cover gives punctured
root rings, and the full root rings have regular local rings along the divisor and
are etale away from it. The new lemma covers empty and disconnected models: m=0 gives
the zero product ring, empty scheme and dense empty open; off the divisor use f=1 and
exponents one. Positive invertible exponents are essential and retained. No global
connectedness assumption is used. The existence witnesses are eliminated only within a
proof; no data is defined by choosing from an unproved existence theorem.

## New nodes

`lem-sbc-trait-generic-root-model`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-trait-generic-root-model.json`, records
`AlgebraicGeometry.Scheme.GaloisCover.trait_generic_root_model` in
`lean/Sheaf/AlgebraicGeometry/Morphisms/TraitGenericRootModel.lean`.
Its source is Stacks 0EYJ/09EB/0EYG/0EYH, with complete construction and normality
arguments in the node and docstring. LeanSearch returned an Internal Server Error;
LeanFinder, Loogle, Mathlib grep, searches of both library roots and the blueprint
found no existing punctured normal-root-model theorem. The recorded three search kinds
reflect the actual tool results, including LeanSearch's unavailability.

The original node now records the new geometric dependency and
`lem-sbc-normalization-dense-open`, together with the proved universal-property and
smooth-base-change steps. No change record or forced adaptation is needed: all existing
public signatures and public imports are preserved.

## Second reading by V3

1. Compared the delivered chart module with the repository using diff and a literal
   signature comparison. Verdict: the existing theorem signature is byte for byte
   unchanged after restoring the indentation of its final line; its docstring and all
   five public imports are unchanged. No definitions or other modules were adapted,
   and no interface change record is required.

2. Compiled both delivered modules in import order with lcompile.py, without errors
   or warnings. Scanned for prohibited declarations and all sorry occurrences: the
   only textual hole is the named public trait_generic_root_model theorem. Scratch
   copies with #print axioms show only propext, Classical.choice and Quot.sound for
   normalization_iso_of_dense_open_model; the chart and root-model theorems also use
   sorryAx, as expected from the explicitly open geometric lemma. Verdict: valid
   reduction, not an axiom-free completion. No data definition chooses a witness from
   the new existence theorem: its witnesses are eliminated inside the chart proof.

3. Read the new lemma, its node and its full natural-language proof against
   [Stacks 0EYG](https://stacks.math.columbia.edu/tag/0EYG),
   [0EYH](https://stacks.math.columbia.edu/tag/0EYH), and the trait paragraph of
   [0EYJ](https://stacks.math.columbia.edu/tag/0EYJ). Verdict: true geometric input.
   The neighborhood is existential, not universal. Over the closed fibre, the root
   coordinate is a nonzerodivisor with regular quotient; away from it the derivative
   is invertible, proving regularity and normality. The punctured open is dense.
   Checked exponent one, the off-divisor choice f=1, disconnected smooth families,
   empty L and the empty product. In a nonempty chart a torsor is surjective, so the
   construction does not incorrectly require an empty product there. Repeated
   LeanFinder, Loogle and Mathlib grep with different queries, and searched both Lean
   roots; no matching construction is available. Recorded these searches in the new
   node. This remaining geometric input cannot be closed by a short available lemma;
   it is strictly the local-model part of the argument, with no normalization in its
   conclusion. The finiteness, normalization comparison and base change are actually
   proved in the chart module. One hole closed and one added remains a decomposition
   with net zero, not a completed geometric proof.

4. Read the proof from the chart downward and compared other normalization comparison
   lemmas. The dense-open theorem plus Mathlib's universal property is a direct route;
   finite_normal_iso_of_dense_open would additionally require normality of the other
   source and a common base open. Verdict: no shorter available route found. Both
   added imports in the chart module are proof-only. Removed the unused public import
   Mathlib.AlgebraicGeometry.Morphisms.Integral from the new root-model module and
   recompiled. The original node had no proof_deps, so there are no old dependency
   nodes to prune. The trait-case tame root-chart route of sk-prop-input-spreading is
   preserved; its realized arrays are empty in the repository, and this delivery
   neither invents entries nor bypasses any realized node. No baseline module pruning.

5. Compared both node records with the declarations and the actual Lean proof.
   Verdict: the new node contains the required source, searches, creation/blueprint,
   chapter/unit, Lean signature and proof fields; the existing node's proof_deps are
   exactly the new local-model node and the existing dense-open normalization node.
   Its proof describes the finite-algebra instance, Noetherian ascent, explicit inverse
   construction and smooth normalization base change as written. Original statement
   fields are unchanged.

Changes made by this reader: restored literal signature whitespace, removed the unused
public Integral import from the new module, recorded independent searches, and added
this review. No theorem body or remaining statement needed mathematical repair.
