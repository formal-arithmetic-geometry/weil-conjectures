## What changed

Replaced the sole sorry in `AlgebraicGeometry.Scheme.exists_smooth_section_power_series_chart`
by a compiling proof from two smaller statements, imported only for the proof:
`Sheaf.AlgebraicGeometry.Morphisms.SmoothSectionCompletionChart` and
`Sheaf.AlgebraicGeometry.Morphisms.FlatPowerSeriesChartGenericImage`.
The existing signature and docstring are unchanged. The second reading removes redundant
direct public imports already publicly exported by Smooth. The proof constructs the base change,
lifts the section, composes the flat chart with the flat projection, derives both the
commuting square and origin equality, and constructs the required nonempty open using
Mathlib's Noetherian component theorem in an affine neighbourhood of the fibre.
The node's proof and dependencies now follow that Lean proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_smooth_section_power_series_chart`
(node `lem-sbc-smooth-section-power-series-chart`). Its own proof contains no sorry.
This is a decomposition, not an unconditional proof: one upper hole was closed and two
strictly smaller lower holes were added, for a net hole change of +1.

Every remaining hole in this delivery is a public named theorem in its own new module:

- `AlgebraicGeometry.Scheme.exists_smooth_section_completion_chart`
  (`lem-sbc-smooth-section-completion-chart`): construct the flat completion chart for
  a section over a single local base, with equality of the entire section morphism.
- `AlgebraicGeometry.Scheme.exists_flat_power_series_chart_generic_image`
  (`lem-sbc-flat-power-series-chart-generic-image`): for an already supplied flat chart
  over the base-changed scheme, identify the extended maximal-ideal point and show
  its image is a generic component point in an affine neighbourhood of the closed fibre.

Both have `:= by sorry`, source citations and complete proof sketches. No data definitions,
axioms, private holed helpers, or existing statements were added or changed.
All three modules compiled together cleanly through lcompile.py.

## No longer needed

Removed the redundant direct public import `Mathlib.AlgebraicGeometry.Noetherian`
from all three delivered modules. Removed `Mathlib.RingTheory.LocalRing.RingHom.Basic`
from the original module and the new generic-image module, and
`Mathlib.RingTheory.RingHom.Flat` from the original module. All three are already
publicly exported through `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; the exported
notions and instances remain available. These are direct-import removals, not pruning
of modules from the targets' import closure. No previously planned DAG node is unused:
the original node had an empty `proof_deps`. Both new proof imports are used.
The unit route (smooth affine chart, section-ideal completion, flat base change,
and the closed-fibre generic point) is retained.

## Where the brief, the DAG or earlier work was wrong

The original node gave a single long proof step with no named dependencies; there was no
existing completion-chart or generic-image interface to apply. Searches of Sheaf,
WeilConjectures, Mathlib and the full blueprint found no matching statement. Mathlib
contains flatness of Noetherian completion and flat going down, but not their assembly
with the power-series identification and the required scheme morphisms. LeanSearch
returned Internal Server Error; actual searches and supporting hits are recorded.

A crucial edge case checked during drafting is that flatness of a map to L alone does
not make the image of m_B P generic in the original closed fibre. For A a field,
B = A[y]_(y), L = affine one-space, n = 0, and the map x to y, the map to L is flat
but m_B maps to the closed point x = 0. The delivered generic-image lemma instead
requires flatness to L base changed to Spec B and compatibility with projection to B;
this makes the closed-fibre restriction flat, and excludes that example. The original
completion construction supplies exactly this stronger hypothesis. This is a correction
to an undelivered draft, not a dispute of the existing theorem.

The rank-zero case remains included throughout. For q the identity and n = 0 the generic
image reduces to the unique closed-fibre point, and for a positive-dimensional smooth
section the completion has the corresponding positive number of variables. No dense
open, depth bound, or global quasi-compactness was added. The nonempty-open construction
is performed in an affine neighbourhood, so it uses only local Noetherianity of the fibre.

## New nodes

`lem-sbc-smooth-section-completion-chart` states the section-compatible completion
construction over one base ring (Tags 0EYB, 05D5, 00MB). It drops the separate base-change
and generic-fibre conclusions and records Noetherian completion flatness as a Mathlib leaf.

`lem-sbc-flat-power-series-chart-generic-image` states the generic-image part for a
supplied flat chart over the changed base. It neither constructs a chart nor asserts a
section or an origin equality, and it leaves the nonempty-open construction to the proved
upper theorem. Its sketch includes coefficientwise reduction and flat going down.

Change record: `coord/changes/SmoothSectionPowerSeriesChart-public-imports.md`
for redundant public-import removal. No forced adaptations were needed.


## Second reading by R1

1. **Interfaces unchanged: pass.** Read the repository and sandbox modules side by
   side with `diff -u`. The original declaration
   `AlgebraicGeometry.Scheme.exists_smooth_section_power_series_chart` has exactly
   the same signature, universes, visibility and docstring. The initial changes
   were two plain proof imports and the replacement of its sole `sorry` by a
   tactic proof. There are no existing definitions, new hypotheses, weakened
   conclusions or forced adaptations. The import removal has the change record
   `coord/changes/SmoothSectionPowerSeriesChart-public-imports.md`. The additional import
   pruning below preserves all public availability through Smooth's public imports.

2. **Proof and axioms: pass as a decomposition.** All three modules compile locally
   in import order through `lcompile.py`. Scratch copies with `#print axioms` for
   each of the three declarations report exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The last is expected from the two reported lower
   holes; the original theorem is not an unconditional completed proof. The upper
   proof has no sorry. The only remaining sorries are the two public named
   theorems, each exactly `:= by sorry`. No definition, arbitrary data witness,
   axiom, unsafe/opaque declaration or foreign implementation occurs. The
   existential charts are destructured inside a theorem proof, not used to define
   an undetermined data object. Scratch files were removed.

3. **Split statements: pass.** Read the statements, docstrings and nodes against
   [0EYB](https://stacks.math.columbia.edu/tag/0EYB),
   [05D5](https://stacks.math.columbia.edu/tag/05D5),
   [00MB](https://stacks.math.columbia.edu/tag/00MB) and
   [00HS](https://stacks.math.columbia.edu/tag/00HS).
   For the completion lemma, the section gives a split augmentation on an affine
   neighbourhood of its closed-point value: every open in a local spectrum that
   contains its closed point is the whole spectrum. Smoothness makes the conormal
   finite locally free; locality makes it free. 05D5 supplies the augmented
   power-series identification, including rank zero; 00MB applies because the
   affine chart is finite type over Noetherian B. Taking spectrum and composing
   with the open immersion gives a flat morphism and the two asserted equalities.
   The whole-section equality is justified by augmentation compatibility, and is
   what the upper proof uses to obtain its pointwise origin equality.

   For the generic-image lemma, finite generation of the maximal ideal is what
   identifies the quotient of the series ring with the series ring over the
   residue field. This is a domain even for n=0, so the prescribed prime exists.
   The commuting square and locality put its image in the original closed fibre.
   Base change of t to the closed fibre is flat because t is flat **to the
   pullback scheme**. Projection along the residue field extension is also flat.
   Going down then sends the zero-ideal generic point to a minimal point of the
   original fibre. In an affine neighbourhood its singleton closure is a
   component. This does not assume that phi is flat and does not mistakenly apply
   flatness of the composite map to L to the scheme-theoretic fibre. Checked
   n=0 with q the identity, affine space with the zero section, and a nontrivial
   residue field extension. The example A=k, B=k[y]_(y), L=affine one-space,
   x mapping to y cannot violate the lemma because its induced morphism to
   L over B is not flat. Neither lower lemma restates the upper item: one
   constructs the chart without any generic image, the other takes a supplied
   chart and proves its generic image without constructing it or any section.

   Repeated searches using different words: LeanFinder queries for a smooth
   augmented algebra's formal neighbourhood and for flat maps of minimal points;
   Loogle `MvPowerSeries.map, Ideal.map`; msearch grep for adic-completion and
   power-series interfaces; direct rg over lean/Sheaf and the upstream
   WeilConjectures algebraic-geometry sources. No exact existing declaration was
   found. Loogle did find `MvPowerSeries.ker_map_of_fg`, a useful ingredient for
   the generic-image hole, not the whole statement. Its reported Mathlib module
   `MvPowerSeries.Ideal` is absent from this machine's pinned source tree, so it
   does not provide a locally usable immediate closure. The existing Mathlib
   formal-smoothness lifting, completion-flatness and flat-generalizing-map
   results also supply parts, not either whole lower theorem. Search calls are
   recorded in searches.jsonl. Both holes require substantial assembly, so no
   extra lower hole was introduced in attempting to close them.

4. **Route and pruning: pass after import repair.** Read
   dag/units/sk-prop-input-spreading.json, especially its completion paragraph,
   and the upper node's original empty proof_deps. The proof retains the smooth
   section, section-ideal completion, flat base-change projection, and closed-fibre
   generic-point route. No node in the unit's realized fields is bypassed (those
   fields currently contain empty lists). The categorical equalities follow
   directly from pullback.lift_fst/lift_snd and pullback.condition. The nonempty
   open is proved using the existing Mathlib Noetherian component theorem
   (NoetherianSpace.lean:203), rather than split off. Its hypotheses are obtained
   only on the affine open V: the fibre is locally Noetherian, and V is
   Noetherian. No global quasi-compactness of L or its fibre is silently assumed.
   Openness and nonemptiness of its image follow from the open embedding V.ι;
   specialization follows from singleton closure and continuity. Removed
   redundant public imports as listed under No longer needed. Both plain
   proof-only imports remain necessary.

5. **Node records: pass.** The existing node differs only in proof, proof_deps and
   proof_origin; its statement and Lean signature are unchanged. Its steps match
   the actual lift/completion construction, flat projection and origin equality,
   generic-image application, and proved affine Noetherian open construction.
   The two new nodes match their Lean statements verbatim, have separate modules,
   source/proof sketches, statement dependencies, creation records, blueprint
   ancestor/via records, three actually logged searches (LeanSearch unavailable,
   correctly recorded as unavailable), chapter/unit and complete Lean records.
   The cited completion-flatness and going-down Mathlib nodes say exactly what
   the sketches use. No circular reliance on the original chart theorem occurs.

**Changes made by the second reading:** removed redundant direct public imports of
Noetherian, LocalRing.RingHom.Basic and RingHom.Flat where present, corrected the
report's previous claim that all direct imports were necessary, and added this
review. Existing theorem statements and the working proof were left unchanged.
One original hole is closed, two lower holes remain added: decomposition with net
one additional hole, no target-closure module pruned.

Preflight initially required a change record for public-import pruning; added the
record with every module reported by downstream.py and current claim holders.
The same public dependency closure guarantees unchanged downstream statements.

An unchanged scratch copy of ClosedFiberPowerSeriesTest could not be checked:
its baseline SmoothClosedPointLocalSection.olean is absent from the local compiled
library. Removed the scratch copy. The delivered three modules compile cleanly;
the source public-import graph proves that the removed imports remain publicly
available, so this missing unrelated baseline artifact requires no adaptation.
