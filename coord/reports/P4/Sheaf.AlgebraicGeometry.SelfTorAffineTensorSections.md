## What changed

Proved `AlgebraicGeometry.exists_selfTor_affine_tensor_sections` with its original
signature and normalization unchanged. Added proof-only imports of
`Mathlib.LinearAlgebra.TensorProduct.Tower`,
`Sheaf.AlgebraicGeometry.SelfTorAffineChartSections`, and
`Sheaf.AlgebraicGeometry.LocallyQuasicoherentAffinePullbackSections`.

The first new module constructs the normalized A-linear chart-section equivalence
and proves that the open pushforward is quasi-coherent after restriction to U.
The second proves the B-linear pullback-section equivalence assuming quasi-coherence
only after restriction to U. Its private bijectivity argument follows the already
proved `ModulePullbackAffineSectionsBijective` argument, with the hypothesis reduced
to the one it actually uses: quasi-coherence on the canonical Spec A chart. It uses
the existing `affineChart_pullback_unit` and source-library `pullbackSpecΓEquiv`.
The item's proof tensors the chart equivalence with the B-linear identity of B,
composes the two equivalences, and computes the pure-tensor image explicitly.

Updated the item's proof, proof_deps and proof_origin to match this route. Created
DAG records for the two proved intermediate modules. Existing signatures, public
imports, definitions, and target statements remain unchanged. No adaptations or
change records are necessary.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_selfTor_affine_tensor_sections`
(`new-v2-self-tor-affine-tensor-sections`).

Also proved, with complete Lean proofs:

- `AlgebraicGeometry.exists_selfTor_affine_chart_sections`
  (`new-p4-self-tor-affine-chart-sections`).
- `AlgebraicGeometry.exists_locallyQuasicoherent_affine_pullback_sections`
  (`new-p4-locally-quasicoherent-affine-pullback-sections`).
- The private `tensorPullback_affine_sections_bijective_of_chart` in the latter
  module, which checks bijectivity by the canonical affine chart comparisons.

No sorry remains in the item's module or either new module. No holes were added or
split off: one hole closed, zero added. Empty U, empty inverse image V, and zero M
are covered by the proved isomorphisms; there is no choice of a point or nonempty
open. The geometric module construction is unchanged, and no data is chosen from
an unproved mere existence statement.

All three modules compiled individually through lcompile.py and together in import
order. The longest compile was approximately 43 seconds, below the 60-second limit.
The required deliver3.py dry run performs the declaration and axiom probes.

## No longer needed

No original import was removed: all three original public imports are preserved.
The new chart module imports only Mathlib.AlgebraicGeometry.Modules.Tilde; it already
publicly imports the quasi-coherent module API.

The item's former proof route no longer needs these dependencies:

- `lem-sc-tensor-pullback-open-square`, module
  `Sheaf.AlgebraicGeometry.TensorPullbackOpenSquare`.
- `lem-weil-pbc-module-pullback-affine-sections`, module
  `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, nor its proof module
  `Sheaf.AlgebraicGeometry.ModulePullbackAffineSectionsBijective`.
- `lem-weil-pbc-open-immersion-module-pullback-restriction` as a separate comparison:
  the proof uses restriction adjunctions and the canonical affine-chart unit
  equation directly. The restriction and tilde Mathlib APIs themselves remain used.

The former direct edges to `lem-weil-pbc-affine-tilde-gamma-adjunction` and
`pqf-def-affine-morphism` are also replaced by the new helper edges; both facts
remain used in the helper proofs and are not claimed as globally pruned.

The affine tilde-Gamma adjunction, affine-morphism property, tensor product, and
selfTorAffineSection remain required, in the new intermediate proofs or the item's
statement. Pruning here concerns this proof's dependency edges; these lemmas may
still be required elsewhere in the targets' closure. No unit statement or realized
step is bypassed: the unit record has no realized entry for this new node.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly avoids asserting that the chart open pushforward is
quasi-coherent on all of Y. Its listed affine-sections theorem has a global
quasi-coherence hypothesis and therefore cannot be applied directly to that
pushforward. Its already proved affine-chart argument only needs quasi-coherence
on Spec A; the new local comparison formalizes exactly that observation. The
normalized open-square comparison is consequently unnecessary here. There is no
statement dispute or change of mathematical meaning.

Read Stacks Tags 01I9 (affine associated-module pullback), 01I7 (associated modules
and their mapping property), and 0096 (pullback adjunction), together with the
existing Lean comparison implementations. The referenced local Stacks .tex files
are absent in this clone, so the public tag pages supplied the source text.

Mathlib searches: Lean Finder returned affine-space morphism APIs, not this
section comparison; Loogle confirmed `tilde.adjunction` and its unit isomorphism;
LeanSearch was unavailable with an Internal Server Error; msearch grep had no
hits for the three affine-chart APIs, while repository rg located the proved
`affineChart_pullback_unit`, `sectionsRestrictFromSpecLinearEquiv`, and
`pullbackSpecΓEquiv`. The exact queries and results are in searches.jsonl and in
both new nodes. The imported blueprint search for "affine sections" returned no
matching node. No new unproved theorem was needed.

## New nodes

`new-p4-self-tor-affine-chart-sections`, in
`dag/nodes/sec-picard-framework/new-p4-self-tor-affine-chart-sections.json`, records
the normalized chart section equivalence and local quasi-coherence, proved in
`Sheaf.AlgebraicGeometry.SelfTorAffineChartSections`.

`new-p4-locally-quasicoherent-affine-pullback-sections`, in
`dag/nodes/sec-picard-framework/new-p4-locally-quasicoherent-affine-pullback-sections.json`,
records the affine pullback section equivalence under the local quasi-coherence
hypothesis, proved in `Sheaf.AlgebraicGeometry.LocallyQuasicoherentAffinePullbackSections`.
Both are strictly parts of the original argument, and both are proved rather than
left as new work. There are no change records.

## Second reading by P4

1. Compared the item with the repository by diff: its original declaration
signature, docstring, definitions and public imports are preserved. Only proof
imports, elaboration options and the proof body are added. Restored the accidental
extra space before `:=` so the signature text is unchanged. The two other modules
are new; there are no forced adaptations or interface changes.

2. Read all three complete proofs and compiled the set in import order without
errors or warnings (50.1, 16.6 and 4.9 seconds). No delivered module contains
`sorry`, a new axiom, unsafe code, opaque declarations, extern or implemented_by.
The chart equivalence is built from the tilde unit and actual restriction maps;
the pullback map is built by TensorProduct.lift, and bijectivity is proved by
comparison to the standard pullback equivalence. Choice of the existing proved
adjunction is constrained by its sectionwise unit formula, not a witness chosen
from an unproved existence claim. The required delivery axiom probe checks every
declaration, including the private bijectivity helper.

3. There are no split-off holes. Checked the two proved helper statements against
[01I7](https://stacks.math.columbia.edu/tag/01I7),
[01I9(1)](https://stacks.math.columbia.edu/tag/01I9),
[0096](https://stacks.math.columbia.edu/tag/0096) and
[0097](https://stacks.math.columbia.edu/tag/0097). The chart helper uses the whole
chart, so its image is top; the pullback helper uses affineness only to make the
inverse-image open affine and uses quasi-coherence only after restriction to U.
Both formulas are normalized by the existing canonical adjunction unit. Empty U,
empty inverse image and M=0 introduce no missing hypothesis: all constructions
and bijections are valid without choosing a point. The chart normalization and
local pullback comparison are separate parts of the argument, not unproved
renamings of the item. Independently searched msearch grep for
`restrictFunctorAdjCounitIso|pullbackSpecΓEquiv`, Loogle for `restrictAppIso`,
and repository rg for affine section equivalences. The existing
ModulePullbackAffineSections theorem requires global quasi-coherence; its
bijectivity implementation was read and compared with the private local version.
The latter changes the hypothesis to exactly the chart quasi-coherence used by
pullbackSpecΓEquiv. No existing exact local normalized theorem was found.

4. Read from the item downward: TensorProduct.AlgebraTensorModule.congr tensors
the chart equivalence; the locally quasi-coherent comparison gives the other
equivalence; their formulas and rfl give selfTorAffineSection exactly. Read
SelfTorAffineSection, ModulePullbackAffineChartUnit, TensorPullbackAdjunction,
and the source-library PullbackTilde implementation. The unit theorem has no
global quasi-coherence hypothesis; the source-library comparison takes exactly
the quasi-coherence supplied on Spec A. Removed a redundant new public import
of Quasicoherent from the chart module, because Tilde publicly imports it. All
original public imports remain necessary for the item signature. Completed the
pruning report with the former direct tilde-adjunction and affine-morphism edges.
The unit sk-thm-picard-duality has empty realized statement and step entries;
no realized unit node is bypassed. No shorter existing normalized local route
was found.

5. Compared the item's node diff: only proof, proof_deps and proof_origin change.
Its three steps match the actual two comparisons and final pure-tensor
calculation. Read both new nodes: their union of step uses equals proof_deps;
chapter, unit, source, creation, blueprint provenance and search records are
present. Their hypotheses and conclusions match the Lean statements. Corrected
the new nodes' lean.statement fields to the actual multiline signatures, rather
than flattened text. Verdict: the proof and mathematical interfaces pass this
second reading; one original hole closed and none added.

Changes by the second reader: signature whitespace restored; redundant chart
import removed; pruning report completed; new-node Lean signatures recorded
verbatim. The proof arguments themselves required no repair.

Final verification: the deliver3.py dry run printed OK and passed preflight.
A scratch copy with explicit `#print axioms` for the item and both new public
helper theorems compiled; each reports exactly propext, Classical.choice and
Quot.sound, with no sorryAx. The delivery's all-declaration probe also passed.
The scratch copy was removed. Review class is CODEX because of the two new
modules and nodes; the required delivery tool will submit that reviewable set.
