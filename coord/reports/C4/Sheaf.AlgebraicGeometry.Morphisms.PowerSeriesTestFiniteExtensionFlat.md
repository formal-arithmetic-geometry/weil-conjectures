## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.flat_of_power_series_depth_two_finite_extension`
with a compiling assembly of finite etale extension existence, depth-two extension uniqueness,
and Mathlib's flatness instances. The existing signature and public imports are unchanged.
Added proof-only imports of `Mathlib.RingTheory.MvPowerSeries.Equiv`,
`Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesFiniteEtaleExtension`, and
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness`.
The first supplies Noetherianity of the spectrum for the uniqueness step.
Updated the item's node proof and dependencies to match the Lean proof.
All three sandbox modules compile together in import order through lcompile.py.

Read Stacks https://stacks.math.columbia.edu/tag/0EYA and
https://stacks.math.columbia.edu/tag/0EY6. The former gives extension existence;
the latter's converse proof of (2) gives uniqueness using only source boundary depth.
The reduction follows the existing item's documented route and preserves the unit route.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.Scheme.flat_of_power_series_depth_two_finite_extension`
(node `lem-sbc-power-series-test-finite-extension-flat`). No direct sorry remains in the item.

Added two named holes, each in its own module:

- `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_power_series_open`
  (node `lem-sbc-power-series-finite-etale-extension`).
- `AlgebraicGeometry.Scheme.iso_of_finite_depth_two_extensions`
  (node `lem-sbc-depth-two-finite-extension-uniqueness`).

This is a decomposition: one hole closed and two added, not a proof without remaining
assumptions. The first lemma starts with a cover over V and produces an extension;
it does not assume or assert a property of the supplied F in the original theorem.
The second is independent of power-series rings, etaleness, and base depth, and only
compares two finite extensions. The item genuinely combines the two results and
transports flatness along the resulting isomorphism. No data definition was added.

## No longer needed

None. The original node had no proof-dependency imports to prune. Existing public
imports supply the unchanged statement and remain. All three new proof-only imports
are used. No existing node or module is made unnecessary by this decomposition.

## Where the brief, the DAG or earlier work was wrong

The node's proof_deps was empty although its docstring invoked extension existence
and uniqueness. Searches through the DAG and Lean library found the existing
DepthTwoFiniteExtension theorem asserts existence but not uniqueness or power-series
purity; it cannot alone close this hole. Neither new lemma duplicates it.

The uniqueness argument of 0EY6(2) only needs locally Noetherian base and the two
source boundary depth conditions. Its base depth and etaleness assumptions are used
to construct the canonical extension, not in the converse uniqueness proof.
For U equal to L, the restriction is the given isomorphism. For U empty, depth two
at every source point forces both finite sources empty: a nonempty locally Noetherian
scheme has a minimal point whose stalk has dimension zero and hence depth zero.
This rules out hidden components supported in the missing locus.

For power-series extension, V equal to T and the empty cover are included. If V
contains the closed point of the local power-series spectrum, V is T, so this case
is handled before identifying the zero-section slice with the punctured spectrum.
The prime m_B R has contraction m_B and its localized coefficient map is flat local,
hence faithfully flat; this justifies the descent detail omitted in 0EYA.
No excellence, domain, smoothness, or section hypothesis was added.

LeanSearch returned Internal Server Error for both searches; this is recorded as
unavailable. LeanFinder and source grep returned no matching theorem. Blueprint
searches for finite depth, power series, 0EYA and 0EY6 found no matching imported
blueprint statement. The ancestor helper prints None because the item's created.item
is a module; the new nodes inherit the item's explicit recorded blueprint ancestor
sbc-thm-spreading-finite-etale-galois and its via chain instead.

## New nodes

`lem-sbc-power-series-finite-etale-extension`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesFiniteEtaleExtension.lean` states
essential surjectivity in 0EYA with the boundary depth of the canonical extension
from 0EY6. Its docstring expands the descent at m_B R and includes the full-open case.

`lem-sbc-depth-two-finite-extension-uniqueness`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/DepthTwoFiniteExtensionUniqueness.lean` states
the comparison consequence of the converse proof of 0EY6(2), with its finite-algebra
depth comparison, Hartogs algebra identification, and affine reconstruction explained.
No change record is needed: existing statements and interfaces are unchanged.

## Second reading by C4

1. Compared the delivered item with the repository using diff. Its existing theorem
   signature, docstring, visibility, and public imports are byte for byte unchanged.
   Only the proof and three proof-only imports differ. The other two modules are new;
   no existing definition or target statement changes. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py (2.6, 2.9, and 2.7 s).
   Separately compiled scratch copies with #print axioms for all three declarations:
   each reports only propext, Classical.choice, Quot.sound, and sorryAx.
   The item has zero direct holes; each new public theorem has exactly one whole-proof
   sorry with its matching node and complete sourced docstring. There are no data
   definitions, forbidden declarations, or arbitrary witness constructions. Verdict:
   valid assembly with two remaining assumptions, not a completed axiom-free proof.
3. Read Stacks 0EYA, 0EY6, 0AUK, and 0E9I directly. The power-series lemma is the
   essential-surjectivity argument plus the canonical extension's boundary depth.
   The uniqueness lemma follows from coherent finite direct image algebras, finite
   algebra depth comparison, and canonical Hartogs restriction; base depth and
   etaleness are unnecessary for this comparison. Checked full-open and empty-source
   cases, the empty-open uniqueness case, and the proper-open zero-section slice.
   For V containing the closed point, locality forces V to be the full spectrum;
   otherwise its zero-section slice is the punctured spectrum. At m_B R, the flat
   local map B -> R_(m_B R) is faithfully flat, so the descent argument is valid.
   Neither new statement restates the item's flatness conclusion. Independent
   LeanFinder searches used coherent-algebra reconstruction and formal closed-fibre
   extension terminology; no exact matches resulted. Loogle confirms the Noetherian
   instance used in the item. Source searches located DepthTwoFiniteExtension,
   DepthTwoHartogsAlgebraComparison, and FiniteStructureAlgebraDepth: they do not
   assert either new statement, and the last transfers depth in the opposite
   direction. No split-off hole has a short direct closure from these declarations.
   Verdict: true, needed decomposition; one closed hole and two added, net minus one.
4. Read the item top downward and checked each import against its use. Equiv supplies
   the Noetherian instance for uniqueness; both new theorem imports are needed.
   The original proof_deps is empty, so the No longer needed section is complete.
   Read dag/units/sk-prop-input-spreading.json: its existing realized lists are empty;
   this delivery preserves them and the depth-two extension/local computation route.
   No unit or chapter node is bypassed. Verdict: pass, with the baseline unit mapping
   incompleteness recorded here rather than silently claiming populated realizations.
5. Checked each node's lean.statement against the exact Lean signature and each
   proof_deps against the union of its proof steps' uses. All agree. The existing
   node changes only proof, proof_deps, and proof_origin. Both new nodes have source,
   searches, creation, blueprint ancestry, chapter, unit, and full Lean records.
   Verdict: pass.

Second reading changed only this report: added the independent checks, axiom results,
edge-case verdicts, and the explicit net-hole count. No Lean or DAG repair was needed.
