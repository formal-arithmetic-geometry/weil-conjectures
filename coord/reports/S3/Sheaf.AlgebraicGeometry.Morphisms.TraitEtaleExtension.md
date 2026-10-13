## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_trait_neighbourhood`
with a complete Lean reduction. The original public signature and all public imports
are unchanged. The proof handles a field by constructing the empty open subscheme,
proves the nonfield normal local dimension-at-most-one base is a DVR using Mathlib,
and applies the new DVR purity theorem for the cover and its restriction isomorphism.

Three private helpers are proved: `smooth_normal_stalks` transfers normality through
smooth affine charts and prime localizations using `RingHom.Smooth.isNormalRing`;
`dense_puncture` uses a nonempty open in an irreducible spectrum and
`Dense.preimage` along a smooth open map; `trait_isDVR` uses the DVR TFAE.
Normality and density of the extension are proved from its smooth composite to
Spec A, so they are absent from the remaining purity statement.

Added `Sheaf.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity`, containing only
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_dvr_neighbourhood`.
It assumes a genuine DVR and concludes only finite etale extension with a compatible
restriction isomorphism. Unlike the original theorem, it has no field case, no
normal-stalk conclusion, no dense-puncture conclusion, and no qcqs assumption on q.
It is strictly the purity part of the original argument, not the original statement
with repackaged hypotheses. Updated the parent node's proof and dependencies, and
added the node of this remaining step. No definitions or existing signatures changed.

Both delivered modules compile together through lcompile.py with no errors or warnings.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_trait_neighbourhood`
(node `lem-sbc-trait-etale-extension`). No sorry remains in the item module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_dvr_neighbourhood`
(node `lem-sbc-dvr-punctured-cover-purity`, new module
`Sheaf.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity`). Its proof is exactly
`:= by sorry`, with the source and complete geometric argument in its docstring.

This is one decomposition, not a sorry-free proof of the geometric extension theorem:
one original hole closed, one strictly smaller hole added, net zero holes from these
two declarations. The field case, DVR criterion, chart/stalk normality, and density
are now actual Lean proofs. Existing holes reachable through SmoothNormalRing are
neither changed nor duplicated.

## No longer needed

Removed the proof imports `Mathlib.AlgebraicGeometry.Noetherian` and
`Sheaf.RingTheory.EtaleNormalRing`. The parent proof no longer needs node
`lem-weil-pbc-etale-over-normal-ring-normal` or its module
`Sheaf.RingTheory.EtaleNormalRing`: composing the etale p with smooth q is smooth,
and the smooth normality theorem suffices. No other original dependency was pruned.
These are local route removals; other target branches may still use those modules.
All original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The original proof paragraph contains a genuine purity step without a separate
Lean dependency: its only two proof dependencies concern ring normality. Those ring
lemmas do not produce a finite etale cover. The new node isolates that geometric
step. This is a gap in the dependency plan, not a disputed mathematical statement.

A simpler density argument works here: for a nonfield domain the puncture is a
nonempty open of an irreducible spectrum, and smoothness is open. There is no need
to formalize the uniformizer nonzerodivisor/component argument merely for density.
The existing statement is unchanged, and the unit's trait/purity route is preserved;
`dag/units/sk-prop-input-spreading.json` has no realized node bindings to bypass.

Read Stacks Tags 0EYE and 0EYJ on their official pages. The new theorem is the trait
purity application in the first two paragraphs of 0EYJ, using 0EYE. Checked the
edge cases: the original field case has empty V and is proved by an empty E; the
new DVR theorem excludes fields; the empty punctured cover is permitted by purity;
N may have vertical components, since only its restriction and its etale model near
the special-fibre generic point are used; E is not assumed integral or connected,
and normality is proved stalkwise. An empty L cannot meet the given x hypothesis.
The DVR purity theorem does not require q quasi-compact or quasi-separated, since
local Noetherianity follows already from its smoothness over the DVR.

Searches: LeanFinder returned only smooth-chart/locus and etale-implies-smooth
results; msearch grep found no purity extension theorem in Mathlib; rg of both
library roots found only this parent and its importers or stronger spreading
statements; blueprint searches for 0EYE and regular Cartier returned no existing
blueprint node. LeanSearch was unavailable (Internal Server Error). Loogle's DVR
query returned the standard Mathlib DVR class and TFAE-related tools used in the
proved base reduction.

## New nodes

`lem-sbc-dvr-punctured-cover-purity`: the genuine-DVR purity extension step, with
normality and density removed and proved in the parent. Source: Stacks Project
Tags 0EYE and 0EYJ, trait proof. Module:
`Sheaf.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity`. The full source proof,
three search kinds (including LeanSearch's service failure), inherited chapter/unit,
and blueprint ancestry are recorded. No change record or forced adaptation is needed.

## Second reading by S3

1. Interface preservation: PASS. Compared the delivered TraitEtaleExtension module
   with the repository using diff and checked its existing theorem signature
   byte for byte. The existing docstring, public imports, hypotheses, conclusion,
   and visibility are unchanged. The only added declarations in that module are
   private proved helpers. There are no definition changes or change records.
2. Proof and axioms: PASS as a decomposition. Compiled both modules in import
   order through lcompile.py without errors or warnings. Scanned both sources:
   exactly one sorry, in the named public DVR purity theorem, and no forbidden
   declarations or attributes. Compiled scratch copies with #print axioms for
   the main theorem, all three helpers, and the new theorem. The density and DVR
   helpers use only propext, Classical.choice, Quot.sound. The normal-stalk helper
   and main theorem additionally use sorryAx from existing SmoothNormalRing
   dependencies; the main theorem also depends on the new DVR purity hole.
   There is no arbitrary witness chosen in a definition: all E and p witnesses
   are unpacked only within an existential theorem proof.
3. Split statement: PASS. Independently read https://stacks.math.columbia.edu/tag/0EYE
   and https://stacks.math.columbia.edu/tag/0EYJ. The special fibre is a nonempty
   connected regular locally Noetherian scheme, hence integral. The open W
   contains its generic point; the given finite etale model there supplies
   unramifiedness at the unique codimension-one point in the special divisor.
   This is precisely the purity hypothesis. Local Noetherianity needs no qcqs
   assumption. Checked empty covers, disconnected covers, vertical components
   of N outside the relevant open, and the excluded field case. The new theorem
   has a complete source proof and matching node, and is strictly the purity
   part: the field case, DVR criterion, normality and density are discharged
   separately by actual Lean proofs. It is not a renaming of the original hole.
   Independently searched msearch grep for unramified|ramification|CartierDivisor
   and LeanFinder for extension without ramification at height-one primes;
   results concern algebraic etale loci and arithmetic ramification, not this
   extension. Searched both Lean roots for competing geometric purity results;
   the relevant stronger statements are downstream importers, so cannot supply
   a shorter route. The remaining purity formalization is not a few-minute hole.
4. Route and pruning: PASS. The reduction follows the shortest available route
   through Mathlib's DVR TFAE, initial empty schemes, dense open subsets and
   openness of smooth maps, using the existing smooth-normality theorem only
   where needed. Proof-only imports have plain import visibility. The removed
   Noetherian and EtaleNormalRing imports are reported; the only removed original
   proof dependency is lem-weil-pbc-etale-over-normal-ring-normal. All original
   public imports remain. The unit sk-prop-input-spreading has empty realized
   bindings and its trait/purity argument is preserved.
5. DAG agreement: PASS. Read both delivered nodes, the repository parent node,
   its two original dependencies, the localization-normal-domain Mathlib match,
   and the unit. The parent proof and proof_deps describe the four actual steps
   and the dependency union. The new node's statement matches its Lean signature;
   it has its source, proof steps, dependency union, proof_origin, search records,
   split status, creation record, blueprint ancestry, chapter, unit and Lean record.

Second reading changed only this report, adding the independent checks and
verdicts. No Lean or node repair was necessary. One original hole is closed and
one smaller hole is added: net zero, a decomposition rather than a completed
sorry-free proof of the extension theorem.
