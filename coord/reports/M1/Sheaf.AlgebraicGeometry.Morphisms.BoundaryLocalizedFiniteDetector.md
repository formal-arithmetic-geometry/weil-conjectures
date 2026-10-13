## What changed

Proved `AlgebraicGeometry.Scheme.boundary_localized_finite_detector` with its entire
signature unchanged. The proof uses actual section modules on finitely many basic
opens, sheaf separatedness on the open subscheme, and localization by common
denominators. Three proved private helpers handle common annihilators, localized
joint zero detection, and localized injective scalar multiplication.

Replaced the proof imports by
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme` (finite basic-open covers)
and `Mathlib.RingTheory.Localization.Module` (localized maps with extended scalars).
Updated the existing node's proof, proof_deps, and proof_origin to this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.boundary_localized_finite_detector`
(node `stage3-boundary-localized-finite-detector`). No holes were added or split off;
no sorry remains in the delivery. All three private helpers are proved.

The finite-set induction includes the empty cover. Sheaf separatedness gives S=0
in that case; the common denominator is 1. No finiteness of S or N is assumed.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`;
- `Mathlib.Algebra.Module.LocalizedModule.Exact`.

The detector no longer needs either original proof dependency:
- `pqf-lem-pushforward-qcoh`, module
  `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`;
- `lem-weil-pbc-affine-module-basic-open-localization`, module
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.

This is pruning of this item's route; other targets may still use these modules.
The unit record `sk-prop-input-spreading` has no realized nodes here, and its
statement and steps are preserved. The original public imports stay because the
unchanged statement uses their definitions.

## Where the brief, the DAG or earlier work was wrong

The planned identification of basic-open sections with P[1/f_i] and its appeal to
quasi-coherent pushforward were unnecessary. On each basic open the scalar f_i is
a unit in the section ring, which already gives injectivity for its section
module. Finite common denominators prove localized joint detection directly,
without a finite-product localization equivalence. The quasi-coherence hypothesis
is therefore unused by the proof but remains unchanged in the statement.

Mathlib searches were run with msearch.py (leanfinder, loogle, grep); the recorded
results supply localization API and related sheaf facts, rather than an exact
pre-existing detector theorem. Import direction was checked for the finite-cover
source module. No interface changes, forced adaptations, or new nodes.

Retry verification reproduced the delivery-tool failure. The submitted module
compiles with `lcompile.py` (exit 0) without warnings. The mandated
`deliver3.py --no-push` exits 1 with `COMPILES WITH WARNINGS (local)`:
its generated `BoundaryLocalizedFiniteDetector__probe.lean` line 211 exceeds
100 characters. It prints `SHEAF-PROBED 1` and no axiom or sorry findings,
but never prints OK. The generated probe originates in
`tools/stage3_delivery.py`; AGENTS.md section 3 forbids workers from editing
or working around these tools. A maintainer tool repair is still required.
No Lean proof, signature, node, or tool file was changed in this retry;
only this report was updated. No files outside the sandbox were changed.

The fourth retry independently read the complete saved proof and node route, then
recompiled the submitted module cleanly (12.3 seconds, exit 0). Its fresh dry run
again reported the generated probe at line 211:100 exceeding the line limit,
with `SHEAF-PROBED 1` and no axiom findings (14.1 seconds). The same tool defect
therefore persists. The proof and node were preserved unchanged for the reader;
no delivery was pushed and no tool workaround was attempted.

## Earlier second reading (a previous round; superseded)

Pending independent second reading. The proof preserves the target signature and the
unit route; no new statements or nodes were added.

## Second reading by M1

1. Compared the complete delivered module with the repository using diff and
   checked its existing theorem signature byte for byte. It is unchanged,
   including the quasi-coherence hypothesis and both conclusions. The four
   public imports are unchanged; both new imports are proof-only. No definitions
   or other public interfaces were changed. Verdict: pass.
2. Independently read every proof, compiled the delivered module with lcompile.py
   (exit 0, no warnings), then compiled a scratch copy with #print axioms for
   common_annihilator, localized_joint_zero, localized_smul_injective, and
   boundary_localized_finite_detector. All four use only propext,
   Classical.choice, and Quot.sound. No sorry or forbidden declaration is
   present. The section modules, scalar maps and localized modules are genuine
   constructions. Verdict: pass.
3. No statements were split off and no new public statements or nodes were added.
   Checked the private helpers: finite denominator products preserve membership
   in the submonoid; the empty finite family uses denominator 1; joint detection
   then forces the original module to be zero. The localization arguments do not
   assume finite generation. Verdict: pass.
4. Read from the target downward and checked the existing finite-cover theorem
   in WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme. Searched lean/ for
   alternative detector and finite-cover declarations and ran a fresh Loogle
   search for IsLocalizedModule.map with Function.Injective. The proof already
   uses the applicable map_injective lemma. The direct common-denominator route
   avoids an unnecessary localization/product equivalence. The two proof imports
   supply the finite cover and mapExtendScalars APIs; public imports supply the
   unchanged signature. No longer needed lists every old proof dependency and
   every removed import. Checked sk-prop-input-spreading.realized: no statement
   or step is assigned to this node, and the unit route is preserved.
   Verdict: pass.
5. Compared repository and sandbox nodes: only proof, proof_deps and proof_origin
   differ. The four recorded steps follow the actual finite-cover, separatedness,
   scalar-injectivity and common-denominator arguments; their union of node uses
   is the empty proof_deps. Statement, source, Lean signature and unit assignment
   are unchanged. No new-node fields are required. Verdict: pass.

Second reading changed only this report. The Lean proof and node were preserved.
The earlier generated-probe warning is a historical tool failure: the currently
installed deliver3.py explicitly filters messages located after the submitted
file's last line. No worker edited or bypassed a tool. Fresh delivery checks follow.
