## What changed

Repaired Sheaf.Paper.CechCupSignedAxisPairing at the supplied broken tip.
Replaced the public CechCupProduct import with CechCupProductCore and used its
n2CechCupCochain in the beta representative hypothesis. This is definitionally
the same tuple formula as cechCupCochain. The signed tensor-cycle descent and
both axis proof branches are unchanged, as are all docstrings.

Updated the existing node's Lean spelling, proof dependencies and proof explanation.
Updated coord/changes/cech-cup-signed-axis-restoration-M2.md.
No other source module, project configuration or target was changed.

Validation uses only local single-file lcompile.py runs with the 60-second limit.
The final source compiled cleanly in 17.6 seconds (no warnings). A temporary anonymous example at the
complete original theorem type was proved directly by the repaired theorem and
compiled in 17.1 seconds; its temporary long-line warning was removed with the example.
An in-file axiom/direct-sorry check covered 55 local constants, including internal
helpers, and compiled in 18.5 seconds with no forbidden axioms or direct sorries.
Temporary checks are removed from the final source. Source import traversal confirms that CechCupProduct,
ModuleCohomologyCupProduct, ModuleCupResolutionInvariance,
ModuleCupNaiveDerivedCompatibility and GlobalTensorPullbackMonoidalNormalization
are all absent from the repaired dependency closure.

## Proved and sorry left

AlgebraicGeometry.Scheme.Modules.cupCech_signed_axis_pairing
(lem-sc-cech-cup-signed-axis-pairing) retains its complete proof.
All private helpers retain their proofs. No direct sorry remains, no hole is added,
and no statement is split off. The existing cochain-map existence dependency still
contains its previously recorded sorry; the repair adds no assumption or axiom.
This is an import repair, not an additional claim of hole progress.

## No longer needed

Removed the full public import Sheaf.Paper.CechCupProduct. This module needs only
the coefficient tuple formula provided by Sheaf.Paper.CechCupProductCore.
Its proof_deps now names new-cup-cech-product-core instead of
def-sc-cech-cup-product. The latter remains a mathematical statement dependency
in the node, since the formula is the same cup product.

The derived product characterization and resolution-invariance proof chain are
not needed for this signed total pairing. In particular, this item's closure no
longer reaches Sheaf.Paper.ModuleCohomologyCupProduct,
Sheaf.Paper.ModuleCupResolutionInvariance, Sheaf.Paper.ModuleCupRealizationEvaluation,
Sheaf.Paper.ModuleCupEqualDerivedMapsClass, Sheaf.Paper.ModuleCupNaiveDerivedCompatibility,
Sheaf.Paper.ModuleCupKInjectiveTarget, Sheaf.Paper.ModuleCupGlobalTensorPullback,
Sheaf.Paper.GlobalTensorPullbackUnderivedData or
Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization. Other library targets may
still need these modules. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous repair removed import all but retained the full CechCupProduct
public import. Its report treated the colliding instances as an unrelated baseline
issue. That dependency remained part of the landed module and broke the global
import probe. The repair now removes the unnecessary dependency chain itself.
The mathematical coefficient formula and entire original theorem type are preserved
by definitional equality, checked by Lean rather than merely comparing their text.

The repair worker did not deliver or produce second-reading evidence. The independent
second reader records local verification and performs normal delivery below; the
maintainer retains responsibility for the later global build.


## Second reading by XR916f3f6fae119923

Independent review of request.json, delivery.diff, the complete repaired Lean file,
node, change record and report, against the supplied read-only snapshot. Read the
stage-3 brief, stage document, AGENTS sections 4–5 and lead review requirements.
No other agents were used.

1. Interface and mathematics: PASS. The snapshot lacks this withdrawn module and
   node, so I reconstructed the returned versions from delivery.diff. The entire
   Lean diff is exactly the public import replacement and cechCupCochain to
   n2CechCupCochain in the beta hypothesis. All proof bodies, six component
   hypotheses and docstrings are unchanged. I independently copied the four
   original tuple definitions from CechCupProduct into a scratch copy and proved
   an anonymous example at the complete original theorem signature directly by
   the repaired theorem. Lean accepted it, confirming definitional equality.
   No target or definition used by a target was edited; no existing consumer of
   this module or theorem occurs in the supplied snapshot.

2. Compiler and trust: PASS for this repair. The delivered file compiled cleanly
   through lcompile.py in 21.2 seconds. The original-type scratch check compiled
   in 19.5 seconds; the scratch probe alone emitted a long-line warning, absent
   from the delivery. A further scratch compilation in 20.8 seconds printed
   axioms for every one of the 19 private declarations: each uses only propext,
   Classical.choice and Quot.sound. The public theorem uses those plus the
   existing sorryAx from exists_cupCech_total_cochain_map in the unchanged
   dependency chain. There is no direct sorry or forbidden trust declaration in
   the repaired source, and no new hole or axiom. Source traversal of all imports
   (including proof imports) excludes CechCupProduct and both modules named in
   the returned duplicate-instance failure. The repair therefore removes that
   failure's dependency path, not merely its symptoms.

3. Split statements and edge cases: PASS. No statement is split off or newly
   assumed. Read the bilinear quotient descent, tensor Leibniz identity, cycle
   preservation, both boundary proofs and cycle-class naturality. The zero-degree
   branches correctly use the vanishing incoming differential; the positive
   right-degree primitive is multiplied by (-1)^p, whose square is one. Empty
   index families and zero inputs require no nonemptiness hypothesis. The
   existing cochain-map existence result is used inside a theorem, not to choose
   arbitrary data in a definition.

4. Route and pruning: PASS. The proof uses the existing cochain morphism and
   Mathlib's LinearMap.liftQ₂, then applies its two axis equations. Independent
   searches in Mathlib's homology and quotient modules found no shorter complete
   axis theorem. Public imports serve the signature; the quotient and cochain
   pairing imports serve proofs. The old proof dependency def-sc-cech-cup-product
   is correctly replaced by the existing lightweight core node; the report
   identifies the unnecessary derived-product chain. The sk-prop-av-cube unit,
   its statement and realized fields remain untouched; no unit step is bypassed.

5. DAG and records: PASS. The node's Lean signature exactly matches the source.
   Its proof_deps equals the union of proof-step uses, and each dependency node
   already exists with its Lean declaration. The mathematical statement and
   source remain unchanged. The change record accurately documents the import
   and definitionally equal spelling change and the absence of consumers.

Second-reader changes: corrected the report's pre-review status paragraph,
appended this actual independent review, and wrote .check. The first dry-run
preflight found that restoration into this snapshot is treated as node creation:
I corrected created.group and lean.by from S3 to XR916f3f6fae119923 and added
the required New nodes restoration entry. No Lean or mathematical node field
needed correction. Approval is for the red-build import repair;
it does not claim completion of the pre-existing cochain-map hole.

After those metadata corrections, deliver3.py --no-push returned OK: local
compile and stage-3 preflight passed (dry-run commit 3d53340243). No server
compile was requested; normal delivery is to the project server only.


## New nodes

lem-sc-cech-cup-signed-axis-pairing is restored because it is absent from the
supplied baseline after the withdrawn landing. This is the original signed total
homology pairing with both axis formulas, not a new split or additional
assumption. Its Lean coefficient formula is definitionally equal to the original,
independently checked above. Its existing source, blueprint and mathematical
statement are retained; restoration ownership identifies XR916f3f6fae119923.
The import repair is documented in
coord/changes/cech-cup-signed-axis-restoration-M2.md.
