# Q73 compact-product compiler recovery, 2026-10-18

Item: lem-pur-compact-product-proper-support-compatibility, stage 2.
Maintenance workspace:
/home/ubuntu/weil-launcher-all/maint/Q73-lem-pur-compact-product-proper-support-compatibility-1792307354

## Observed cause

The five reported attempts repeatedly reached per-file Lean timeouts and exhausted
approximately the 45-minute worker lifetime without a final-answer file. NOANSWER
is the resulting dispatcher symptom. No HTTP 429, gateway-limit or empty-provider
response was found in those runs. Do not change retry policy or capacity controls.

The server fallback compiler reproduced an unnecessary dependency from the
finite-only FixedFinitePositiveCoefficientTwist through IntrinsicCoefficientTwists
to DerivedPullbackTensorHom. The latter reached its 60-second limit before Q73.
Source repair commit 4ce5a11f47797293f4820fdd66a6891c6acda2fa imports the actual
CoefficientExtensionFinite dependency directly and gives PbcCoefficientTwists an
explicit public import of IntrinsicCoefficientTwists. The finite module passed in
5.4 seconds; the full PBC public import closure is unchanged (11222 modules).
The two source files have .maint-Q73-20261018T072811331852Z.bak siblings.

A newer completed attempt, 1792307356, explicitly reported BLOCKED: the primary
compiler repeatedly looked for OrdinaryFiniteP1Arrows.olean under the live library,
even after explicitly compiling that unchanged source successfully. The source
exists only in /home/ubuntu/weil-newtargets/lean; the live source and live .olean
are absent. The fallback handles this side-only source but formerly encountered
the unrelated DerivedPullbackTensorHom timeout described above.

Required protected-tool correction: resolve/build side-only transitive imports
reached by published importers and expose their complete Lean artifact companions
in the private overlay, rather than selecting absent live artifacts. Audit this
path with OrdinaryFiniteP1Decomposition and OrdinarySupportedKummerSystem. This is
a requested tool-owner correction, not a claim that the protected compiler was
modified here. Existing unrelated modifications in tools/nt_srv_compile.py and
tools/launcher/nt_local_compile.py were left untouched.

## Applied sandbox repair

The worker independently expanded its packet to thirteen Lean modules and thirteen
records. Preserve that work. Maintenance changed only this sandbox record:
dag/nodes/sec-smooth-purity/def-pur-compact-product-realization-arrows.json
It now explicitly cites [lem-pur-support-site-comparison] and
[lem-sf-class-compact-support-comparison] separately in its English statement;
both were already stmt_deps. This fixes the validator's literal citation check.
The mathematical content and dependency list are unchanged. Backup:
<record>.maint-Q73-20261018T081433Z.bak.

The accompanying .patch contains exactly that citation repair and applies at the
sandbox root. It is recovery material, not a stage-2 delivery. In the final maintenance record check, all
thirteen live records passed server record, ownership, Lean-text and incremental
DAG checks with zero findings. Later worker edits must be checked again.

## Next worker

Retain the current thirteen-module packet and use the committed finite import
repair. All maintenance source refactors remain outside the sandbox; none passed
the complete file check. In the actual server wrapper, the current helper split
passed through SupportedTwistDegreeZeroProduct (25-33 seconds) and
SupportedTwistPullback (9-11 seconds) but SupportedTwistMultiplication exceeded
60 seconds. Main item validation and normal stage-2 delivery remain outstanding.
Removing the exterior eqToHom transport alone and adding an intermediate-scheme
helper both still timed out. Do not install those experimental candidates.

Keep the canonical pullback, shift and normalized finite twist multiplication;
the cup comparison remains a theorem conclusion. Do not substitute an arbitrary
map, assumption or weakened statement to avoid elaboration. No item's theorem
proof has been supplied by maintenance. The active worker independently introduced compactProductTwistMultiplicationGeneral
and its focused seven-module scompile.py check now passed: multiplication took
34.2 seconds in the sandbox and 34.8 seconds at its library path. Preserve that
current source; the worker is proceeding to the full delivery dry run. This is
a focused positive result, not certification of the full thirteen-module packet.

An item-specific continuation note is installed at:
/home/ubuntu/weil-launcher-nt/route-notes/lem-pur-compact-product-proper-support-compatibility.md
It is appended automatically to future worker prompts. Finish through the normal
stage-2 dry run and delivery review. No dispatcher state, retry/admission rule,
protected launcher program, review service or landing tool was changed.

See the maintenance workspace REPORT.md and evidence/ for exact compile logs,
backups, import-closure audit and the final experiment result.

Final maintenance experiment: the intermediate-scheme helper with transparency
respected also timed out in SupportedTwistMultiplication after 60 seconds. It
remains outside the sandbox; do not install it. The captured worker focused
success refers to its different generic-coefficient source, not this experiment.
