# Q108: trait-alteration geometric input boundary, 2026-10-24

Cause: Q84 re-admitted lem-per-trait-prime-to-ell-log-alteration while its five exact source-backed
geometric inputs remained in coord/route-pivot-dropped.txt. The repair note
forbade both those citations and duplicate replacements. Repeated workers
correctly left the packet unsplit; preflight then rejected the missing proof.
Retry counts and preflight completion fields cannot resolve this route conflict.

Re-admit precisely these existing statements as separate UNSPLIT stage-1 work:

- lem-per-trait-semistable-galois-alteration
- lem-per-tame-trait-quotient-log-etale
- lem-per-gabber-log-smooth-equivariant-modification
- lem-per-log-regular-projective-log-resolution
- lem-per-projective-finite-group-quotient

ILO XVI 3.7, printed pp.254--255, explicitly assembles semistable G-alteration,
tame change of trait, equivariant modification, quotient and log resolution.
This is the geometric input to the reopened finite-coefficient purity route.
It does not restore the discarded arbitrary-field adic-duality proof.

Preserve every statement, source, statement dependency, Mathlib search,
creation record and blueprint field. Withdraw the five old proof/proof_deps,
proof origins, split reports, tool-use approvals, reviews and Lean attachments.
Retain lean_removed and the empty lean_audit as deletion evidence only.
Fresh released stage-1 repair notes have keep_plan=false. Reconstruct each
interface through the normal worker and independent review path.

The complete statement closure has 113 nodes and no further excluded
interface. After withdrawing these five proofs, their remaining full dependency
closure has 130 nodes and no remaining exclusion. Thus this repair
does not retain a hidden reference to a forbidden prerequisite. Historical
proof closures are not authorized. Any lower-level reconstruction must check
its own sources, hypotheses and permitted inputs afresh.

Remove only these exclusively owned deleted-module exclusions:

- Sheaf.AlgebraicGeometry.TraitSemistableGaloisAlteration
- Sheaf.AlgebraicGeometry.TameTraitQuotientLogEtale
- Sheaf.AlgebraicGeometry.GabberLogSmoothEquivariantModification
- Sheaf.AlgebraicGeometry.LogRegularProjectiveLogResolution
- Sheaf.AlgebraicGeometry.ProjectiveFiniteGroupQuotient

All five source modules remain absent. No theorem statement is weakened and
no proof is approved. The WANTED quotient source is retained honestly in its
source record; the responsible worker must obtain it or reconstruct the proof
with admitted sources, rather than claim to have read a missing document.

This precisely extends Q84's unlisted-exclusion language for the five nodes
and five module ids above. All other exclusions, the 2026-10-19 pivot, no-SGA
4/4.5 rule and bans on arbitrary-field adic duality and the discarded
Artin-Gabber proof remain in force. This is interface authorization only.

The parent repair note, Q108 return and preferred-upstream brief supersede
stale BLOCKED notes. Reuse the saved sandbox research, source transcription
and logged searches. The parent is genuinely unsplit: its next worker writes
the one-level argument and citations, self-reviews, runs one dry run to
completion, and delivers for independent review. Citing these admitted unsplit
inputs is normal stage 1; do not prove them all inside the parent or relabel
the whole conclusion as a new node.

Transaction base: 987f97e422e7a59c15a7e19e70ad864c8e44f9bd. Audit: coord/maintenance/20261024-Q108-log-alteration-audit.json.
Every changed/new file has a sibling .maint-Q108-log-alteration-20261024.bak (empty for new files).
No Lean source, protected launcher/review/landing tool, queue, claim,
dispatcher state, failure counter or concurrency setting is changed.

## Postcheck: retired-proof reachability bookkeeping

Repository-wide check_dag already had unrelated findings before this repair. Its before/after comparison identified exactly six new reach findings caused by withdrawing the historical finite-group quotient proof. The helper ids below now have import_flags containing unreachable, as required for records no target or former target reaches. Every other field is preserved. This is graph bookkeeping only; their exclusions and historical proof status are unchanged. A future fresh split that needs one must resolve its route boundary and reach flag normally.

- lem-per-artin-tate-subalgebra-finite-type
- lem-per-equivariant-projective-envelope
- lem-per-finite-graded-module-dehomogenization
- lem-per-finite-graded-proj-morphism
- lem-per-projective-closed-subscheme-homogeneous-ideal
- lem-per-quasiprojective-affine-composition

These edits and the updated audit have additional sibling .maint-Q108-log-alteration-postcheck-20261024.bak backups.
