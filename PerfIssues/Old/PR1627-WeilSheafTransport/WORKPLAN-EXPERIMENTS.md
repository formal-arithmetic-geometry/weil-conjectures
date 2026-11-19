# Workplan experiments: PR #1627

Case: `P1627-generated-law`, declaration
`AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor`. Lean 4.35.0, master
revision `1ef1fddac73e`, original module identity, one Lean thread.

## Baseline and G2-A

The generated fields `_proof_1` and `_proof_2` are the dominant Kernel
checks. A fresh replay measured 20,228 ms and 33,699 ms for their values;
both inferred types are structurally identical to the declarations and the
final conversions are 0 ms. The enclosing generated-law audit localizes the
slow application to an `id` argument whose instantiated proposition domain
takes approximately 7.508 s and 33.863 s in the preserved prefix probe.
The audit process used 160.08 s CPU, 2:42.79 wall, and 7,786,240 KB peak
RSS.

Probe: [`G2C-GeneratedProofAudit.lean`](probes/wp/G2C-GeneratedProofAudit.lean).
The declaration has 9/13 type binders versus 8/11 value binders, and its
body is `id` with two arguments. The relevant expected domain is reconstructed
after all preceding binders are instantiated; no generic uninstantiated
helper domain is used.

## G2-B/C and G4-A

The proof-value check is slow while the final inferred/declared type check is
immediate. Replacing the proof by an arbitrary term would not preserve the
generated field's proposition, so no invalid `sorry` timing is counted as a
control. The retained generated-prefix probe records the proof proposition
and the dependent domain separately. A concrete data abstraction and a proof
abstraction both require a valid transport in this generated context; neither
was available without changing the theorem obligation.

## Interpretation

The cost belongs to checking the generated law's proof value, not its final
declared type. The shared `id` head is reached only after dependent
instantiation; the next nested proposition term remains unresolved. This is
consistent with a dependent proof-domain conversion, but does not establish
whether the proof construction or concrete functor data is the first trigger.

**Confidence:** plausible, with the exact nested mismatch still open.
