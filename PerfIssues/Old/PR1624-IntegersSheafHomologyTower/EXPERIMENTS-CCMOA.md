# CCMOA: PR1624 IntegersSheafHomologyTower

## Stage audit
- S0: Before assembles the final iso through concrete whiskerings and differently associated derived-functor compositions. After applies homologyIntegersTowerIsoAux to pieces over abstract functor variables. Both have the same declared target type.
- S1: No historical macro-expanded syntax snapshot is retained. Notation expansion is Unknown as an origin.
- S2: No valid historical pre-finalization Expr snapshot exists. The fresh scratch replay fails in preceding declarations with the current permitted closure; its subsequent final-argument failure is not a historical snapshot.
- S3: Imported pre-finalization data are unavailable, so no finalization cause is claimed.
- S4: The earlier imported-value audit found Functor.comp regular:1, with a one-step Functor.mk body. The old value contains 11 lets. Full old ConstantInfo and auxiliary trees were not captured.
- S5: The earlier exact probe checks the last isoWhiskerLeft term and the six-argument Iso.trans prefix, then instantiates its seventh Pi domain with all preceding actual arguments. Both are Iso-headed with matching universes and a structurally identical carrier/category instance. Source and target endpoints are Functor.comp pairs, taking 14.706 and 28.640 s. At these endpoints, arguments 2/3/6/7 are individually unequal in 0-8 ms; argument 6 on the target side contrasts Functor.comp with higherDirectImageQuotPowTower. Exact structural hashes were not retained.
- S6: Functor.comp argument congruence fails, requiring reduction into Functor.mk and dependent endpoint fields. READY4.2 root 22078 has 6,598,545 calls; M1 5,215,138 (99.848% exclusive time), M2 287, Matched 1,383,111. The earliest authored representation difference is S0; the exact old pair is evidenced by the earlier S5 probe.

## Representation control
The same-statement Before/After source replacement reduces target Kernel checking from 102 s to 3.18 s. The older broad aligned endpoint reduces 6,598,545 calls to 456,393 calls in READY3.2, but changes the dependent telescope and removes M0, so it is invalid as a one-factor control. No READY4.2 after-counter or old/fixed S2 Expr comparison exists. This supports the concrete-versus-abstract boundary, without satisfying Demonstrated.

C was not run because the available S5 pair points to concrete source-authored functor compositions, with no isolated S2 provider choice. D was not run because S2/pre-finalization is unavailable.

## Boundary inventory
The fast boundary is homologyIntegersTowerIsoAux applied to abstract functor variables; its stored hint was not measured. The old slow endpoint has Functor.comp (regular:1), whose concrete arguments differ and expose Functor.mk fields after unfolding. Inlining the concrete composition assembly as in Before punctures the boundary and restores the expensive target check. Status: fragile but effective. Reassociating concrete derived functors in the final dependent iso type is the refactor risk.

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
|---|---|---|---|---|---|---|---|
| PR1624 | S0 representation; exact pair at S5 (Strongly supported) | Concrete derived-functor composition (Strongly supported) | Unknown | Unknown | Functor.comp unfolding (Strongly supported) | Abstract functor helper (Plausible) | Fragile but effective (Strongly supported) |

Raw evidence: ccmoa/snapshot-attempt.log documents the incompatible current-closure replay; it is not an Expr snapshot. Historical evidence: HEAD-AUDIT.md, EXPERIMENTS-M1P.md, CLASSIFICATION.md, Before.lean/After.lean.
