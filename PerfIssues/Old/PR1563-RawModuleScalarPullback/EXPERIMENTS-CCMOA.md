# CCMOA: PR1563 RawModuleScalarPullback

## Stage audit
- S0: Before uses simp only to unfold higherDirectImageRawOverFunctor, rawTriangleMap, and concrete derived-category compositions. After applies higherDirectImageRawOverPullback_eq_moduleFactors, which invokes a generic rawTriangleMap helper. The declared theorem type is unchanged.
- S1: No macro-expanded historical tactic snapshot was retained. Macro contribution is Unknown.
- S2: The exact pre-finalization tactic term is unavailable. The stored value contains Eq.mpr, consistent with tactic generation, but this does not locate the first divergence at S2.
- S3: Pre-finalization versus finalized value is unobservable from this imported declaration.
- S4: The fresh successful scratch replay reads the stored old value. Eq.mpr has hint regular:1 and CategoryStruct.comp has hint abbrev; the latter reduces to a CategoryStruct projection. Full ConstantInfo trees and auxiliary declarations were not captured.
- S5: The fourth Eq.mpr argument is Eq.refl. Its actual type and the final Pi domain instantiated with all three preceding actual arguments are Eq/Eq at universe u+2 in the opened 12-binder context. The MOE first structural divergence is root/arg/arg: actual fvar hash 3464578144, expected app hash 2517504410. The differing equality result compares in 28,989 ms. The carrier and left equality side are structurally identical and compare in 0 ms.
- S6: The expected right side is a concrete CategoryStruct.comp and the actual side is headed by DFunLike.coe. Earlier argument probes locate 22.155 s in nested composition argument 6 and 2.079-6.601 s in arguments 2-5. The exact first reduction is not recorded. Earliest proven divergence is S5; S2 is plausible because simp constructed the Eq.mpr proof.

## Representation control
The same-statement Before/After value replacement changes the source proof from concrete simp expansion to a named raw-pullback theorem. The historical target Kernel check falls from 68.2 s to 15.2 s, but the helper itself retains a 32.4-32.7 s floor. This changes more than one expression boundary. The earlier aligned provider control changes the dependent root and is invalid as a one-factor test. READY4.2 original root 7269 has 2,563,145 calls: M1 1,924,504 (99.731% exclusive time), M2 1,029, Matched 637,607. No valid READY4.2 after-counter exists. The observed Expr change is the Eq.mpr result-side fvar/app pair versus a named helper application; an exact old/fixed S2 pair was not captured. No Demonstrated causal claim follows.

C was not run because no S1/S2 pair or selected implicit/provider decision is available. D was not run because the imported pre-finalization value is unavailable and no material S2/S4 difference was established.

## Boundary inventory
The effective boundary is the named raw-pullback theorem over abstract functors, with a private generic associativity theorem behind it. The cheap local step is Category.assoc over variables; the original concrete path exposes functor composition, pullback objects, and a projection through CategoryStruct.comp (abbrev). Replacing the helper application with the original concrete simp proof punctures that boundary and restores a slow target, while the shared helper remains expensive. Status: fragile but effective for the target, with a substantial surrounding type/context floor. Refactoring the theorem back through the concrete functor API risks restoring the old conversion.

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
|---|---|---|---|---|---|---|---|
| PR1563 | S5 observed; S2 plausible (Plausible) | Concrete tactic-generated Eq.mpr/composition vs helper (Plausible) | Unknown | Unknown | Projection continuation (Strongly supported) | Generic raw-pullback helper (Plausible) | Fragile but effective (Strongly supported) |

Raw evidence: ccmoa/snapshot-attempt.log (successful MOE S5 replay). Earlier controls: HEAD-AUDIT.md, EXPERIMENTS-IM.md, EXPERIMENTS-M1P.md, and Before.lean/After.lean.
