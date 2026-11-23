# CCMOA: ImageHomCounit

Case `ImageHomCounit`; conversion `IHC-final-exact-v1`; Lean 4.35.0 and the
case's pinned Mathlib revision. The root is the final `exact h` conversion in
`imageHomIso_counit`, where `h` is the concrete `conjugateEquiv_counit`
application. The imported fixed theorem and all measurements are reused from
the existing case probes; the fresh lightweight S2 snapshot is in
`ccmoa/s2-snapshot.txt`.

## A: stages and first divergence

| Stage | Observation |
|---|---|
| S0 Source | `h` is formed by `conjugateEquiv_counit` with the raw derived-category endpoints. The declared equality uses `DerivedCategoryModule` in its `Quiver.Hom` type and both composition sides. |
| S1 Macro-expanded syntax | Notation expansion (`≫`, `.map`, `.app`) changes application scaffolding only. The raw/wrapper category vocabulary is unchanged; no macro-generated replacement of the endpoint representation was observed. |
| S2 Elaborated Expr | Fresh snapshot roots: actual hash `349589718`, expected hash `1301129340`. Both roots are `Eq` at universe `u+2`, with matching `Quiver.Hom` and composition heads. The first unequal type/data child is the actual raw `DerivedCategory (Sheaf T.left.Etale (ModuleCat A))` versus expected `DerivedCategoryModule A T.left` (an abbrev); the same boundary recurs in the equality sides. |
| S3 Declaration finalization | The imported declaration's pre-finalization term is unavailable. No generated auxiliary declaration is implicated by the selected root. |
| S4 Stored environment | `DerivedCategoryModule` is `abbrev`; `DerivedCategory` is regular (height 15). The relevant category and derived-category instance constants are imported and environment-frozen. The target theorem is opaque. |
| S5 Kernel root pair | The exact inferred-type/goal pair succeeds, but the original READY4.2 root is large: 6,359,958 calls, depth 204, 42,138.453 ms comparison-exclusive, 44,315.360 ms reduction-exclusive, 20,993,747 WHNF requests. |
| S6 Kernel exposure | Unfolding the wrapper/raw endpoint boundary exposes a deep M1 propagation tree. Existing READY3.2/READY4.2 analysis attributes 99.768% of comparison-exclusive time to M1; M2 is 0.008%. |

The first divergence is therefore present at S0/S1 as a source/API
representation choice and is retained at S2. It is latent behind the
`DerivedCategoryModule` abbrev until Kernel reduction enters the dependent
morphism type. The exact structural nodes and hashes are retained in
`ccmoa/s2-snapshot.txt`; the full head audit is in
`ccmoa/head-audit.md`.

## B: representation controls

| Variant | Expr change | Obligation and result | READY4.2 counters |
|---|---|---|---|
| Original `FinalExact` | Raw `DerivedCategory` inferred pair versus wrapper `DerivedCategoryModule` target. | Same final consumer; succeeds after the expensive conversion. | 6,359,958 calls; 42,138.453 ms comparison; 44,315.360 ms reduction; max depth 204. Release probe was about 55 s and 7.46 GB RSS. |
| Full endpoint alignment `aligned-UniformInferred` | Changes only the declared endpoint representation to `type_of%` of the unchanged `conjugateEquiv_counit` term. The elaborated equality sides and type argument become structurally equal; `UniformInferredHead` verifies this. | Same `h`, same final consumer, same proposition up to definitional equality. | Largest recorded root 16.251 ms / 2,881 calls (comparison 11.410 ms, reduction 4.841 ms, depth 37). |
| Wrapper-only expansion `restored-UnfoldWrapper` | Expands only the outer `DerivedCategoryModule` wrapper; the nested raw/wrapper endpoint mismatch remains. | Type-correct restoration; original inner obligation is retained. | 9,539,325 calls; 57.738 s comparison; 58.509 s reduction; max depth 201. |
| Source spelling controls `UniformRaw`, `RegularWrapper` | Changes variable spelling or a same-body local wrapper only. | Type-correct, but the elaborated pair is unchanged, so neither is a valid B control. | Both remain on the approximately 55 s path. |

The full endpoint alignment is a one-boundary control: it changes the targeted
raw/wrapper representation while retaining the consumer, local context, and
proof term. It changes the S2 pair and the Kernel workload by orders of
magnitude. Wrapper-only expansion is a negative isolation control, not a
claim that the outer abbrev alone causes the whole cost.

## C and D

No C run was warranted. S0/S1 already contain the first divergence, and no
provider-only or transparency perturbation was shown to change the S2 pair.
Instance paths under the wrapper are visible in the head audit, but their
causal share is unisolated.

D is unobservable for the imported theorem. S2/S4 provenance does not show a
finalization-generated change, and no generated proof field is the first
divergent child.

## E: cheap-but-fragile boundaries

| Boundary | Current reason it is cheap/effective | Puncture and status |
|---|---|---|
| Whole endpoint alignment | The expected equality is presented in the exact inferred raw endpoint representation, so the final conversion is nearly reflexive. | Replacing it with direct `exact h` restores the deep root. **Fragile but effective.** |
| `DerivedCategoryModule` abbrev/raw interface | The abbrev exposes raw `DerivedCategory`, but nested endpoint and category-instance paths remain behind it. | Unfolding only the wrapper leaves a larger root. **Fragile and not sufficient alone.** |
| Shared category/monoidal providers | The original and aligned controls retain the same preceding providers and local context. | Independently reconstructing providers or mixing raw and wrapper vocabulary is untested and may re-expose the tree. **Untested.** |

## Synthesis row

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
|---|---|---|---|---|---|---|---|
| ImageHomCounit | S0/S1 | Source/API raw versus wrapper endpoint representation (**Demonstrated**) | No relevant first-stage choice observed (**Not observed**) | No generated change observed (**Not observed**) | Wrapper/raw dependent path and M1 propagation (**Demonstrated**) | Full endpoint representation alignment (**Demonstrated**) | Fragile but effective; wrapper-only exposure is insufficient (**Demonstrated**) |

The source-level representation mismatch is the demonstrated origin of the
measured root. The exact downstream instance leaf that amplifies the cost is
not isolated; that narrower claim remains **Plausible**, not demonstrated.
