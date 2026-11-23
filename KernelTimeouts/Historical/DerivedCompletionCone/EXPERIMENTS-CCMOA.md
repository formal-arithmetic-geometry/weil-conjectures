# CCMOA: Derived-completion cone

Scope: historical `DerivedCategory` cone at source revision `9ba4d01f55c`, Lean 4.33.1. This report reuses `EXPERIMENTS-MOE.md`, `EXPERIMENTS-M1P.md`, `ANATOMY.md`, `REPORT.md`, and the saved round-two controls. No shared build tree was modified.

## A. Stages and first divergence

| Stage | Snapshot and result |
| --- | --- |
| S0 | Original declaration writes `Cone (quotPowFunctor J I ⋙ tensorLeft K)`; the named control writes `Cone (derivedCompletionDiagram J I K)`. The representation choice is source-authored. |
| S1 | In `moe/context_inline.snapshot`, `⋙` expands to `Functor.comp`; `context_named.snapshot` retains a named diagram application. |
| S2 | Shared-context `moe/compare-context.txt` locates the **cross-control** first Expr difference at `root/arg/arg`: inline `kind=app` headed by `Functor.comp`, named `kind=fvar` in that bound context. The inferred monoidal provider on the inline path is `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`; named use stops at the stored diagram. This is not the original M0 pair's first unequal proof field. |
| S3 | The imported `derivedCompletionDiagram` has only a finalized, observational S3 record. The original inline inferred/declared comparison has a historical structural count of 36 proof positions after `abstractNestedProofs`; its pre-finalization value is unavailable. |
| S4 | `moe/diagram-decl.snapshot` stores `derivedCompletionDiagram` as `regular:33`; `abbrevDiagram` is `abbrev`, ordinary and reducible local diagrams are `regular:31`. Generated proof constants occur in stored value-side positions. |
| S5 | Original root: inferred type of `inlineCone` versus declared `Cone (quotPowFunctor J I ⋙ tensorLeft K)`, in the same eight-binder context. `#moe_root derivedCompletionDiagram` separately checks its stored type/value pair as definitionally equal; that is not the inline timeout root. |
| S6 | READY4.1 inline root: 12,220,822 recursive calls, depth 111; M1 9,356,262 (99.694% exclusive time), M2 9,087, Matched 2,855,469. Application, projection, and dependent-body descent expose proof-laden instance descendants. |

The exact original M0 pair is the final inferred/declared cone type above. The available structural audit counts 36 minimal proof-position differences, including generated `derivedCompletionDiagram._proof_*` versus ambient proof terms inside the concrete monoidal instance; it did not retain a stable first unequal Expr path for the original M0. The recorded M1 path `root/binder_body[8]/argument[4]/argument[7]/argument[4]/binder_body[1]` is a propagation path, not a proven first unequal node. The S0/S1 inline-versus-named difference is exact; the original proof-position divergence is first verified at S4. Its first occurrence between S2 and S4 is Unknown.

## B. Controls and READY4 workload

| Control | Expr change and obligation | Counters |
| --- | --- | --- |
| Inline/inferred | `Functor.comp` and synthesized concrete monoidal instance in the original cone type; same eight-binder telescope. | READY4.1 root 12,220,822 calls, timeout-scale; 9,356,262 M1 calls. |
| Named diagram | `Functor.comp` replaced by `derivedCompletionDiagram` at the use site; same cone result shape but a different root Expr. Type-correct. | Earlier instrumented counters: largest root 22 calls, 0.123 ms; no corresponding slow root. |
| Explicit provider sharing | A bound `MonoidalCategory` instance replaces independently synthesized concrete occurrences. Adds a binder and changes the dependent telescope, so it is not an original-M0 one-factor control. | Largest root 344 calls, 1.646 ms. |
| Named + shared | Both changes together; no independent interaction claim. | Largest root 344 calls, 1.668 ms. |

Restoring the inline spelling restores the 12,220,822-call family. The named control changes the S2 Expr and workload, but its root representation differs. A descendant-only proof/provider replacement was rejected because it changes the dependent field type and does not preserve M0. These controls support a naming boundary; they do not prove that one particular proof constant or provider leaf causes the timeout.

## C and D. Provenance and finalization

Targeted inline elaborator trace records synthesis of `MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R)))` through `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` and nested `GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`. The named branch avoids reconstructing that use-site instance. This is an observed S2 representation difference. The explicit-sharing control changes a binder and thus cannot isolate an Elaborator decision under the original obligation. No concrete transparency assignment was shown to change the final Expr under fresh metavariable state. Independent Elaborator causality is **Plausible**, not Demonstrated.

Stored `derivedCompletionDiagram` has `regular:33`; the local `abbrev` control's different hint verifies that metadata can differ. The historical 36 proof positions include generated constants after `abstractNestedProofs`, showing finalization affects the stored value representation. Neither `moe/diagram-decl.snapshot` nor the earlier audit captured the same declaration's pre-finalization S2 value, so whether finalization *created the costly mismatch* is **Unknown**. The saved `#moe_root` result `true` does not resolve that timing.

## E. Boundary inventory

| Boundary | Why cheap now, puncture, status |
| --- | --- |
| `derivedCompletionDiagram`, `regular:33` | Named head keeps the concrete composition and its proof-bearing instance behind a regular definition. Inline expansion at the cone use site restores timeout-scale work. **Fragile but effective**. |
| Shared `MonoidalCategory` binder | Reuses one provider Expr at both occurrences and gives a 344-call local control. It changes the telescope; no original-root causal claim. Independently rebuilding the instance can puncture sharing. **Fragile but effective** for the changed-telescope control. |
| `abbrevDiagram` versus regular diagram | `abbrev` unfolds readily; local ordinary/reducible definitions both have `regular:31`. Hint alone does not explain cost without the exact use-site head. **Untested** as a same-Expr metadata-only boundary. |
| Opaque generated proof bodies | Body opacity is cheap once proposition types match, but the equality proposition types contain the concrete provider. Exposing the data in a dependent declared type re-enters the expensive path. **Fragile but effective** for proof bodies, not isolated as the root cause. |

## Synthesis

| Case | Earliest divergence stage | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Derived-completion cone | S0/S1 naming choice; original proof path S4 (**Strongly supported**) | Inline concrete composition and instance representation (**Strongly supported**) | **Plausible** | **Unknown** | **Strongly supported** | Named `derivedCompletionDiagram` (**Strongly supported**) | **Strongly supported** fragile |

No `Demonstrated` causal level is assigned: the named and shared controls change the root Expr or telescope, and the original first proof-position path has no matched one-factor intervention.
