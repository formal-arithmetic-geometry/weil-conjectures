# Slow Derived Tensor: left canonical instance provenance (round 8)

## Evidence key and scope

`[R]` is a fresh Expr replay of the saved round-6 `icd_tensorObj_probe` in the pinned checkout; `[D]` is a compiled declaration/Expr audit; `[S]` is a fresh source-site synthesis trace; `[F]` is a disposable control; `[A]` is a source/import audit; `[H]` is the prior round-6 exact-root trace; `[I]` is an inference from the cited observations; `[U]` identifies a limit. The data and probes are in `sdtlcp/`. [R,D,S,F,A,H]

The environment uses Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and consumer `bdab171985a5e6c6e44fc3920386b89fc5627ca3`. Lean ran only in a disposable scratch area against the pinned checkout, with no Kernel or synthesis changes. The saved round-6 artifact is an exact-root **path trace**, not a serialized Expr; this round re-extracts its saved source probe with the same 12-binder descent. Thus fresh Expr hashes and paths below are replay measurements, while the round-6 root ID and cost path remain historical evidence. [R,H,U]

## 1. Exact left root and canonical occurrences

Round 6 root `557` compares `Eq` after `binder_body[12]`; the expensive branch is `argument[2]`, then `tensorObj`, the generic field, its proposition type, and the uncurried functor. `sdtprov/exact-root-paths.txt` records that path. [H]

The replay's Kernel-checked final body is an `Eq` Expr, hash `2070169438`, size `4805`, type `Prop` (type hash `3944470172`); its stored declaration-type counterpart is hash `3731220334`, size `18261`, also `Prop`. The checked and stored right-hand `tensorObj` Exprs have hashes `2245536834` and `3007844552`. Full `Lean.Expr` dumps are marked `LCP-DUMP-CHECKED` and `LCP-DUMP-STORED` in `sdtlcp/lcp-path.out`. These fvar-bearing hashes identify this replay only. [R]

| Expr scope | Direct canonical before reduction | Direct shortcut before reduction | Direct generic field before reduction | Evidence |
| --- | ---: | ---: | ---: | --- |
| Checked final body and its `tensorObj` provider | 0 | 1 | 0 | [R] |
| Stored final body and its `tensorObj` provider | 0 | 1 | 0 | [R] |
| Checked provider after `whnf` | 58 syntactic constant paths with the same 19-argument application hash | 0 | 26 paths with the same 10-argument application hash | [R] |
| Stored provider after `whnf` | 0 | 58 syntactic shortcut paths with the same application hash | 26 field paths with the same application hash | [R] |

For example, relative to `checked-provider-instance-whnf`, the first canonical **application** is at `root/fn/fn/fn/fn/fn/fn/fn/arg/body/body/fn/arg/fn/arg/fn/fn/fn/fn/fn/arg`; its constant node is reached by 19 further `/fn` edges. Its levels are `[max (u + 1) u', 0, u + 1]`, its application hash is `305716512`, and it is in the reduced provider's value/proof graph. All 58 application paths are in `sdtlcp/canonical-parent-paths.txt`; the compiled shortcut body identifies one source selection behind these repeated reduced paths. [R,D]

The un-reduced checked root instead reaches the shortcut constant at `root/arg/fn/fn/arg/arg/arg/fn/fn/fn/fn/fn/arg/fn/fn/fn/fn/fn/fn/fn/fn`, with levels `[u + 1, max (u + 1) u']`. That location is inside the right-hand `tensorObj` argument, not a directly stored canonical argument. [R]

## 2. Why the generic field sees only its local instance

`FromJoel/CategoryTheory/Monoidal/Derived.lean:143-159` declares the field for a rigid generic `C` under `[MonoidalCategory C]` and registers the projection as an instance. At that source site the measured goal is `MonoidalCategory C`, candidate array `#[inst✝²]`, and result `inst✝²` with no generated instance subgoal. The original import environment contains neither concrete HomotopyCategory declaration. [A,S]

A disposable copy adding the shortcut import makes **both** concrete declarations available, yet the same generic goal still has array `#[inst✝²]`. The concrete heads target `HomotopyCategory ...`, which cannot be unified with the rigid generic `C`; the registry's candidate array excludes them before attempts. The local wins after enumeration, not by stopping enumeration early. Both generic copies later fail in unrelated rewrite tactics, so the class-site trace is a partial-module replay, not a successful whole-module rebuild. See `sdtlcp/generic-trace.txt` and `generic-import-trace.txt`. [S,U]

## 3. Every relevant application of the generic field

| Site | Category `C` and actual `[MonoidalCategory C]` argument | Role | Evidence |
| --- | --- | --- | --- |
| `FromJoel/CategoryTheory/Localization/DerivabilityStructure/Monoidal.lean:74` | Generic `C`; the `HasDerivedMonoidalCategory` structure literal fills its field with `by infer_instance` under the local `[MonoidalCategory C]`. | Source-level field construction. | [A] |
| `FromJoel/CategoryTheory/Monoidal/Derived.lean:270`, compiled `CategoryTheory.DerivedMonoidal.instMonoidalCategory` | Generic `C`; compiled 10-argument projection at `root/body/body/body/body/body/body/body/body/body/body/fn/fn/fn/fn/fn/arg/arg`, argument 4 = bound local `[MonoidalCategory C]`. | One stored projection application, with no canonical/shortcut in this declaration's value. | [D] |
| Checked concrete provider after reduction, `C := HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)` | The 10-argument field application has argument 4 = fully applied canonical instance (19 arguments). | 26 reduced Expr paths with the same application hash. | [R] |
| Stored concrete provider after reduction, same `C` | The corresponding argument 4 = fully applied shortcut (8 arguments). | 26 reduced Expr paths with the same application hash. | [R] |

For both reduced applications, argument 0 is the HomotopyCategory, argument 2 its `instCategoryHomotopyCategory`, and argument 9 is `DerivedCategory.hasDerivedMonoidalCategory`; arguments 1, 3, and 5-8 are printed in `sdtlcp/lcp-path.out`. The first checked field path is `root/fn/fn/fn/fn/fn/fn/fn/arg/body/body/fn/arg/fn/arg/arg`; every reduced field path and its argument 4 is indexed in `sdtlcp/field-app-paths.txt`. These 26 paths arise from unfolding one compiled projection application, not 26 source calls. [R,D]

The compiled field projection itself has no proof value; `DerivedCategory.hasDerivedMonoidalCategory`, `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor`, and `Etale.isLeftDerivedFunctor₂_derivedTensor` have shortcut in relevant theorem types and no direct canonical constant. The generic field never selects canonical at declaration time. [D,S]

## 4. Actual canonical-supplying application

The first source-level selection of canonical is the final `inferInstance` in the **shortcut's own definition**, `CategoryTheory/Monoidal/Instances/HomotopyCategory.lean:28-31`. Its preceding local `have (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance` supplies a recursive premise. The compiled shortcut value contains `HomotopyCategory.MonoidalCategory.instMonoidalCategory` at `root/body/body/body/body/body/body/body/body/body/arg`, applied to 19 arguments; its type contains neither concrete constant. It is selected by typeclass synthesis and stored in the shortcut body, then exposed by delta unfolding in the left provider. [A,D,S,R]

The 19 argument heads, in order, are `A`, `[Category A]`, `Abelian.toPreadditive`, `[MonoidalCategory A]`, `Abelian.hasZeroObject`, two generated proofs, `Int`, `Int.instAddMonoid`, `ComplexShape.up Int`, tensor signs, the local graded tensor witness, five generated proofs, `Int.instDecidableEq`, and a final generated proof. The exact argument hashes and proof names are in `sdtlcp/lcp-decls.out`. [D]

## 5. Source declaration and environment

The shortcut source directly imports `Mathlib.CategoryTheory.Limits.Shapes.Countable`, `Mathlib.CategoryTheory.Monoidal.Closed.Basic`, `Mathlib.CategoryTheory.Monoidal.Limits.Preserves`, and `FromJoel/Algebra/Homology/HomotopyCategory/Monoidal`. Its open namespaces are `CategoryTheory`, `Limits`, and `MonoidalCategory`; its binders are `[Category A] [Abelian A] [HasColimitsOfSize.{0,0} A] [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]`, plus the local graded tensor `have` in the value. The shortcut itself is not yet declared/registered at this source point; the canonical instance is available through the import closure. [A,S]

At the concrete field application in `DerivedMonoidal.instMonoidalCategory`, `C` has been instantiated by the HomotopyCategory through the `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` provider. Its field argument is the local monoidal parameter specialized to that `C`, whose source term is the shortcut. The **selection** of canonical belongs to the earlier shortcut definition, not this field application. [D,R,I]

## 6. Synthesis at the actual selection site

The fresh F0 source replay, with original imports and binders and tracing restricted to the instance definition, reaches `MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ))`. Its candidate array is `#[HomotopyCategory.MonoidalCategory.instMonoidalCategory, inst✝³]`; reverse-order attempt of local `inst✝³ : MonoidalCategory A` fails target unification, then canonical succeeds after recursive subgoals. The result prints `HomotopyCategory.MonoidalCategory.instMonoidalCategory A (ComplexShape.up ℤ)`. This is a reconstructed source event, verified against the canonical constant in the compiled shortcut body, not an archived historical elaborator log. [S,D,U]

The canonical registration's default priority is 1000 in the pinned environment; F3 explicitly raises it to 2000. The F0 array order and attempt trace, rather than priority competition with shortcut, determine this site's observed result. [H,F,S]

The shortcut is unavailable as a candidate at its own defining `inferInstance`; adding its import to this module would be a self-import/cycle. The two concrete global instances therefore do not compete at this site. [A,S,I]

## 7. Provider chain to the final left root

The measured chain is `Eq` right argument -> `MonoidalCategoryStruct.tensorObj` -> `inferInstance` for `MonoidalCategoryStruct (DerivedCategory (Sheaf ...))` (argument 2 of `tensorObj`) -> `MonoidalCategory.toMonoidalCategoryStruct` (provider argument 1) -> `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` (argument 2, source `CategoryTheory/Monoidal/Instances/DerivedCategory.lean:35`) -> `DerivedMonoidal.instMonoidalCategory` (source `FromJoel/CategoryTheory/Monoidal/Derived.lean:270`) -> `curriedTensor_hasLeftDerivedFunctor₂` (the proof in the reduced monoidal structure, argument 4 = monoidal category of the HomotopyCategory) -> shortcut -> canonical body. The first two application spines and hashes are recorded in `sdtlcp/lcp-path.out`; the wrapper/field/shortcut bodies are audited in `sdtlcp/lcp-decls.out`. [R,D,A]

The historical comparison then descends through the generic field's proposition type, its `curriedTensor` functor, and `Functor.uncurry` proofs to the repeated `whiskerRight`-related comparison recorded under root `557`. That explains the connection to the expensive comparison; it is historical path evidence, not a new right-hand consumer search. [H]

## 8. Reduction provenance and G case

The wrapper's compiled value has an 8-argument shortcut application at `root/body/body/body/body/body/body/body/body/body/domain/fn/fn/fn/fn/arg`, hash `2016317515`, size `25`, with no canonical node. One targeted delta unfold of that shortcut gives hash `2178980340`, size `272`, containing canonical and no shortcut; inside it the canonical 19-argument application has hash `375119503` and levels `[u, 0, v]`. Both pre/post exact `Lean.Expr` dumps are in `sdtlcp/lcp-reduction.out`. [D,R]

**G4 holds**, with **G2 delta unfolding** as its mechanism: the apparent canonical argument is a reduced presentation of the originally supplied shortcut. It was not stored directly in the final root, introduced by beta/projection alone, or independently synthesized when the generic field was applied. [R,D,I]

## 9. Why the generic field is not the selection site

Its original goal is `MonoidalCategory C` with only `inst✝²`; its compiled projection takes its monoidal argument as a binder. At the concrete application that binder receives the shortcut. Canonical appears only after that supplied term is unfolded. These are three distinct events: generic source elaboration, concrete application, and Kernel reduction. [S,D,R]

## 10. F controls at the concrete source site

| Control | One-factor result | Type-correct declaration? | Evidence |
| --- | --- | --- | --- |
| F0 original source-site replay | Array canonical + local mismatch; canonical selected. | Yes. | [S,F] |
| F1 suppress shortcut registration **after** definition | Internal final `inferInstance` still selects canonical. Probe names the anonymous instance solely to address its post-definition attribute. | Yes. | [F] |
| F2 suppress canonical registration before definition | Final array becomes local mismatch only; synthesis fails. | No. | [F] |
| F3 raise canonical priority to 2000 before definition | Canonical still selected; there is no competing shortcut candidate. | Yes. | [F] |
| F4 raise shortcut priority to 2000 **after** definition | Internal choice remains canonical; the post-definition attribute cannot rewrite its compiled body. Same probe naming adjustment as F1. | Yes. | [F] |
| F5 add/remove shortcut import at its own definition | Not a valid one-factor import control: this module defines that shortcut, so import would be cyclic. | Not run. | [A,I] |
| F6 change a matching local instance | No matching local `MonoidalCategory (HomotopyCategory ...)` exists here; the local `MonoidalCategory A` is a measured mismatch. Conditional control does not apply. | Not run. | [S,I] |

F0's selected trace is `sdtlcp/f0-selected-trace.txt`; the F2 failure and F3/F1/F4 results are in their named reduced files. All tested controls are disposable copies. [F]

## 11. Remaining limits and decision

No serialized copy of historical root `557` or original source-time elaborator event was saved. The fresh replay uses the saved source probe and pinned environment, so its fvar-dependent hashes should not be compared numerically to older runs. A complete transitive-import manifest was not exported; direct imports, candidate availability, compiled definitions, and the decisive source-site trace were checked. [U,R,S,A]

**Section 14 outcome C:** canonical enters the inspected left provider by reduction of the nested shortcut, specifically delta unfolding of its body. The provenance map is corrected: the concrete generic field argument is shortcut before reduction and canonical only in its reduced presentation. This also explains why the earlier generic field's local-only candidate list did not identify canonical's source. [R,D,S,I]
