# Slow Derived Tensor: Instance-Synthesis Forensics (round 7b)

## Evidence key and pinned environment

`[FT]` is a fresh Lean 4.33.1 synthesis trace from this round; `[FC]` is a fresh controlled probe; `[SA]` is a source/import audit; `[IA]` is a pinned Lean implementation audit; `[CE]` is the round-6 compiled-Expr audit; `[INF]` is an inference; `[UNK]` marks an unmeasured event. The reduced observations and probe inventory are in `sdtisf/`. [FT, FC, SA, IA, CE]

The consumer is `bdab171985a5e6c6e44fc3920386b89fc5627ca3`, Mathlib is `0df444a360eaa60ab8c11cda51a86af692955474`, and Lean source is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. All new runs used the pinned Lean executable, a 3600 s timeout, and at most two investigation Lean processes concurrently. The scratch files were confined to `sdt-isf`; no shared checkout, Kernel semantics, commit, or push was changed. Disk usage was 83-85%, below the 90% limit. [FC, SA]

## 12.1 Exact goals and sites

The named earlier declaration is the **projection** `Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂`, declared as a class field at `WeilConjectures/FromJoel/CategoryTheory/Monoidal/Derived.lean:144-145` and registered as an instance at line 159. Its source expression is `(curriedTensor C ...).HasLeftDerivedFunctor₂ W W`, with a generic `C` and local `[MonoidalCategory C]`. A fresh re-elaboration of that module traces the goal `MonoidalCategory C`, candidate list `#[inst✝²]`, successful application of that local instance, and result `inst✝²`. No concrete homotopy-category instance is chosen at this source site. [SA, FT]

The later source site is `WeilConjectures/SixFunctors/Etale/Derived/Tensor.lean:81-86`, `derivedTensor := curriedTensor _`; the same module's `isLeftDerivedFunctor₂_derivedTensor` at lines 100-105 triggers another concrete search. A fresh trace of the exact source copy records `MonoidalCategory (HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))`, with universes displayed as `u + 1` and `max (u + 1) u'`, and selects the shortcut. A transient metavariable goal earlier in elaboration is not the final successful goal. [SA, FT]

**A3 decision:** the *instantiated monoidal argument types in the two final `curriedTensor` Exprs* are structurally identical, and their category arguments are pointer-shared, as measured in round 6. The *source-time synthesis goals and local contexts just identified* are different: generic `MonoidalCategory C` with a matching local instance versus the concrete homotopy-category goal with a local `MonoidalCategory A` of the wrong target. Therefore “the two synthesis goals are identical” is true only for the final instantiated target types, not for these two source-time calls. No unequal universe or category argument was found in the final Expr comparison. [CE, FT, SA]

The class-field source is generic, so its compiled projection does not contain a source-time choice between the canonical and shortcut concrete instances. The round-6 final Expr nevertheless has a canonical instance application on the left and a shortcut application on the right. The exact route by which the left concrete canonical argument appears remains unobserved; assigning a separate synthesis event to the class-field source would be incorrect. [CE, FT, UNK]

A fresh compiled-declaration audit finds neither concrete constant in the projection's type or value. `DerivedCategory.hasDerivedMonoidalCategory` and `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor` contain the shortcut in both theorem type and value, with no direct canonical constant; `Etale.isLeftDerivedFunctor₂_derivedTensor` contains the shortcut in its type and neither concrete constant in its proof value. Thus these inspected declaration trees do not store a direct canonical application at the reported left site. The canonical seen after the round-6 extraction/reduction may arise while unfolding the shortcut or another nested term; the exact transformation has not been isolated. [FC, CE, INF, UNK]

## 12.2 Module environments and candidate inventory

The generic class-field module directly imports the six `FromJoel` monoidal/derived helper modules listed in its source and does not directly import the shortcut. The historical `HasMonoidalDerivedCategory` module *does* directly import `CategoryTheory/Monoidal/Instances/HomotopyCategory`; the historical `Instances/DerivedCategory` module also imports that shortcut module; the final consumer imports both of those modules. Fresh recompiles of the two intermediate historical sources find the shortcut in the registry and select it for their concrete homotopy-category goals. Thus an assertion that every earlier concrete declaration lacked the shortcut is contradicted by the measured import closure. A complete machine-readable transitive-import list was not exported. [SA, FT, UNK]

| Candidate at relevant goal | Old generic field | Exact consumer concrete goal | Priority / origin | Evidence |
|---|---|---|---|---|
| Local `inst✝² : MonoidalCategory C` | Listed and selected | Not this local | Local, appended last | FT, IA |
| Local `inst✝⁴ : MonoidalCategory A` | Not this local | Listed; head/type mismatch | Local, appended last | FT |
| `@SemiCartesianMonoidalCategory.toMonoidalCategory` | Not listed for generic goal | Listed; not reached after shortcut success | Global; prerequisite class candidate | FT |
| `HomotopyCategory.MonoidalCategory.instMonoidalCategory` | Not listed for generic goal | Listed before shortcut; not attempted in baseline | Global, priority 1000, 19 arguments; `FromJoel/Algebra/Homology/HomotopyCategory/Monoidal.lean:235` | FT, CE, SA |
| `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures` | Not listed for generic goal | Listed after canonical; tried and succeeds | Global, priority 1000, 8 arguments; `CategoryTheory/Monoidal/Instances/HomotopyCategory.lean:28` | FT, CE, SA |

The candidate arrays above are the actual `Meta.synthInstance.instances` arrays, not `#print instances` output. The canonical-only import probe returns `#[canonical, local]`; the consumer suppression probe returns `#[SemiCartesian, canonical, local]` when shortcut registration is removed and `#[SemiCartesian, shortcut, local]` when canonical registration is removed. The shortcut constant remains available in the latter probe, and its compiled body still contains the canonical constant. [FT, FC, CE]

## 12.3 Old-site and earlier concrete paths

At the named generic class field, the trace has one candidate: `inst✝² : MonoidalCategory C`. Unification succeeds without generated instance subgoals, and the returned Expr is that local variable. Adding the shortcut import to a disposable copy does not change this candidate list or result at the class field. Later rewrite tactics in that import-variant copy fail, so E1 is a **partial source-site diagnostic**, not a successful recompilation of the whole changed module. [FT, FC]

A separate canonical-only import probe with the concrete goal first rejects local `MonoidalCategory A` by target mismatch, then applies `HomotopyCategory.MonoidalCategory.instMonoidalCategory A (ComplexShape.up ℤ)`. Its recursive search visits the canonical declaration's 19 arguments: category/preadditive/monoidal inputs, zero object and additive functors, `AddMonoid ℤ`, tensor signs, graded tensor and coherence families, colimit-preservation families, `DecidableEq ℤ`, and `HasMapBifunctor`. The successful final answer is canonical after recursive alternatives and failures (including absent `NonPreadditiveAbelian A` on one `HasZeroObject` branch). This is a controlled canonical-only **proxy**, not a recovered original left-hand historical search trace. [FC, CE, UNK]

Fresh recompiles of the historical `HasMonoidalDerivedCategory` and `Instances/DerivedCategory` sources instead select the shortcut for their concrete `MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ))` goals. Their trace rejects the local `MonoidalCategory A` by target mismatch, then succeeds with shortcut; neither shows canonical selected at that concrete goal. This narrows, but does not locate, the original left canonical selection. [FT, UNK]

## 12.4 Consumer path and G case

The exact consumer trace reports the array `#[@SemiCartesianMonoidalCategory.toMonoidalCategory, HomotopyCategory.MonoidalCategory.instMonoidalCategory, instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures, inst✝⁴]`. Search first tries local `inst✝⁴`; unification fails because its target is `MonoidalCategory A`. It next tries the shortcut; target unification succeeds. Its six generated class subgoals are `Abelian (Sheaf ...)`, `HasColimitsOfSize (Sheaf ...)`, `MonoidalCategory (Sheaf ...)`, `MonoidalPreadditive (Sheaf ...)`, `MonoidalClosed (Sheaf ...)`, and `BraidedCategory (Sheaf ...)`, each solved through the consumer's local or global instances. The returned Expr is `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures (Sheaf X.smallEtaleTopology A)`. Canonical is in the array but is never attempted after this success. [FT]

**G1 holds.** In pinned `Lean/Meta/SynthInstance.lean:202-237`, `getInstances` obtains indexed global candidates, stable-sorts by ascending priority, filters erased/private candidates, appends matching locals, then traces the array. At line 608, `generate` selects index `currInstanceIdx - 1`, so it attempts the array from the end. Equal-priority canonical and shortcut appear in that order in the measured consumer array, hence shortcut is attempted before canonical. Opposite-registration minimal controls return `[first, second]` then choose `second`, and `[second, first]` then choose `first`. The controls demonstrate the implementation's tie behavior; they do not prove which historical import introduced each registry entry first. Canonical's applicability is established separately by E3/E5, not by pretending baseline tried it. [FT, FC, IA]

## 12.5 Shortcut's internal synthesis and `_proof_2`

Re-elaborating the shortcut's defining module with its original imports traces its local `have (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance` and the final `inferInstance`. The local tensor witness resolves through graded tensor candidates; the final goal `MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ))` has candidate array `#[HomotopyCategory.MonoidalCategory.instMonoidalCategory, inst✝³]`. The local `MonoidalCategory A` fails by target mismatch; canonical succeeds using the newly available tensor witness and its other recursive arguments. The shortcut is therefore a compiled wrapper around canonical, not a second independent tensor construction. [FT, SA, CE]

During that source compilation the nested `IsRightCancelAdd ℤ` goal has candidates `#[@IsCancelAdd.toIsRightCancelAdd, @AddRightCancelSemigroup.toIsRightCancelAdd, @instIsRightCancelAddOfAddRightReflectLE]`. Search applies the last candidate, recursively resolves `PartialOrder ℤ` and `AddRightReflectLE ℤ` (with failed alternatives), and returns `instIsRightCancelAddOfAddRightReflectLE`. The generated declaration `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures._proof_2` is an opaque theorem of type `IsRightCancelAdd ℤ`, with no instance registration; its printed value is unavailable. The exact post-extraction transformation from the selected provider Expr to that generated theorem body was not dumped. [FT, CE, UNK]

Round 6 measured the first expanded field difference as the left inlined `instIsRightCancelAddOfAddRightReflectLE ...` proof versus the right `_proof_2` constant; all eight parent monoidal data fields are structurally different but Kernel-DefEq true. The common compiled shortcut body contains canonical. A valid dependent-field same-provider rebuild was not run in this round; no claim is made that replacing only `_proof_2` would remove every remaining difference. [CE, UNK]

## 12.6 Same-goal cross-environment matrix

| Goal and local context | Environment/control | Candidate order and outcome | Evidence |
|---|---|---|---|
| Generic `MonoidalCategory C`, local `[MonoidalCategory C]` | Canonical-only import closure | `[local]`; local succeeds | FC |
| Same generic goal/context | Consumer import closure | `[SemiCartesian, local]`; local succeeds | FC |
| Concrete `MonoidalCategory (HomotopyCategory A (.up ℤ))`, local `[MonoidalCategory A]` | Canonical-only closure with needed non-shortcut Mathlib imports | `[canonical, local]`; local mismatch, canonical succeeds after recursive search | FC |
| Same concrete goal/context | Consumer closure | `[SemiCartesian, canonical, shortcut, local]`; local mismatch, shortcut succeeds | FC |

These are controlled replay contexts, not a byte-identical swap of `Environment` around the original theorem's unavailable elaborator metavariable. The generic and concrete rows are different source-time goals. The exact final extracted monoidal argument types were structurally compared in round 6, but a goal hash, local-context ID, environment fingerprint, and per-candidate metavariable assignment dump were not captured in this round. [FC, CE, UNK]

## 12.7 E-experiment outcomes

| Test | Observed result | Evidence |
|---|---|
| E0 old generic source | Only local `MonoidalCategory C` candidate; local wins. Canonical-only concrete proxy selects canonical. | FT, FC |
| E1 add shortcut import to old class-field source | At the field, still only local and local wins; later unrelated rewrites fail, so no complete changed declaration artifact. | FC, UNK |
| E2 exact consumer recompile | Shortcut wins at the concrete homotopy goal; source copy compiles with no errors. | FT |
| E3 suppress shortcut registration | Canonical wins; the shortcut declaration remains present. | FC |
| E4 suppress canonical registration | Shortcut wins; its stored body may still refer to canonical. | FC, CE |
| E5 canonical priority 2000 / shortcut 1000 | Canonical wins. | FC |
| E5 shortcut priority 2000 / canonical 1000 | Shortcut wins. | FC |
| E6 minimal opposite registration orders | Last returned equal-priority entry wins in both variants. | FC, IA |

The priority and registration controls establish applicability and tie mechanics, not the cause of the historical left-hand choice. A faithful import-order swap for the full module graph was not performed. [FC, UNK]

## 12.8-12.10 Explanation, Kernel consequence, unknowns

The consumer choice is fully observed: both global candidates are indexed, the local candidate mismatches, the equal-priority shortcut is tried first in reverse array order, its subgoals succeed, and search stops. The old generic field chooses its local parameter. The canonical left term in the round-6 extracted Expr cannot be attributed to that generic field's candidate search; its exact route through elaboration and reduction remains unknown. Fresh recompiles of two plausible intermediate declarations choose shortcut, and their stored theorem trees contain shortcut rather than a direct canonical application. This is a mixed result: G1 explains the right; the precise left provenance remains unresolved. [FT, FC, CE, IA, INF, UNK]

The different selected instance terms are fixed in elaborated expressions; reloading an imported `.olean` does not re-elaborate its source. Round 6 directly measured the resulting proof/provider divergence inside `tensorObj` and `whiskerRight`, then its propagation into `Functor.uncurry` and the expensive Kernel DefEq path. This round supplies the actual consumer and shortcut-internal search traces, but does not prove the missing left-hand source event or a sole `_proof_2` causal effect. [CE, FT, INF, UNK]

**Section 13 decision:** final instantiated goal types: same; original source-time goals/local contexts: different; relevant candidate sets: different between generic and concrete sites; consumer candidate order: measured; canonical applicable: yes by E3/E5; shortcut applicable: yes by E2/E4/E5; shortcut wins by G1 reverse-array traversal after equal-priority registry ordering; `_proof_2` originates in the shortcut's nested `IsRightCancelAdd ℤ` synthesis and proof extraction; exact route from the inspected compiled theorem trees to the original left canonical Expr: unresolved. No historical candidate attempt is inferred from that Expr alone. [CE, FT, FC, IA, UNK]

Built-in tracing exposed candidate arrays, attempted applications, failure/success, and recursive subgoals, so no Lean search implementation was changed. It did not expose the complete section-10 event schema (call IDs, environment fingerprints, raw goal hashes, all metavariable assignments); those fields and a full historical left trace remain missing. Raw scratch traces were below 2 GB each; the reduced repository files are below 5 MB each and contain no machine addresses or absolute paths. [FT, IA, UNK, FC]
