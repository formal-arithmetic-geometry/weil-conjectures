# Slow Derived Tensor: Monoidal Instance Provenance Report

## Evidence and environment

**Direct root evidence** means READY4.2 on the exact historical lemma comparison. **Direct child replay** means a Kernel comparison of an Expr extracted from that lemma, in the same local context. **API-level counterfactual** means a rebuilt, Kernel-checked Expr with an argument changed. **Direct environment audit** means declarations, instance registry, source, and history at the pinned revisions. **Inference** and **Unknown** mark conclusions beyond those observations. These labels apply to each table row through its evidence column. [Direct environment audit]

All fresh measurements used Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11cda51a86af692955474`, consumer `bdab171985a`, and observational READY4.2. Each process had a 3600 s timeout; at most three investigation Lean processes ran at once. No Kernel decision logic or historical source was changed. The initial exploratory run in a later checkout was discarded before attribution. [Direct environment audit]

The fresh exact `M0` root returned `true` with 6,239,533 calls. A counters run took 71.797 s instrumented root wall time, and a trace run took 59.466 s; the different wall times reflect current load, while calls agree with Stage I. The traced root's disjoint `Functor.mk` field subtrees were `obj` 0.401 s, `map` 18.016 s, `map_id` 0.805 s, and `map_comp` 40.241 s. Their sum differs from the traced root by only the surrounding nodes. [Direct root evidence; Inference for load attribution]

## 1. Exact declarations

| Side | Declaration, construction, and arguments | Registry and hint | Evidence |
|---|---|---|---|
| Left | `HomotopyCategory.MonoidalCategory.instMonoidalCategory.{u_1,u_2,u_3}`: 19 arguments, including category, preadditive and monoidal structures, graded `HasTensor`, colimit preservation, graded coherence, decidability, and `HasMapBifunctor`; body applies `MonoidalCategory.ofBifunctor` to `unit`, `bifunctor`, associator, unitors, pentagon, triangle. | Global, priority 1000; regular(24). | Direct environment audit |
| Right | `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures.{v,u}`: 8 arguments for an abelian, cocomplete, monoidal, preadditive, closed, braided `A`; body introduces `have (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance`, then synthesizes the homotopy monoidal instance. | Global, priority 1000; regular(25). | Direct environment audit |

The exact declaration types and printed elaborated values are in `sdtprov/declarations.txt`. The right wrapper generates `_proof_2 : IsRightCancelAdd ℤ`, a theorem, not an instance-registry entry. `MonoidalCategory.ofBifunctor` has regular(5) and fills the parent structure from the bifunctor's object and map fields. [Direct environment audit]

## 2. Source and history

The left declaration is in `WeilConjectures/FromJoel/Algebra/Homology/HomotopyCategory/Monoidal.lean:235`; the right is the anonymous instance in `WeilConjectures/CategoryTheory/Monoidal/Instances/HomotopyCategory.lean:28`. The former was migrated with the August 2026 code; the shortcut file appears in the September 2026 derived-category change. The consumer source imports `HasMonoidalDerivedCategory` and `Instances/DerivedCategory`, while `HasMonoidalDerivedCategory` imports the shortcut after the migrated derived-monoidal module. The reduced history is in `sdtprov/*-history.txt`. [Direct environment audit]

## 3. Selection at `curriedTensor`

The exact extracted `Functor.comp` has `curriedTensor C` at source argument 6. Its own argument 2 is `MonoidalCategory C`. The left elaborated term supplies `HomotopyCategory.MonoidalCategory.instMonoidalCategory` with 19 arguments; the right supplies `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures` with 8. The source category and its category instance at curried arguments 0 and 1 are pointer-shared, and the instantiated monoidal argument types are structurally identical. [Direct child replay]

The left term was fixed in the earlier `Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂` proposition when that declaration was elaborated. At the later consumer call, typeclass synthesis has the global shortcut available and selects it. Neither term is an explicitly supplied `curriedTensor` instance argument, a local instance at the call site, or a transport. This path is reconstructed from import order, source and the final Expr; a historical elaborator search trace was not retained. [Direct environment audit; Direct child replay; Inference for the synthesis search order]

## 4. Construction ancestry

```text
shared coefficient MonoidalCategory and graded tensor machinery
  -> HomologicalComplex tensor data and its induced monoidal structure
  -> HomotopyCategory.MonoidalCategory.bifunctor
       = curriedTensor.bifunctorMapHomotopyCategory (quotient lift)
  -> HomotopyCategory.MonoidalCategory.instMonoidalCategory
       = MonoidalCategory.ofBifunctor(unit, bifunctor, associator, unitors, laws)
       -> left direct application
       -> right shortcut: local graded HasTensor witness; inferInstance
            -> generated IsRightCancelAdd ℤ proof provider
```

The right declaration is a shortcut around the canonical migrated instance, not an independent tensor functor, equivalence transport, or different mathematical tensor. Its elaborated value contains the canonical `instMonoidalCategory` constant (`sdtprov/ancestry.txt`). Both expand to `MonoidalCategory.mk/13`, whose parent expands to `MonoidalCategoryStruct.mk/10`; both use the same `.ofBifunctor` recipe and quotient-lift bifunctor ancestry. The first common instance ancestor is the migrated `instMonoidalCategory`; the first divergent assembly step is the shortcut's locally synthesized witness/provider arguments. [Direct environment audit; Direct child replay]

## 5. Field comparison

In parent field order, `tensorObj` is the first structurally unequal field. All eight parent fields are nonidentical Exprs but Kernel DefEq returns `true`. Their instantiated type Exprs are structurally unequal too (recorded in `sdtprov/j-types.txt`); conversion of the well-typed field values succeeds. The first unequal child in each expanded field is the left expanded `instIsRightCancelAddOfAddRightReflectLE ...` proof versus the right generated `_proof_2 : IsRightCancelAdd ℤ`; this is a proof/provider difference inside dependent tensor construction, not evidence for different mathematical tensor data. [Direct child replay; Direct environment audit; Inference for type convertibility]

For both sides, `.ofBifunctor` defines `tensorObj X Y = (F.obj X).obj Y`, `whiskerLeft X g = (F.obj X).map g`, and `whiskerRight f Y = (F.map f).app Y`; `tensorHom` uses its default right-then-left whiskering composite. The remaining parent fields are the common `unit`, componentwise `associator`, and componentwise unitors. Their `F` terms descend from the same quotient-lift bifunctor declaration but carry the different proof providers. The law fields are generated by the same `.ofBifunctor` proof constructors, with dependent proposition types assembled from those parent fields. [Direct environment audit; Direct child replay]

| Parent field | Structural Expr equal? | DefEq? | J wall | Original-root route | Evidence |
|---|---|---|---:|---|---|
| `tensorObj` | No | Yes | 0.413 s | `curriedTensor.obj`, then `U.obj` and morphism domains | Direct child replay; Direct root evidence |
| `whiskerLeft` | No | Yes | 0.871 s | Inner functor `map` | Direct child replay; Inference from source |
| `whiskerRight` | No | Yes | 15.058 s | Outer `NatTrans.app` | Direct child replay; Inference from source |
| `tensorHom` | No | Yes | 17.695 s | No direct projection observed in original `curriedTensor` path | Direct child replay; Direct root evidence |
| `tensorUnit` | No | Yes | 0.001 s | No direct projection observed | Direct child replay; Direct root evidence |
| `associator` | No | Yes | 12.154 s | No direct projection observed | Direct child replay; Direct root evidence |
| `leftUnitor` | No | Yes | 2.464 s | No direct projection observed | Direct child replay; Direct root evidence |
| `rightUnitor` | No | Yes | 3.229 s | No direct projection observed | Direct child replay; Direct root evidence |

The ten law fields (`tensorHom_def`, identity/composition and whiskering laws, associator/unitor naturality, pentagon, triangle) are also structurally unequal and separately DefEq-true. Their J replays range from 0.547 s (`whiskerLeft_id`) to 134.138 s (`pentagon`), because proof irrelevance still compares dependent proposition types. These are independent J comparisons, not root costs or proof-body execution. Full field-by-field results and first-difference paths are in `sdtprov/j-fields.txt`; counters are in `j-counters.txt`. [Direct child replay]

## 6. Root reachability

The original root reaches `Functor.uncurry`'s `obj`, `map`, `map_id` proposition and `map_comp` proposition. The `map` expression uses source `tensorObj` for domains, `whiskerRight` in the first composite factor and `whiskerLeft` in the second. The `map_comp` equality endpoints repeat those factors through target composition. No direct projection of `tensorHom`, unitors, associator or monoidal coherence proofs was observed on this root path. Presence in the instance constructor alone is not charged as root work. [Direct root evidence; Direct environment audit; Inference for field-to-expression mapping]

## 7. K1: object field

`curriedTensor.obj X` has object function `Y ↦ X ⊗ Y`, hence projects `tensorObj`. The resulting source object passes through `toDerivedMonoidal.obj`, definitionally `Qh.obj`, into `U.obj`. The fresh `U.obj` child replay succeeded in 56,018 calls and 0.391 s instrumented time (0.433 s enclosing wall). Its small share relative to morphism fields is observed; the explanation is that it avoids the repeated localized Hom/composition endpoints. [Direct child replay; Direct environment audit; Inference for relative-cost mechanism]

## 8. K2/K3: inner and outer maps

The inner functor map `X ◁ g` projects `whiskerLeft`; the outer `curriedTensor.map f` constructs a natural transformation whose `app Y` is `f ▷ Y`, projecting `whiskerRight`. `Functor.comp` applies `toDerivedMonoidal.map` to each. `Functor.uncurry.map` then compares `(F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2`, in the target `DerivedMonoidal` Hom. Its composition is the localized target `CategoryStruct.comp`. The source formula and the fresh curried/uncurried field Exprs establish this route; the separate causal effect of each field is tested in L. [Direct environment audit; Direct child replay; Inference for transport reduction]

## 9. K4: `map_comp` and proof fields

The generated `map_comp` proof body is skipped by proof irrelevance. Its proposition has five structurally shared binder domains, then an `Eq` whose type is a target `Quiver.Hom` and whose two endpoints head with `CategoryStruct.comp`. Fresh, independent child replays: Hom type 112,002 calls/0.884 s; first endpoint 1,902,432 calls/14.698 s; second endpoint 3,301,411 calls/26.354 s. The two endpoints are not charged to J fields, and these replay times are not added to the same-root `map_comp` 40.241 s. [Direct child replay; Direct root evidence]

The original endpoints contain `whiskerLeft`, `whiskerRight`, `tensorObj`-dependent domains, `Qh.map`, and target composition through the displayed `uncurry` map. `Functor.map_comp`, `NatTrans.comp_app`, naturality and associativity appear in the source proof construction, but their proof bodies and monoidal law proofs are not executed as the expensive equality endpoints are compared. The original root does compare the dependent propositions of `Functor.uncurry._proof_2` and `_proof_3`; the shortcut's `IsRightCancelAdd ℤ` proof occurs in dependent tensor terms. The monoidal law propositions can be costly in standalone J checks, but direct original-root reachability of those law projections was not observed. [Direct environment audit; Direct root evidence; Direct child replay; Inference for reduction route]

## 10. L: causal interventions

The controls replace one parent data field at a time with the corresponding left field while retaining every other right field and law proof. Each rebuilt final `U` passed `checkWithKernel`, and every measured DefEq returned `true`. The new `U`, `map`, and `map_comp` measurements below are separate direct child replays; times are READY4.2 instrumented total milliseconds, converted to seconds. Every row is an API-level counterfactual and leaves the exact `M0` obligation unchanged in the repository but does **not** preserve that obligation as its measured comparison. [API-level counterfactual; Direct child replay]

| Aligned field | Rebuilt `U`: calls / time | `map`: calls / time | `map_comp`: calls / time | M0 preserved? | Restoration | Evidence |
|---|---:|---:|---:|---|---|---|
| `whiskerRight` only | 617,758 / 4.424 s | 168,438 / 1.049 s | 337,275 / 2.268 s | No | Fresh E0 at end: 6,239,463 / 51.735 s | API-level counterfactual; Direct child replay |
| `whiskerLeft` only | 6,238,713 / 52.444 s | 1,902,253 / 14.920 s | 4,196,413 / 33.943 s | No | Same fresh E0 restoration | API-level counterfactual; Direct child replay |
| `tensorObj` only | 6,043,673 / 51.060 s | 1,846,464 / 14.424 s | 4,140,945 / 33.904 s | No | Same fresh E0 restoration | API-level counterfactual; Direct child replay |

`whiskerRight` alignment removes about 90% of `U` calls and 91% of its measured time, but leaves a smaller comparison. `whiskerLeft` alignment leaves the full expensive call path. `tensorObj` alignment removes 3.1% of `U` calls and 1.3% of `map_comp` calls, while its 1.3% time difference from the restored run is not material against run variation. Each candidate starts with the original right parent, so replacements do not accumulate; the final E0 replay verifies return of the expensive path. `tensorHom` and law fields were not separately aligned because no direct original-root projection to them was observed. [API-level counterfactual; Direct child replay; Inference for materiality]

The interventions rebuild a `MonoidalCategoryStruct.mk` parent and `MonoidalCategory.mk` wrapper, then Kernel-check the final uncurried `U` containing those terms before comparison. They alter API-level source terms; none preserves the exact `M0` obligation. `tensorHom` and coherence fields are not intervened on absent direct root reachability. [API-level counterfactual; Direct root evidence]

## 11. First ancestors and repair scope

The common ancestor is the canonical migrated homotopy-category instance and its quotient-lift tensor bifunctor. The first divergence is the shortcut's generated proof/provider path, which is already visible in `tensorObj`; the remaining fields inherit the same provider difference. Sharing the exact canonical `MonoidalCategory` term at the two `curriedTensor` sites removes the expensive uncurried path in the fresh E1 control (`F` 1 ms, `U` 4 ms, `map` 1 ms, `map_comp` 2 ms; all Kernel-valid). This is an API-level counterfactual, not an `M0`-preserving local cut. [Direct environment audit; Direct child replay; API-level counterfactual]

## 12. Remaining uncertainty and decision

No historical elaborator trace records the sequence of failed and successful candidates, so the reason for the right selection is reconstructed from imported global instances and the final elaborated Expr. The isolated effect of replacing only the generated `IsRightCancelAdd ℤ` proof provider was not measured. Target localization/composition remains the cost context; Stage I did not find it to be an independent producer among tested non-instance factors. [Unknown; Direct environment audit; Direct child replay; Stage I API-level counterfactual]

**§14 decision: Outcome A, instance-only producer supported among tested factors.** Stage I found no reproducible material non-instance effect; the pinned fresh `M0` reproduces the expensive path, and fresh E1 alignment of only the source monoidal instance removes it. L identifies `whiskerRight` as the dominant single-field transmitter; `whiskerLeft` is used by the source map but its isolated alignment does not remove the path. This does not exclude untested factors or prove a Kernel implementation defect. [Direct root evidence; API-level counterfactual; Direct child replay; Inference]

Reduced, path-neutral probes and outputs are in `sdtprov/`. All files are below 5 MB. No commits or pushes were made. [Direct environment audit]
