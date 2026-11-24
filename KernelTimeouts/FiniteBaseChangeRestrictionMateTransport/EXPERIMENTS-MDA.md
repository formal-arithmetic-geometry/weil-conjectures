# MDA attribution: FiniteBaseChange

## Scope and evidence

The source declaration is `finite_base_change_restriction_mate_transport` at revision `0676f555de6410290e94024fe84ba51c2f73fde7`; the measurement import tree is `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`, Lean 4.35.0. The measured conversion is argument 49 (`hb`) of private `transport_from_unit`, after the first 48 dependent arguments are instantiated. `probes/mprwe/Original.lean` is the original probe. The exact S2 root pair and local context are in `EXPERIMENTS-MOE.md` and `ccmoa/S2-S4-site-proet.snapshot`; new kernel Exprs and costs are in the `mda/` artifacts.

Source supplies a concrete square using `Scheme.ProEt X`; the helper expects a square using `Site .ordinary X`. The outer `forall M : FiniteModules A X'` and `Eq` skeleton agree. The S2 first structural divergence of the isolated site pair is `root/fn`: `Scheme.ProEt` constant versus `Site` application to `Mode.ordinary`, with the same scheme argument. In the instantiated `hb` proposition this sits in a `Quiver.Hom` type below `ProjectionRestriction.Mod`, on both sides of the equality. `Site` has hint `regular:20` and its ordinary-mode body reduces to `Scheme.ProEt` (`regular:19`). This source/API difference is D; it is separate from the later projection cascade.

## 4.1 Gateway-to-cost

| Gateway ID | Parent M0 path | Kernel branch | Exact child pair | Source/API candidate | Subtree calls / M1 calls | Subtree comparison-exclusive | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| 16563:2 (parent 1) | `root/binder_body[1]` | `quick` dependent body | `Eq` / `Eq`; left `ProjectionRestriction.Mod (Scheme.ProEt X) ...`, right `ProjectionRestriction.Mod (Site .ordinary X) ...` | instantiated `hb` equality body | 239,340,711 / 130,197,227 | 1,238,807.422 ms | S: exact Expr pair and S2 join |
| 16563:7823 (parent 2) | `.../argument[2]` | application argument 2 | `CategoryStruct.comp` / `CategoryStruct.comp` with `instCategoryProEt` / `instCategorySite` | composition under dependent `Quiver.Hom` | 239,332,890 / 130,191,839 | 1,233,203.176 ms | S: first dominant internal child |
| 16563:7937 (parent 7936) | `.../argument[6]/argument[5]/binder_body[1]/whnf` | `second_whnf` | `ModuleCat.Hom._mkInternal` / same | concrete module-Hom exposure | 239,325,566 / 130,186,706 | 1,232,236.300 ms | S: nested path node |
| 16563:8494 (parent 8493) | `.../argument[4]/argument[20]/projection[0]` | projection field 0 | `PresheafOfModules.Hom.proj` / same | Hom projection chain | 239,324,552 / 130,186,142 | 1,231,825.045 ms | S: nested path node |
| 16563:8496 (parent 8495) | next projection | projection field 0 | `SheafOfModules.Hom.proj` / same | sheaf-Hom component | 239,324,549 / 130,186,140 | 1,231,799.735 ms | S: nested path node |
| 16563:8497 (parent 8496) | next projection | projection field 0 | `Functor.proj` / same | functor component | 239,324,548 / 130,186,139 | 1,231,793.696 ms | S: nested path node |
| 16563:8530 (parent 8497) | `.../argument[2]` | application argument 2 | `NatTrans.app` / same | natural-transformation component | 239,324,515 / 130,186,131 | 1,231,791.290 ms | S: nested path node |

The new MDA trace has 239,340,712 calls, 130,197,227 M1, 40,495,866 M2, 68,647,618 Matched, and 1,239,204.129 ms comparison-exclusive. M1 direct time is 878,808.871 ms and M2 direct time is 343,169.605 ms. The earlier READY4.2 813.896 s comparison-exclusive is a lower-overhead baseline; the call counts and within-trace partitions are the stable comparison. The selected child pair at 7823 retains the `ProEt`/`Site` and `instCategoryProEt`/`instCategorySite` differences. `Quiver.Hom` and `Site` occur in its type, but the first dominant *recursive child* is the equality body at 2, then `CategoryStruct.comp` at 7823. The first delta event for `Site` is not isolated as the owner of this subtree. Nested inclusive times must not be summed.

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen | Kernel path | M1 calls | M1 exclusive | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `Scheme.ProEt X` versus `Site .ordinary X` | producer | S0/S2 | `hb` `Quiver.Hom` site leaf | 130,197,227 root total | 878,808.871 ms root M1 direct | whole-`hb` transport | D |
| `Site` ordinary-mode definition and `instCategorySite` | representation path | S4/S6; exact pair at 7823 | delta/category argument | not separately isolated | not separately isolated | no valid one-factor leaf cut | S for presence; P for isolated cost |
| instantiated `Eq` body / `CategoryStruct.comp` | gateway | calls 2 and 7823 | dependent body, then application argument 2 | 130,191,839 under 7823 | 1,233,203.176 ms inclusive, overlapping with 2 | local `hb` leaf alignment is a no-op | S |
| `ModuleCat.Hom._mkInternal`, `LinearMap.comp`, `PresheafOfModules.Hom.proj`, `SheafOfModules.Hom.proj`, `Functor.proj`, `NatTrans.app` | downstream amplifier path | calls 7937-8530 | WHNF, application, projections | 130,186,131 under 8530 | 1,231,791.290 ms inclusive, overlapping with 7823 | whole-`hb` transport | S path |
| projection field 0 | amplifier component | complete `mda_group` | projection | 98,782,787 direct | 329,175.321 ms direct | no isolated field control | S branch, P exact field identity |
| dependent body 1 | amplifier component | complete `mda_group` | quick | 19,907,361 direct | 330,838.233 ms direct | no isolated local control | S branch |
| structure eta field 0 | amplifier component | complete `mda_group` | eta structure | 19,741,562 direct | 297,236.093 ms direct | no isolated local control | P field identity |

## 4.3 Root-to-source chain

Source concrete `Scheme.ProEt X` square -> helper's instantiated `Site .ordinary X` square (S2 M0) -> dependent `hb` proposition under `forall`/`Eq`/`Quiver.Hom`/`ProjectionRestriction.Mod` -> equality body at call 2 -> `CategoryStruct.comp` argument at call 7823, with `instCategoryProEt`/`instCategorySite` still in the exact pair -> `ModuleCat.Hom._mkInternal`, `LinearMap.comp`, `PresheafOfModules.Hom.proj`, `SheafOfModules.Hom.proj`, `Functor.proj`, `NatTrans.app` -> 130,191,839 M1 calls and 1,233,203.176 ms inclusive under call 7823. Source-to-M0 is D; the measured gateway/path is S. A distinct `Site` delta share is still P, since an unfolded constant is not automatically the gateway owner.

## 4.4 Summary

| Case | Producer | Expansion gateway | Cost amplifier | Best intervention | Evidence |
| --- | --- | --- | --- | --- | --- |
| FiniteBaseChange | concrete `ProEt` versus instantiated `Site .ordinary` (D) | dependent equality body at call 2, composition argument at 7823 (S); isolated `Site` delta share P | category/Hom projections, structure eta, and dependent bodies (S path; P field split) | whole-`hb` transport: 239,340,712 calls -> 19,783 captured largest-root calls; restoring concrete `h` -> 239,340,712 | D API counterfactual; M0 changes |

Whole-argument transport keeps the helper, first 48 arguments, consumer, local context, and final theorem obligation, but changes the argument proposition and M0. The local `hb` alignment leaves the original root unchanged, so it is a negative control. The effective boundary is fragile: replacing transported `hb` with concrete `h` restores the expensive path. The 19,783-call control result is the largest threshold-zero captured root in that file, not a paired root ID, so cost relocation within the fast variant is not isolated. No causal Elaborator-provider or declaration-finalization claim follows from the available data.

## Audit note

The `ProEt` versus `Site .ordinary` producer is **D** from the exact S2 pair.
The dependent-body and composition gateway is **S**; the selected rows are
inclusive and the isolated `Site` share is therefore only **P**. Whole-`hb`
transport and restoration demonstrate an API-level boundary, not an M0-
preserving field cut.
