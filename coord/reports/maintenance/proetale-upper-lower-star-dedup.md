# Pro-etale upper/lower-star ownership repair — 2026-10-16

The canonical owner is `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` in both repositories. The finite-coefficient module only publicly imports it. All 20 explicitly named signatures and declaration bodies are preserved; `overPullbackId` moved to the canonical owner with its existing proof. Both anonymous adjoint instances and both scoped star notations are owned by the canonical module. No mathematical statement, proof, axiom, or sorry was added or changed.

## Inventory before the repair

The current source inventory differs from the older failure description because live commit `99115f75d1` had already reversed the compatibility import:

| Tree | Ordinary Defs | FiniteCoefficient Defs | Direct overlap within the tree |
| --- | --- | --- | --- |
| Side | 19 explicitly named declarations + 2 anonymous instances | `AlgebraicGeometry.ProEt.overPullbackId` | None after `5e80a8ea08` pruned the other copies |
| Live | Compatibility import of finite Defs, no declarations | All 20 names below + 2 anonymous instances | None after `99115f75d1` |

The 19 `AlgebraicGeometry.ProEtale.*` names below were all declared in **side ordinary Defs and live finite Defs**, and in the two side implementations before `5e80a8ea08`. `AlgebraicGeometry.ProEt.overPullbackId` was declared in **side finite Defs and live finite Defs**. The opposed source/artifact owners explain both the duplicate-declaration errors and the missing functors after dropping the import. `lowerStarComp` is included in this inventory. Live commit `1682253199` is the analogous squareTransport dedup in Etale MorphismDefs; it does not itself modify either of these Defs files.

Every explicitly named declaration involved:

- `AlgebraicGeometry.ProEt.overPullbackId`
- `AlgebraicGeometry.ProEtale.additive_upperStar`
- `AlgebraicGeometry.ProEtale.conjugateIsoEquiv_upperStarId`
- `AlgebraicGeometry.ProEtale.hasPointwiseLeftKanExtension_op_overPullback`
- `AlgebraicGeometry.ProEtale.isLeftAdjoint_op_overPullback`
- `AlgebraicGeometry.ProEtale.lowerStar`
- `AlgebraicGeometry.ProEtale.lowerStarComp`
- `AlgebraicGeometry.ProEtale.lowerStarId`
- `AlgebraicGeometry.ProEtale.lowerStar_additive`
- `AlgebraicGeometry.ProEtale.lowerStar_map_hom_app`
- `AlgebraicGeometry.ProEtale.lowerStar_obj_val_obj`
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_lowerStar`
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overPullback`
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar`
- `AlgebraicGeometry.ProEtale.preservesHomology_upperStar`
- `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_lowerStar`
- `AlgebraicGeometry.ProEtale.upperStar`
- `AlgebraicGeometry.ProEtale.upperStarComp`
- `AlgebraicGeometry.ProEtale.upperStarId`
- `AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`

The two anonymous instances give `(g)_*[A].IsRightAdjoint` and `(g)^*[A].IsLeftAdjoint`; the scoped notations are `(g)_*[A]` and `(g)^*[A]`.

## Changes and imports

- Both ordinary Defs files now have identical canonical source. Both finite Defs files declare nothing and re-export the canonical module.
- The explicit side overlay manifest includes **both** Defs paths. This is necessary because a published importer can reach either path without traversing its side source. Precompiling the pair prevents stale live artifacts from reintroducing opposing ownership.
- The existing nine consumers use their finite-module imports to receive the canonical declarations; no consumer proof was changed by this repair.
- The full side-tree scan also found two pre-existing cycles through the frozen `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension` source. Removed exactly three private proof-only imports: `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField`, `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`, and `Sheaf.AlgebraicGeometry.GeometricFiberFinite`. Its statement and body are unchanged, and it compiles without those imports. The active compiler already uses the live replacement of this frozen source.

The ordinary module imports only its six lower-level Mathlib/Weil infrastructure modules. The only compatibility edge is finite Defs → ordinary Defs. No lower-level import reaches either Defs path.

## Graph validation

Used the repository's comment-aware `stage2_delivery.imports` parser on every WeilConjectures/Sheaf Lean source and a full DFS cycle check, including private imports:

| Graph | Modules | Cycles |
| --- | ---: | ---: |
| side | 14171 | 0 |
| live | 14167 | 0 |
| full-side-over-live | 14725 | 0 |
| compiler-overlay | 14725 | 0 |
| union-import-edges | 14725 | 0 |

`full-side-over-live` chooses side source wherever it exists; `compiler-overlay` uses the actual manifest/side-only selection; `union-import-edges` retains import edges from **both** versions of every shared module. All are acyclic.

## Compilation

All checks used the side server compiler `python3 tools/nt_compile.py`, which compiles one Lean file per process, sequentially through prerequisite imports, at nice 19 with two Lean threads and a 60-second limit per file. Live-file checks supplied the live source as a JSON input to that same compiler. No global Lake build was invoked by this maintenance session.

| Tree | File under lean/ | Result | Target-file seconds |
| --- | --- | --- | ---: |
| weil-newtargets | `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean` | PASS | 1.9 |
| weil-newtargets | `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.lean` | PASS | 1.2 |
| weil-newtargets | `Sheaf/AlgebraicGeometry/ProEtaleInverseImage.lean` | PASS | 3.4 |
| weil-newtargets | `Sheaf/AlgebraicGeometry/ProEtaleSupportedSections.lean` | PASS | 1.3 |
| weil-newtargets | `Sheaf/AlgebraicGeometry/ProEtaleFiniteCoefficientDirectImage.lean` | PASS | 2.0 |
| weil-newtargets | `Sheaf/AlgebraicGeometry/FiniteEtaleProEtaleAdjunction.lean` | PASS | 2.1 |
| weil-newtargets | `Sheaf/AlgebraicGeometry/ComparisonPullbackCoherence.lean` | PASS | 3.0 |
| weil-newtargets | `Sheaf/Paper/SupportedCohomologyHom.lean` | PASS | 2.4 |
| weil-newtargets | `Sheaf/Paper/CompactSupportComparisonPullbackCoherence.lean` | PASS | 3.2 |
| weil-newtargets | `Sheaf/Paper/DerivedLocalIsomorphismSheaf.lean` | PASS | 2.7 |
| weil-newtargets | `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Open/Defs.lean` | PASS | 2.2 |
| weil-newtargets | `Sheaf/Paper/ProEtaleFiniteCoefficientDirectImage.lean` | PASS | 1.7 |
| weil-conjectures-sheaf | `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean` | PASS | 2.1 |
| weil-conjectures-sheaf | `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.lean` | PASS | 1.2 |
| weil-newtargets | `Sheaf/AlgebraicGeometry/Sites/AffineTorsionCohomologicalDimension.lean` | PASS | 3.2 |

This covers the two touched Defs paths in each tree, all nine requested consumers, the additional `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage` wrapper, and the affine cycle cleanup. Raw per-file output, declaration inventory, and graph audit are retained under `local/ulsdedup-20261016/` on the server.

## Stage-2 dry run

Ran exactly:

```sh
WEIL_SANDBOX=/home/ubuntu/weil-newtargets-stage2-sandbox SHEAF_LEAD=L-only python3 ~/weil-launcher-nt/deliver2.py ND prop-weil-pbc-cone-independence --no-push
```

Result: exit 0 — `OK (dry run): commit 3ef60c7d61 passes the preflight and compiles; nothing pushed`.

The initial local attempt used an older overlay snapshot and printed the old missing-functor errors; the tool's normal server confirmation compiled the complete delivery successfully against the repaired sources. Refreshed the launcher snapshot with its existing `parallel_land.py overlay` command. A subsequent direct local `scompile.py` check imports both Defs modules and checks `lowerStar`, `upperStar`, `lowerStarComp`, and `overPullbackId`; both sandbox and library compiles pass (2.3 s and 2.7 s), without server fallback. An optional duplicate full dry run was canceled while waiting for a shared repository slot, before it began compilation; the successful requested dry run above is the delivery validation. Logs: `local/ulsdedup-20261016/deliver2-dry-run.log` and `local-import-probe.log`.

Rechecked all five graph variants after concurrent import-restoration commits; every graph still has zero cycles (`audit-final.json`).

## Commit provenance

While validation was running, the existing coordinators included the two source edits in their own commits: side `1ab0e654f0`, live `a02cc2d24c` (both authored Bin Wu <844524296@qq.com>). The remaining explicit overlay manifest and side cycle cleanup were committed under `flock coord/.merge.lock`, `SHEAF_LEAD=L-only`, and the required identity in side `ad273c5762`. This report records the repair separately from those concurrent landing messages. Existing unrelated working-tree changes were preserved.
