## What changed

Replaced the canonical tensor-route parent's dependence on arbitrary-monoidal
transport with direct tensor/counit normalization, valid for every homotopy
complex. The canonical parent statement is unchanged. Withdrew the assigned
K-flat module and removed its only use together with the obsolete descent import.
Removed `integralResidue_tensorRoute_model_transport`, whose arbitrary monoidal
parameter conflicts with the fixed canonical model map on its right side.

The current upstream model already accepts its named derived functor and counit
through `tensorModelMapWith`, matching `tensorModelTargetWith`; that API is retained.
Added fully proved APIs for model normalization,
ordinary pullback braiding, and the derived tensor/counit square in their existing
construction modules. Concrete construction scopes select the same existing
ambient sheaf braiding. Derived monoidality retains its original oplax fields
directly. These are definitionally equal data, with no target-meaning change.
The scalar-geometry and tensor-geometry consumers have necessary proof-only
unfolding adaptations, with their statements and hypotheses unchanged. The current
scalar-counit consumer already contains its required adaptation and is retained
verbatim, including the upstream proof changes.
The model's proof imports the existing source module
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided` for the generic
homotopy braiding equation. Its ten additions to the targets' import closure are
all free of `sorry`; this route adds no unresolved proof obligation to that closure.

Change records: `coord/changes/C2-canonical-residue-tensor-route.md` and
`coord/changes/C2-residue-tensor-named-data-api.md`.

Repair validation: `lcompile.py --all` compiled all seven sandbox modules on the
server without errors or warnings. The scalar-counit source exactly matches the
current shared source. The import-direction check permits the added braiding
import. The delivery dry run reached preflight but did not push; its tool failure
is recorded below.

## Proved and sorry left

The assigned module originally had one hole,
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_kFlat`.
Its assertion is disputed and the unused module is withdrawn: this is pruning,
not a proof of that false assertion. Original holes proved: 0 of 1. New holes: 0.
No sorry remains in the changed Lean files.

The unchanged canonical theorem `integralResidue_tensorRoute_model` has a direct
proof from the new, fully proved `CategoryTheory.Functor.tensorModelRoute_fac`,
`CategoryTheory.Functor.residueDerivedMonoidal_counit`, and
`AlgebraicGeometry.ProEtale.CondensedRing.residueOrdinaryUpperStar_braiding`.
The scalar-counit consumer also compiles with its unchanged statement.

## No longer needed

- `Sheaf.Paper.IntegralResidueTensorRouteKFlat` and node
  `new-integral-residue-tensor-route-kflat`: withdrawn, with no remaining importer.
- `integralResidue_tensorRoute_model_transport` and node
  `new-integral-residue-tensor-route-transport`: removed, with no remaining user.
- Parent import `Sheaf.Paper.IntegralResidueTensorRouteDescent` and node
  `new-integral-residue-tensor-route-descent`: no resolving-class descent is used.
  Its file is not changed; it is held by A2.
- Parent proof imports `IntegralResidueDerivedMonoidal` and
  `IntegralResidueTensorPresentation` are supplied by the model interface and
  need no separate import. The separate ordinary-construction import is likewise
  redundant once the model interface supplies the proved APIs.

No realized blueprint-unit statement or proof step is removed. The pruning is
below the unit's proper-base-change route.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the K-flat and transport statements quantify over arbitrary
ordinary monoidal structures, but their model map fixes the canonical one.
Negating both the lax tensorator and the monoidal unit gives another strong
monoidal structure, with negated oplax tensorator. The derived comparison depends
linearly on that tensorator, so the left side changes sign while the fixed right
side does not. For odd residue characteristic, identity pullback on a nonempty
geometric point and the degree-zero unit complex give a nonzero residue map.
The unit complex is K-flat, so K-flatness cannot repair this mismatch.

The canonical theorem needs neither a K-flat representative nor a descent step:
the defining tensor/counit equation and naturality hold for every homotopy complex.
The relevant source commutation is Bhatt--Scholze Lemma 6.5.9(5); part (3) concerns
the projection formula. No statement of `Challenge.lean` changes.

Repair of return C-55a79 (reviewed head `55a7970b7`): the prior delivery passed
review but could not land because `IntegralResidueScalarCounitModel.lean` changed
after its base `8074ba108`. Compared the retained sandbox with the current shared
source. The current scalar-counit file already unfolds `tensorModelMapWith` and
`residueExchangeTensorCounit`, so its required adaptation has landed independently.
Copied that current file verbatim into the sandbox; it contributes no file change
to this delivery. The canonical-route proof and withdrawal remain substantive
changes. The delivery tool rebuilds the delivery on the freshly fetched
`sheaf-dag` base; no direct git operation is performed in the shared repository.

The repair dry run failed with exactly one preflight reason:
`(a) uncommitted changes in the working tree`. The current `deliver3.py` writes
tracked `tools/stage3_gate.py` and `tools/stage3_delivery.py` after creating the
delivery commit, then invokes preflight without `--branch`; preflight rejects
the dirty working tree produced by the delivery tool itself. The worker contract
forbids modifying or working around delivery tools. Nothing was pushed.
Separately, the dry run reported that the appended axiom probe for
`IntegralResidueScalarGeometryBridge` timed out after 60 seconds; its ordinary
server compile passed. This probe note was not the preflight rejection reason,
and a compile timeout is not being classified as the tool failure.

## New nodes

`new-integral-residue-derived-monoidal-counit` records the fully proved defining
square of the derived tensorator in the existing derived construction module.

`new-integral-residue-ordinary-braiding` records the fully proved braiding equation
for canonical ordinary module pullback in its existing construction module.

`new-integral-residue-tensor-model-route-fac` records generic model normalization
from that square, braiding and the canonical presentation counit in the existing
model module. None adds a module or a sorry.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
