## What changed

Replaced the proof of
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_single`, retaining
its complete theorem header, public imports, coefficient predicate, and constructibility
predicate. The proof refines the two constructible stratifications, computes the tensor
on each noetherian stratum, descends the lower bound, and witnesses constructibility of
homology on that same stratification. The upper bound is the existing generic
`DerivedCategory.isLE_tensor` theorem.

Two new modules contain proved local calculations. `LocallyFreeTensorSingle` distributes
tensor over a finite free chart, identifies the coefficient sheaf with the tensor unit,
and descends vanishing and local finite presentation from a pro-etale cover.
`LfpTensorSingle` treats field coefficients by local triviality and integral coefficients
by the existing `integral_lfp_locallyFree_resolution`. Tensoring its short exact triangle
and rotating gives the lower bound -1. The weak Serre homology property gives locally
finitely presented cohomology. The integral and unit-ball coefficient constructors are
identified with the actual continuous integral coefficient ring.

All additions to the existing module's imports are proof imports. The proof reuses
existing proved private presentation/cover comparisons with `import all`, including
`common_lfp_stratification`, `abDetectMaps`, `algcl_lf`, the local integral kernel API,
and the generic local cokernel/extension API. No existing definition, signature,
visibility, target, or consumer is changed. No data definition chooses witnesses from
an unproved mere-existence theorem: the resolution is destructured only inside a proof;
the new isomorphisms are explicit categorical constructions.

The three modules compiled together cleanly in dependency order, within the original
60-second per-file limit (about 1, 34 and 25 seconds in the successful run). No compiler
limit is raised. The local calculation keeps `DerivedCategory.TStructure.t` locally
irreducible and supplies explicit integer equalities, avoiding expensive unfolding and
default arithmetic search. Temporary profiling and diagnostic commands were removed.
The final import-minimization compile also passed cleanly: 32.3, 32.0 and 25.7 seconds
for the finite-free, locally finitely presented, and assigned modules respectively.
The first delivery preflight correctly classifies the removed item as a new module:
its original B2 creation metadata no longer matches that baseline. This is repaired
by recording C4 as the reintroducing worker and adding the restoration change record.
The recovered statement, source, statement dependencies and public imports remain
unchanged; historical review markers are left to the current independent review.
The repaired dry run passes compilation and preflight and is classified CODEX, as
expected for the restored item, new nodes, and restoration change record.

## Proved and sorry left

Original holes closed: one of one,
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_single`
(node `lem-sfb-dc-tensor-single`).

New holes added: zero. Sorries left in delivered Lean files: none. Both new public
theorems, `AlgebraicGeometry.ProEtale.CondensedRing.locallyFree_tensor_single` and
`AlgebraicGeometry.ProEtale.CondensedRing.lfp_tensor_single`, and every private helper
have complete proofs. This is a proof from existing library declarations, rather than
a split of the original hole. Existing postponed inputs in the imported theory,
including the integral local chart/pivot theory, remain existing obligations.

Edge cases: the finite-free calculation includes rank zero via the empty biproduct;
zero homology has the empty finite presentation. Covers and strata may be empty.
The descent proof uses the finite jointly surjective stratum family and its
quasi-compact immersions, supplied by the noetherian geometric setting. Local
field triviality is used on the noetherian base/strata, never on arbitrary cover
schemes. Integral torsion is retained by the short exact resolution.

## No longer needed

No original public import is removed. The following old direct proof dependencies are
unnecessary for this proof route, and their dedicated modules are not imported:

- `lem-sfb-integral-lfp-constant-model-comparison`
  (`Sheaf.Paper.IntegralLfpConstantModelComparison`): a locally finite free resolution
  suffices without replacing the local-finite-presentation predicate by scalar models.
- `lem-weil-l-adic-extension-integers-dvr`
  (`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`) and
  `lem-sc-dvr-saturation-line-smith-normal-form`: no scalar cyclic decomposition is used.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): the existing normalized
  internal-module inverse image already has its monoidal derived comparison.
- `lem-weil-pbc-noetherian-stratum-detection`
  (`Sheaf.AlgebraicGeometry.NoetherianStratumDetection`): the already proved
  `abDetectMaps` API detects vanishing directly along the finite stratum immersions.
- `lem-weil-pbc-site-pullback-abelian-exact`
  (`Sheaf.CategoryTheory.SitePullbackAbelianExact`): exactness and homology comparison
  are already in the actual inverse-image functor's API.
- `def-pc-kflat-complex` (`Sheaf.Algebra.Homology.KFlat`): no explicit two-term K-flat
  cyclic resolution or cone calculation is needed.

These old direct dependencies move into reused APIs or remain definitions, rather than
being discarded mathematically: `lem-weil-pbc-condensed-lfp-local-triviality` and
`lem-weil-pbc-condensed-qbar-lfp-local-triviality` are used by `LfpTensorSingle`;
`lemma-constructible-pullback-stratification` is used through common refinement;
`sk-def-sfb-condensed-ring`, `sk-def-sfb-pullback-from-point`,
`sk-def-sfb-pulled-back-coefficients`, `sk-def-sfb-qlbar-condensed`, and
`def-weil-abstract-derived-category` remain the underlying definitions. Their old
standalone proof steps are removed from the item node. No assertion is made that
these modules become unreachable from every other target.

The exploratory import of `Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated` was
removed: only its field-comparison helper was relevant, and the actual field
local-triviality theorem plus the existing coefficient isomorphism suffices directly.
No new theorem depends on that module. The new local-finite-presentation module also
omits the redundant public `ModuleObject.Basic` import (already exported by
`Derived.Tensor`). The finite-free module publicly imports only the tensor structure
needed by its statement and imports `Derived.Monoidal` privately for its proof.

## Where the brief, the DAG or earlier work was wrong

The scalar-model/DVR plan is longer than needed given the existing two-term locally
finite free integral resolution and the proved local weak Serre APIs. The updated
nodes record the actual argument. The item's statement is not disputed or weakened.
The unit `sk-def-sfb-dc-restricted-functors` keeps its tensor-preservation step and
restricted functor route; the change is below that unit.

During this session the shared repository rolled back the B2 landing which introduced
this item, and removed both its module and its node. The rollback repair record is
`coord/repair-notes/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible.json`.
The sandbox retains the original module and recovers the original node from that
record. The theorem header matches that original text exactly. The rollback's failing
importer and repair belong to the parent item; this delivery changes only the assigned
module and its two new local calculation modules.

Generic tools from the proper-base-change development are reused below the tensor
unit: local finite presentations and coefficient comparisons, joint abelian detection,
and the integral locally finite free resolution/local kernel theory. The derived
weak-Serre homology theorem is generic categorical machinery. They do not replace a
unit-level step. No maintainer `tool_uses` approval is added by this worker.

## New nodes

`lem-sfb-dc-tensor-single`, module
`Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle`: reintroduced after the
upstream rollback removed the assigned node and module from the delivery baseline.
Its statement, source and statement dependencies are recovered unchanged; its proof,
proof dependencies, creation record and Lean authorship now describe this C4 delivery.
The pre-rollback B2 review markers are omitted so that the reintroduction receives its
own independent review. This is the assigned theorem, not an additional split-off.
The restoration change record is
`coord/changes/C4-restore-bounded-constructible-tensor-single.md`.

`lem-sfb-locally-free-tensor-single`, module
`Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle`: the tensor calculation when the
first sheaf is locally finite free, over arbitrary commutative condensed coefficients;
fully proved, including local-to-global descent.

`lem-sfb-lfp-tensor-single`, module `Sheaf.AlgebraicGeometry.LfpTensorSingle`:
the lower bound -1 and local finite presentation of all tensor cohomology for two
locally finitely presented ell-adic coefficient sheaves on a noetherian space;
fully proved from the finite-free calculation, field triviality, and the integral
resolution. Both nodes cite Bhatt--Scholze 6.8.11(3), record the three kinds of actual
logged searches, and inherit the item's chapter and unit. Blueprint searches found
no existing node with either local calculation statement. The rollback restoration is documented in
`coord/changes/C4-restore-bounded-constructible-tensor-single.md`.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
