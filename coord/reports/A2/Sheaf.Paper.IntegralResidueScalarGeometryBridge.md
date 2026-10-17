## What changed

Repaired the retained returned delivery against the current shared source after the
upstream synchronization. The return requested recompilation against the source; this
repair also replaces the expensive inline ordinary coefficient isomorphism in both new
counit statements with the fully constructed generic
`residueOrdinaryRestrictedRegularPullIso`. Its body is exactly restriction/pullback on
the regular residue module followed by restriction of the inverse monoidal unit.
It uses no unproved existence theorem or data hole. Both local pullback counits
now refer to the already constructed `residueExchangeUpperStarCounit` instead of
repeating its defining `unfold`/`exact` conversion.

The bridge theorem `integralResidue_tensorGeometry_component` retains its original
signature byte for byte. Its complete Lean proof computes the tensor route with the
existing `integralResidue_tensorRoute_model`, computes the scalar route using the two
counit identities, and cancels only `residueExchangeTensorModelTarget`, whose
invertibility is proved from `hFP`. The retained `hP` binder is unused by this route;
the existing declaration-scoped unused-variable option preserves that binder.

The bridge's new imports are proof-only. Both original public imports remain.
The two counit modules are new relative to the current shared source. No other
module is adapted, and no target statement or target definition is changed.
The definition repair and its complete consumer list are recorded in
`coord/changes/integral-residue-ordinary-regular-pull-iso.md`.

## Proved and sorry left

This is a repaired decomposition, not an axiom-free proof or a net hole reduction.

Closed one of one assigned holes:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorGeometry_component`
(node `new-integral-residue-scalar-geometry-component`). The bridge has zero holes.

Added relative to the current shared source, and retained from the returned split:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_scalarCounit_model`,
  node `new-integral-residue-scalar-counit-model`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorPullCounit_model`,
  node `new-integral-residue-tensor-pull-counit-model`.

Each is a named public theorem with proof exactly `:= by sorry`, its source,
and the complete natural-language argument in its docstring. There are exactly two
holes in the delivered Lean files: one upper hole closed and two lower holes added,
net minus one relative to the current-source item. No additional split was created
in this repair session. The ledger determines the import-closure-wide counts.

The existing `integralResidue_tensorRoute_model` is an unchanged upstream open
dependency and is not counted as newly proved or newly added. There is no sorry in
a definition, no private sorry, and no arbitrary witness chosen from unproved existence.

Final validation through the required compiler wrapper: `lcompile.py --all` compiled all three delivered modules
in import order with no errors or warnings: scalar-counit 7.9 s, tensor-pull-counit
6.6 s, and bridge 16.5 s. The delivery dry run is the remaining check.

## No longer needed

Removed direct imports from the current-source bridge:
`Sheaf.Paper.IntegralResidueOrdinaryMonoidal`,
`Sheaf.Paper.IntegralResiduePullSquare`, and
`Sheaf.Paper.IntegralResidueTensorPresentation`.
Their old direct proof-dependency edges are replaced by the explicit counit identities.
The derived-monoidal and tensor-pull-presentation edges stay; tensor-model,
tensor-route-model and the two counit nodes are the dependencies of the actual proof.
The new scalar-counit module also drops its redundant direct import of
`Sheaf.Paper.IntegralResidueDerivedMonoidal`; its tensor-model import already exports
that API. The new tensor-pull-counit module drops redundant direct imports of
`Sheaf.Paper.IntegralResidueDerivedMonoidal` and
`Sheaf.Paper.IntegralResidueTensorModel`; the scalar-counit import exports them.
The removed direct imports remain transitive dependencies, so no whole module is
claimed pruned from the targets' import closure. No unit realization or maintainer
`tool_uses` approval is removed.

The previously rejected equivalent-restatement module/node
`Sheaf.Paper.IntegralResidueScalarGeometryModelComp` /
`new-integral-residue-scalar-geometry-model-comp` is absent from the current source
and this delivery. It is not resurrected. Scratch proof experiments are not delivered.

## Where the brief, the DAG or earlier work was wrong

The retained delivery did not compile against the synchronized upstream source.
The local inline coefficient construction exposed large concrete monoidal instances
inside the two dependent counit statements. Naming the same construction at generic
condensed coefficients repairs that elaboration problem without weakening a statement.
This is a source change, not an unchanged re-push or a rebase alone.

The earlier equivalent postcomposed restatement was not a valid reduction: cancellation
made it equivalent to the assigned statement. The retained two-part route is different:
one identity concerns only the X tensor presentation and its defining counit, while
the other concerns the scalar mate and ordinary balanced-tensor comparison. Neither
contains the entire original square.

The scalar-route theorem already imports this bridge; using it here would introduce
a cycle. The independent tensor-route formula is used instead. The more specialized
`residueExchangePull_flatModel` requires a cochain representative with a flat colimit
presentation and does not supply the ordinary balanced tensor coefficient calculation.
No unit-level route is bypassed.

The tensor-pullback calculation in Lemma 6.5.9(5) is on printed page 51; its lemma
starts on page 50. New docstrings identify both the precise location and the additional
formal counit-normalization argument. Existing source fields are preserved.

## New nodes

`new-integral-residue-scalar-counit-model`, in
`Sheaf.Paper.IntegralResidueScalarCounitModel`, isolates the scalar mate followed by
the tensor-presentation counit and the ordinary coefficient identification. It has
no tensor-model target or derived oplax tensor comparison. What remains is the
scalar mate unit/counit factorization, followed by the ordinary balanced-tensor
coequalizer calculation explained in its docstring. A scratch implementation of the
mate factorization elaborated all five compatibility steps but did not finish kernel
checking within the compile limit. The balanced-tensor compatibility still needs a
Lean proof; no extra hole for either step is introduced. The ordinary coefficient data
are constructed by `residueOrdinaryRestrictedRegularPullIso` in the same module.

`new-integral-residue-tensor-pull-counit-model`, in
`Sheaf.Paper.IntegralResidueTensorPullCounitModel`, isolates normalization of the
X tensor-pull presentation against its target model. It has no scalar pull mate.
Its proof combines the degree-zero coefficient counit identity with the defining
left-derived presentation counit identity and braiding/lax-tensor naturality.
It never inverts an arbitrary representative's counit. This obligation remains
open: the generic coefficient-counit calculation, tensor-presentation counit
calculation, and naturality calculation were written and compiled in scratch
experiments, but their full specialization to the fixed sheaf-module interfaces did
not finish within the compile limit. The remaining proof must connect those fixed
interfaces without repeatedly unfolding their large module instances. Unused scratch
helpers are not delivered.

Both statements apply to arbitrary homotopy representatives, including zero, without
coefficient flatness. For identity pullback they specialize to the same fixed
unit/counit comparisons; empty sites require no extra hypothesis. Their definitions
use explicit composites, not arbitrary witnesses. The nodes carry their source,
full natural-language proofs, actual searches, blueprint provenance and Lean signatures.

Change record: `coord/changes/integral-residue-ordinary-regular-pull-iso.md` (open).

## Second reading by A2

1. **Signatures and accidental changes.** Compared the delivered bridge with the
   repository version byte for byte at the theorem declaration. Its statement and
   all binders are unchanged; only proof-only imports, the unused-binder linter
   option, and the proof body changed. The two counit modules are new delivery
   modules, and their statements match their new nodes. The generic coefficient
   isomorphism is the construction recorded in the change record and introduces no
   hypothesis or altered target definition.

2. **Compilation and proof status.** Ran `lcompile.py --all` on the three modules;
   all compiled with no errors or warnings. The bridge has no `sorry`; the only
   delivered holes are the two named, documented split theorems
   `integralResidue_scalarCounit_model` and
   `integralResidue_tensorPullCounit_model`. There is no `sorry` in a definition,
   no axiom/unsafe/opaque/extern declaration, and the bridge proof uses only the
   existing tensor-route theorem plus the two explicitly named counit identities.

3. **Statements and split nodes.** Read each new theorem against its node and
   checked zero and identity pullback specializations conceptually. The scalar
   counit isolates the scalar mate and ordinary balanced-tensor comparison; the
   tensor-pull counit isolates the X tensor-presentation normalization. Neither
   restates the bridge, adds flatness, or uses an arbitrary witness. Searches in
   Mathlib and `lean/` found only generic mate/counit/tensor results, not these
   fixed residue comparisons. The new generic coefficient isomorphism is an
   explicit composite of existing isomorphisms.

4. **Route and pruning.** The bridge follows the retained route: cancel the
   invertible tensor-model target, apply `integralResidue_tensorRoute_model`, and
   normalize the scalar route using the two counit identities. The unit-level
   tensor-presentation and derived-monoidal route remains represented. Removed
   direct imports are proof-only redundancies now supplied transitively; the
   removed dependencies and the open change record are listed above.

5. **DAG agreement.** Checked that every delivered theorem name, statement,
   `proof_deps`, source, and `proof_origin` agrees with its node. The two new
   split nodes carry complete proof sketches, searches, Lean signatures, and the
   existing chapter/unit route; the bridge node's proof dependencies match the
   declarations used in its proof.

**Changes made during second reading.** No mathematical statement or proof was
   changed. I verified the synchronized three-module version, retained the named
   generic coefficient construction and counit interfaces, and added this review.
