## What changed

The statement of `AlgebraicGeometry.ProEtale.reductionExceptional_chartEquation`
is unchanged. Its proof now constructs the ordinary input-origin isomorphism by
full faithfulness of site comparison on bounded-below complexes. The finite-Tor
scalar preservation lemma provides the required bound. The proof also constructs
the common-annihilator invertibility witness in the field and then in global sections.

At each input it lifts the actual intrinsic exceptional coefficient component through
the same fully faithful comparison. The new theorem
`reductionExceptional_counit_descent` derives its ordinary counit equation from the
existing `reductionSiteCoefficientPasting`, the realization counit fields, naturality,
and cancellation of the specified invertible intrinsic coefficient comparison.
The remaining generic categorical pasting is proved as the private `transfer_chart`:
it combines an ordinary chart identity with the scalar/site/pullback cube and the
actual realization isomorphisms to give exactly the required intrinsic chart identity.

Two geometric comparison identities remain as named statements in new modules.
Both have source proofs and new DAG nodes; neither is the original statement with
its hypotheses repackaged. The ordinary chart lemma has no intrinsic categories,
no realizations, and no choice of input origins. The cube has no exceptional functor,
no compactification, no counit transpose, and no smoothness or constructibility input.
The public theorem `reductionExceptional_counit_descent` and the origin-isomorphism
construction are proved components of the reduction.

`Sheaf.Paper.ReductionSiteCoefficientPasting` now imports
`ReductionExceptionalObjects` in place of `ReductionExceptional`, avoiding the
cycle back through the assigned item. Its declaration and proof are unchanged.
The matching DAG node now cites the extracted definition node instead of the
parent exceptional-isomorphism theorem in its statement and dependencies. Its
`statement_change` preserves the old metadata and audits every citer; the
mathematical and Lean assertions are unchanged. This also removes the stale DAG
cycle through the assigned chart node.
The change record is `coord/changes/F2-reduction-site-coefficient-import.md`.
All proof-only imports in the item are private imports. No source-library file,
definition, existing theorem signature, target, or global attribute changes.

## Proved and sorry left

One original hole is closed: `AlgebraicGeometry.ProEtale.reductionExceptional_chartEquation`
(`lem-sp-reduction-exceptional-chart`). Its module contains zero `sorry`.
This is a **decomposition**, not a completed mathematical proof: two lower holes
are added, so the raw count is one closed and two added.

The two new holes are:

- `AlgebraicGeometry.ProEtale.reductionSite_scalar_pullback`, node
  `lem-sp-reduction-site-scalar-pullback`, in `ReductionSiteScalarPullback.lean`.
- `AlgebraicGeometry.ProEtale.reductionExceptional_ordinary_chart`, node
  `lem-sp-reduction-ordinary-chart`, in `ReductionExceptionalOrdinaryChart.lean`.

The new `AlgebraicGeometry.ProEtale.reductionExceptional_counit_descent`, node
`lem-sp-reduction-counit-descent`, has no hole. Its categorical descent helper,
site full-faithfulness helper and the item's categorical chart-pasting helpers
are proved. The existing hole
`AlgebraicGeometry.ProEtale.reductionSiteCoefficientPasting`, node
`lem-sp-reduction-site-coefficient-pasting`, is retained verbatim in the adapted
import-only module. No other hole is added or changed.

Edge cases checked when stating the new lemmas: zero rings are allowed by unital
coefficient maps and all identities use their canonical functors; the cube has no
positive-dimensional or nonempty-scheme assumption; at dimension zero the ordered
affine right functor is the identity, leaving the sum/evaluation transpose. The
ordinary chart statement allows a general endpoint map a and makes no false claim
that it is invertible. It only asserts an equation for q when the actual counit
equation is supplied. Arbitrary finite scalar extension is never assumed exact.

Validation: the unchanged direct importer
`Sheaf.Paper.EtaleAffineProjectionCoefficientMate` compiled against the replacement
import in 36.4 seconds (exit 0). Its temporary unchanged source copy was removed.
The first delivery's two related-module compiles also passed (67 seconds total).
Its preflight found the stale DAG citation described below; no files were pushed.
The item compiled without warnings in 22.6 seconds and the new counit descent
module in 10.1 seconds.
The two new geometric statement modules compiled separately. Delivery reruns the
required checks. Large chosen comparison definitions are kept folded locally, and
proof-irrelevance congruences handle the realization record's site-instance proofs.
No compilation limit or transparency safety setting is relaxed.

## No longer needed

No module is withdrawn or claimed globally pruned. The item originally imported
only `ReductionExceptionalObjects`; that public import is retained. The redundant
proposed public import of `Sheaf.Paper.ExceptionalCoefficientMaps` in the new
ordinary-chart module was removed because the objects interface already exports it.
The sole changed existing import is the parent-to-objects correction described above.

The item's direct proof no longer needs these old planned dependencies:

- `det-pe-finite-tor-comparison-noetherian`,
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`: ordinary
  bounded-below Hom comparison already supplies the full faithfulness needed here.
- `lem-sp-open-exceptional-scalar-locality`,
  `Sheaf.Paper.OpenExceptionalScalarLocality`, and
  `lem-sp-open-proetale-counit-scalar`, `Sheaf.Paper.OpenProEtaleCounitScalar`:
  the argument descends the counit to ordinary coordinates before restricting to
  a chart; it needs no separate intrinsic exceptional-locality calculation.
- `det-sf-mate-open-restriction`, `Sheaf.Paper.MateOpenRestriction`: the ordinary
  chart lemma contains the ordinary open-adjunction step instead.

The chart-adjunction and chart-counit nodes
`lem-sp-chart-finite-ring-adjunction` and `lem-sp-chart-counit-scalar-transport`
remain dependencies of the ordinary-chart subargument, rather than direct imports
of the item. `lem-asd-finite-etale-twist-line` is used through the unchanged
canonical Tate constructions; no independent twist-line proof is needed in the
item. These observations do not remove their modules from other proof routes.
The existing coefficient/site square is reused instead of leaving a third new hole.

## Where the brief, the DAG or earlier work was wrong

The historical build-error file refers to an import failure that the current source
and published artifacts no longer reproduce; the baseline item compiled and had
one hole. The current queue row assigns a proof route, so this delivery supplies a
real reduction and does not treat the old successful compilation as completion.

Several planned comparison modules import the parent `ReductionExceptional`, which
itself imports the assigned chart item. Such imports cannot be added to this item's
proof without repairing the cycle. The needed mixed-endpoint coefficient/site square
was already stated in `ReductionSiteCoefficientPasting`; its parent import is repaired
here to the already extracted objects interface, retaining its statement and hole.
Preflight also exposed the corresponding stale DAG dependency: the square's node
still cited `det-sp-reduction-exceptional` for the constructed family. That node now
represents the theorem that uses this chart lemma. The square only needs the
verbatim extracted objects, so both its definition citation and its planned proof
reference are corrected to `def-sp-reduction-exceptional-realization-objects`.
A statement-change record documents this citation-only repair and the unchanged
uses of the square.
Its sole original direct importer independently imports the parent and therefore keeps
the old public context. No forced adaptation of another group's module is made.

The existing chart counit transport is stated in finite-ring restricted-adjunction
coordinates, with geometric coefficient and normalization data. The required
ordinary-chart corollary uses arbitrary specified ambient right adjoints and exactly
`reductionEtaleChartRightIso`. The remaining glue is isolated as that site-free
ordinary theorem. The fixed-site scalar/pullback cube similarly needs normalization
through the intrinsic realization and exact/derived ordinary pullback comparisons;
the new cube specifies this precise equality rather than assuming it by definitional
conversion. The updated nodes record these actual proof obligations. The blueprint
unit route, sum/evaluation followed by ordered affine trace, is retained.

## New nodes

`lem-sp-reduction-site-scalar-pullback` records the tensor-free normalized cube,
with no exceptional or smooth data. Its proof transports the existing fixed-module
etale/pro-etale cube through the specified realization mates and exact pullback.

`lem-sp-reduction-counit-descent` records the proved pointwise descent step. Its
proof uses the already stated mixed-endpoint coefficient/site square, the two
realization counit equations and faithful comparison into the bounded-below origin.
It makes no chart assertion.

`lem-sp-reduction-ordinary-chart` records the ordinary single-input chart transpose
calculation. Its inputs are ordinary right adjoints and the actual ordinary counit
equation; its proof uses open sum/evaluation and the ordered affine trace counit,
then right-adjoint uniqueness. It has no intrinsic realization or origin-selection
obligation. Its zero-dimensional and zero-ring cases are included explicitly.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ReductionSiteCoefficientPasting": "23801cb1e873c10e00255ec64f112a0b7f0ab034", "Sheaf.SecSmoothPurity.ReductionExceptionalChart": "7f239e467d5cefe749a6144ac7bee9cc90c22c9a", "Sheaf.SecSmoothPurity.ReductionExceptionalCounitDescent": "742d5eb5d2ab92440809c54112220e718df5960d", "Sheaf.SecSmoothPurity.ReductionExceptionalOrdinaryChart": "7fa1be6158fb8f0ce2cb7c8309cba3900c6c9655", "Sheaf.SecSmoothPurity.ReductionSiteScalarPullback": "8aef6cbf09e5d8fdaf46f60923a4a3dc43f84ba8"}, "results": {"Sheaf.Paper.EtaleAffineProjectionCoefficientMate": {"hash": "8fe18745e840210cd3cbc80d992cde3ee53b6cbc", "status": "OK"}, "Sheaf.SecSmoothPurity.ReductionExceptional": {"hash": "b80f17c7b85d282f0e2f46a9482d4abe6835b64c", "status": "OK"}}, "seconds": 115, "time": "2026-10-28T01:36:05+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
