## What changed

Replaced the hole in `WeilConjectures.zl_curve_restriction_filtration_spectrum` by
an assembly of two independent geometric statements, a proved classical filtration
lemma on geometric fibres, and the existing `zl_classical_weil_filtration_heart_transport`. The supplied filtration's terms,
quotients, inclusion maps, quotient maps and top isomorphism are retained. An explicit
isomorphism of short complexes transfers exactness across the realization comparison;
`IsZero.of_iso` transfers the initial zero term. The top comparison is the prescribed
inverse realization component followed by the restricted given top isomorphism.

Moved the twelve existing data declarations, including the assertion predicate,
to `Sheaf.Paper.CurveRestrictionFiltrationData` to avoid import cycles. Eleven bodies
are verbatim. In the finite-model normalization field a named, explicitly constructed
isomorphism replaces its identical large eqToIso expression, reducing repeated kernel
work. All existing mathematical types are
definitionally unchanged. The assigned
module publicly reexports the data. Registered their ownership with a definition node.
Change record: `coord/changes/B7-curve-restriction-data-extraction.md`.

Validation: `lcompile.py --all` compiled all five packet modules in import order,
with no warnings or errors. The theorem signature and extracted assertion definition
were checked against the original source and remain verbatim. Development profiler
and heartbeat options were removed before this final compile.

## Proved and sorry left

Closed the original hole in `WeilConjectures.zl_curve_restriction_filtration_spectrum`
by decomposition. The original module has zero remaining holes. This is a reduction,
not a complete proof of the geometric inputs. Two holes are added:

- `WeilConjectures.zl_curve_classical_pullback_exists`
  (`lem-zl-curve-classical-pullback-exists`).
- `WeilConjectures.zl_curve_restriction_local_powers`
  (`lem-zl-curve-restriction-local-powers`).

`WeilConjectures.zl_curve_classical_filtration_pullback` is fully proved from the
supplied natural isomorphisms of geometric fibre functors. It returns the zero and
exactness proof fields; the parent constructs the image diagram directly. Its private helper
`curve_fibre_exact_of_iso` transports injectivity, exactness and surjectivity through
three linear isomorphisms. This classical lemma works for any morphism with the
supplied fibre comparisons, so its unused closed-immersion section instance is omitted.
The private categorical helpers for mapped and composite isomorphism squares,
top normalization, `curve_zero_reindex`, and `curve_shortExact_of_iso` are also fully proved. The classical
term equalities are transported by explicit mapped isomorphisms, avoiding expansion
of the large realization functors. The initial zero indices are transported explicitly
before realization, so different implicit `NeZero` proofs on literal finite zeros do
not cause the kernel to unfold those functors. There are
no holes in definitions or in the extracted data module. This is a decomposition:
one upper hole closed and two lower holes added, net -1 among the changed declarations.
The delivery ledger determines the import-closure totals against its pinned baselines.

## No longer needed

Removed the assigned module's direct private imports of
`Sheaf.Paper.ZlImmersionWeilLocalBehavior`,
`Sheaf.Paper.LisseCompletedSystemComparison`,
`Sheaf.Paper.LisseRationalRealization` and
`Sheaf.LinearAlgebra.PowerSpectrumConjugation`. Their mathematical inputs remain
needed in the normalized geometric construction and local-operator subarguments; no module is claimed pruned or withdrawn.
The eight public imports remain available through the public data-module reexport.
The separate direct obligations
`lem-zl-classical-finite-weil-diagram-realization` and
`lem-zl-classical-local-frobenius-iterate-comparison` are not invoked by this assembly:
the existing filtration heart transport already supplies the finite filtration stage
and all-period comparisons, while the new local lemma concerns constructible operators.
Their modules may remain needed by the transport theorem or other parents; none is
withdrawn. The three generic permanence nodes
`lem-pod-separated-finite-type-base-change`,
`lem-weil-pbc-closed-immersion-integral-separated-uc` and
`lem-weil-pbc-finite-over-separated-finite-type` need no separate theorem application;
existing base-change, closed-immersion and composition instances discharge these facts.
The constant-extension, immersion, completed-system, rational-realization and power-spectrum
nodes remain inputs of the geometric subarguments. The reality definition remains part
of the assertion data. The classical filtration heart-transport unit step is retained
on both schemes.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original plan states ordinary lisse inverse-image and
normalized composite-stalk arguments in prose; the declared general comparison and
constant-extension results do not themselves expose these curve-specific conclusions.
The new statements isolate these exact arguments, rather than duplicating the
full filtration-spectrum assertion. The classical step makes no heart or local-operator
assertion; the existence step makes no filtration or spectrum assertion; the local step
requires no filtration or lissity and can be applied to the independently given G.

Read blueprint latest, real-mixed-by-curves, paragraphs 1--2; Bhatt--Scholze pp.59--62
(Propositions 6.8.4 and 6.8.14, Remark 6.8.15); Deligne Weil II pp.151--152
((1.1.8)--(1.1.10)). Checked r=0 (only the zero term, no quotient indices), empty curve
(vacuous local conditions), zero rank (local polynomial one), disconnected schemes,
identity restriction, and coincident powers of eigenvalues. No semisimplicity is used.
The power is the composite map's residue degree, never the total constant degree m.

## New nodes

`def-zl-curve-restriction-filtration-data` registers the existing normalized curve,
finite-stage stalk and assertion data after their extraction, together with the explicit
finite-inclusion isomorphism that packages the old normalization comparison. It adds no hole.

`lem-zl-curve-classical-pullback-exists` isolates ordinary inverse image, compatibility
with the supplied normalized realizations, common-stage lissity and natural geometric
fibre comparisons (old steps 4--5).

`lem-zl-curve-classical-filtration-pullback` proves preservation of the classical
geometric fibre zero and exactness conditions for the prescribed diagram (old steps 3--4).

`lem-zl-curve-restriction-local-powers` isolates the normalized finite model, closed-point
residue-degree operator formula, spectrum multiplicities and reality (old steps 5--8).

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
