## What changed

Proved `WeilConjectures.finite_stage_verdier_biduality` in
`Sheaf.Paper.FiniteStageVerdierBiduality`, with every existing public signature preserved. The
finite-stage pro-etale predicate packages its original conjunction through
`ProEtale.VerdierBidualityOn` while the coefficient category is abstract, avoiding the costly
native closed-structure conversion at finite coefficient specialization. Five proved private
helpers transport the actual pro-etale finite-Tor predicate across isomorphisms and extract
ambient preservation and exactness from a specified subcategory anti-equivalence and its inclusion
comparison. The additional public definition is attached to the existing definition node
`def-sf-finite-verdier-biduality-predicate`. The proof specializes
`finite_stage_etale_geometric_biduality` and `finite_duality_site_comparison`, and applies
`DerivedCategory.nativeInternalHom_contravariant_exact` for exactness. The original canonical
pro-etale pairing witness and its biduality-map assertion are used verbatim. A proved object
equality is rewritten before applying internal Hom, avoiding the expensive implicit conversion
that unfolds its derived right adjoint. The DAG proof now records precisely those dependencies. No
new modules or nodes.

## Proved and sorry left

Closed: `WeilConjectures.finite_stage_verdier_biduality` (node `thm-fix-general-biduality`), the
only original hole: 1 of 1. Added holes: none. Remaining holes in the delivered module: zero. The
five private helper proofs are complete. The proof depends on already stated results, including
the currently unproved `WeilConjectures.finite_duality_site_comparison`; this is an existing
separate item, not a hole added by this delivery. The native internal-Hom exactness theorem is
proved in the current shared source.

## No longer needed

Removed four unused private imports: `Sheaf.Paper.FiniteCoefficientFlatModel`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`, `Sheaf.Paper.ComparisonTorAmplitude`, and
`Sheaf.Paper.WeilVerdierPreservationStrata`. The old direct proof dependencies
`lem-sf-proetale-constructible-origin`, `lem-sf-comparison-tor-amplitude`,
`lem-weil-verdier-preservation-strata`, and `def-pur-derived-internal-hom` are unnecessary as
direct dependencies of this proof: the published site-comparison theorem already contains the
subcategory anti-equivalence and the canonical biduality conclusion. Their use inside that
comparison theorem is retained; no global withdrawal is claimed. Removed the obsolete direct
`tool_uses` approvals for `lem-sf-proetale-constructible-origin` and
`lem-sf-comparison-tor-amplitude`; the site-comparison approval remains. All original public
imports are preserved; the predicate wrapper needs no additional public import. No module is
claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan elaborates descent and biduality transport that are already clauses of
`FiniteDualityComparisonData`. Using those stated clauses avoids repeating that argument. The
remaining exactness clause follows from the existing native internal-Hom exactness theorem, rather
than a new geometric transport lemma. The private Tor transport explicitly handles the ordered
interval and all representative choices; no extra boundedness or nonzero-object assumption is
used. The current blueprint and the unit record were read; this keeps the same etale duality and
site-comparison route. The unit has no separately realized proof steps.
`lem-weil-native-internal-hom-contravariant-exact`, already in the same unit, is used as a generic
categorical tool (Stacks 08JC), with no geometric or biduality assumption. The historical rework
row is superseded by the current restored item source; this delivery preserves all of its public
declarations and attachments.

Generic private helpers extract the comparison consequences and specialize them to fixed scalar
coefficients for an arbitrary compactification before the final Nagata specialization. Diagnostic
profiling options were removed.

Change record: `coord/changes/K4-finite-verdier-native-hom-instance-path.md`. All textual
consumers and every transitive downstream module are accounted for there; no consumer adaptation
is required. The definition repair reopens statement review for the targets using it, with no
semantic or target-text change.

Source checks: the theorem signature and all original public imports are unchanged; the module has
zero `sorry` tokens and no lines exceeding 100 characters. The DAG proof-dependency list is
exactly the union of the uses in the new proof steps.

Validation: the full module compiled cleanly through `lcompile.py` in 12.7 seconds with the
generic predicate repair. Consumer validation uses unchanged sources in a separate scratch
sandbox, outside the delivery file set.

The unchanged `VerdierCoefficientRealization` compiled against the repaired item
in 3.5 seconds. `FiniteTorStability` passed against the published baseline in
41.6 seconds but timed out at 60 seconds against the repair. A diagnostic run
shows that every finite-stage assertion, including both uses of the changed
predicate, elaborates and kernel-checks; its expensive declarations are the
independent integral comparison at original line 616, integral reduction at
line 738, and common-stage rational conclusion. Those do not use the changed
predicate. No consumer source is adapted; the timeout remains a validation limit,
not evidence of a changed statement or failed finite-stage interface.

A standalone `rfl` equality check of the direct ModuleCat braiding and the
symmetric-structure projection compiled cleanly in 4.5 seconds. This checks the
coefficient instance-path equality used by the performance repair.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
