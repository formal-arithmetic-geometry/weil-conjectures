## What changed

Added a kernel-checkable refutation of the assigned statement inside
`Sheaf.SmoothPurity.TraceExistence`. All new declarations are proved private lemmas;
the public statement and its existing proof hole are preserved byte for byte.
The existing informal automorphism warning is now certified for the actual bounded
constructible condensed coefficient category, not merely for an abstract category.

`smoothTrace_char_three_claim_false` specializes the exact assertion to ell = 2,
k = the algebraic closure of F_3, f = the identity of Spec k, and relative dimension
zero. Its proof supplies the required smoothness witness and the isomorphism from
the actual bounded constructible unit to the shifted zeroth Tate twist. It proves
that the quantified representing-uniqueness assertion is false, without invoking
`existsUnique_smoothTrace`, any purity assertion, or any new unproved statement.

The argument first shows that a unique representing trace forces every source
object automorphism to be the identity. The proved geometric-field coefficient
isomorphism identifies the sections of the
actual coefficient object at the final test object with ULift Qbar_ell. A hypothetical
equality of negation and identity gives -1 = 1 there. The faithful derived single
functor and the full bounded constructible inclusion carry this obstruction to the
exact source object of the assigned theorem.

Also proved `normalized_trace_unique`, the correct final categorical step. A
specified natural family E_K : Hom(K,M) equiv Hom(FK,U) determines the trace
explicitly as E_M(id_M); naturality gives its formula and evaluation at id_M gives
uniqueness. The geometric construction must specify this family, including its
normalization, rather than assert only bijectivity.

Added only proof imports of derived full faithfulness, the algebraic closure
construction, and `Sheaf.Paper.CondensedQbarCoefficientConstruction`. Revised the
module/theorem documentation to identify the certified obstruction instead of
presenting the invalid uniqueness inference as a proof. No source-library file,
public signature, definition, attribute, or public import was changed.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added or split off: 0.

The sole remaining sorry is
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace`, node
`lem-route-smooth-trace-representing-unique`. Its current statement is false; the
new counterexample proves the negation of a valid specialization of that exact
statement, so there is no truthful reduction of its uniqueness clause to true
geometric lemmas.

The new private lemmas are fully proved: `no_unique_representing_trace`,
`neg_id_ne_of_faithful`, `neg_id_ne_of_iso`,
`point_unit_neg_id_ne`, `point_derived_unit_neg_id_ne`,
`point_bounded_unit_neg_id_ne`, `point_locallyOfFiniteType`, `point_quasiCompact`,
`point_isSeparated`, `point_no_unique_representing_trace`, `point_zero_twist_iso`,
`point_smooth_zero`, `smoothTrace_point_claim_false`,
`smoothTrace_char_three_claim_false`, and `normalized_trace_unique`.

The counterexample is proved uniformly for every functor from the actual bounded
constructible category to itself; instantiate it with the given lower-shriek functor
to refute the assigned specialization. The generic quantification avoids inheriting
the current lower-shriek construction's existing proof holes in the refutation's type.
The point-unit evaluation uses the fully proved `fieldCoefficientIso`, rather than
the source library's still-unproved point-module equivalence.

The counterexample and normalization lemma compile independently of the assigned
sorry. A separate audit file omitting the assigned declaration checks `#print axioms`
for `smoothTrace_char_three_claim_false`, `smoothTrace_point_claim_false`,
`point_no_unique_representing_trace`, and `normalized_trace_unique`; the only axioms
are `propext`, `Classical.choice`, and `Quot.sound` (the normalization lemma needs only
`Quot.sound`). No data was selected from an unproved existence assertion.

## No longer needed

No public import, DAG dependency, node, or module was pruned. The previous private
`postcomp_bijective_of_iso` helper is superseded by the proved source-automorphism
obstruction, which establishes the actual contradiction needed here. The finite
purity, integral-tower, exceptional-reconstruction, and Tate-realization dependencies
remain relevant to a future correctly normalized trace construction.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: unnormalized Hom bijectivity cannot determine a unique trace.

The final sentence of the node's third proof step confuses uniqueness of a map
inducing a specified adjunction Hom equivalence with uniqueness of a map whose
induced functions are merely bijective. If t represents Hom and e is a source
automorphism, F(e) followed by t also represents Hom. Uniqueness would equate these
two traces, and injectivity at the source object then forces e = id. The concrete
negation automorphism above contradicts this, even though the proposed morphism is
smooth of the stated dimension and all coefficient hypotheses hold. This includes
ell = 2: Qbar_2 has characteristic zero.

The assigned source reference
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-def-sp-trace/sk-def-sp-trace.proof.md`
is absent in the current blueprint. The current unit's `_section.md`,
`def-pur-smooth-trace.md`, and `sk-def-sp-trace-properties.proof.md` specify the
normalized trace as the prescribed purity map followed by the actual counit; they
do not claim uniqueness from unqualified Hom bijectivity.

A correct replacement must retain the finite diagonal/Kummer orientation through
reconstruction and scalar realization and specify its actual Hom equivalences (or
an equivalent normalization equation). `normalized_trace_unique` proves the formal
last step once these data are supplied. Weakening the theorem to mere existence
would not repair `smoothTrace`: choosing an arbitrary existence witness is expressly
forbidden by the project contract.

Consumer audit: only `WeilConjectures.SmoothPurity.Defs` uses the declaration. Its
`smoothTrace` definition takes the supposed unique witness, and its proof of
`smoothPurityIso_zero_of_isOpenImmersion` uses the false uniqueness to equate that
witness to an independently constructed open counit. Any normalized replacement
must adapt that proof to establish the actual normalization. There are 126
transitive importers of the item, so this delivery preserves its interface and
records the obstruction for a coordinated mathematical repair. The required change
to the witness selected
by the source-library `smoothTrace` definition cannot be made under the current
source-library boundary, and no exception for that definition is listed in
`coord/upstream-statement-exceptions.tsv`. This is a certified
counterexample delivery, not a claim that the disputed hole has been proved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SmoothPurity.TraceExistence": "8c9d3434147e91fac632afb2100ef4173f92e6e4"}, "results": {"WeilConjectures.SmoothPurity.Defs": {"hash": "bf5789f90d911ab0a7e6484aa9e6fa239ca04954", "status": "SLOW"}}, "seconds": 131, "time": "2026-10-28T10:29:04+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
