## What changed

The original declaration `Algebra.popescu_special_chart_polynomial` keeps its signature
byte for byte. Its proof constructs an algebra equivalence from the explicitly defined
`Algebra.popescu_special_chart_map`, its proved surjectivity and its remaining injectivity.
The map sends coefficients by the localization lift of `cmod` and sends each free variable
to its explicit auxiliary quotient class. Its coefficient-unit proof is the named, proved
`Algebra.popescu_special_chart_coefficient_isUnit`; no object is selected from an open
existence theorem.

Added modules `Sheaf.RingTheory.PopescuSpecialChartMap`,
`Sheaf.RingTheory.PopescuSpecialChartInjective`, and
`Sheaf.RingTheory.PopescuSpecialChartSurjective`. The latter proves surjectivity without
any Prepared hypothesis, using the k-th defining equations, polynomial induction,
surjectivity of the quotient maps, and localization fractions. Its private
`polynomial_value` helper is now generalized in place: it takes an arbitrary target
R-algebra B, an arbitrary map c from Cbar to B, and an arbitrary algebra map q from
the presentation polynomial ring to B. Equality on original variables implies
polynomial compatibility. It no longer fixes B to the unlocalized quotient or q to
its canonical quotient map. Surjectivity applies this generalization directly with
B equal to the localized quotient T and q equal to F. The existing private helper in
`Sheaf.RingTheory.PopescuLiftChartFlat` is not accessible by its source name even with
`import all`; no import of that module remains. This uses the return's explicit
alternative to generalize in place, rather than reproducing its quotient-specific
statement.

The item's new imports are proof-only imports of the injectivity and surjectivity modules.
Its original public import of `PopescuLiftPresentation` stays. Each new module publicly
imports only the module needed by its signatures and definitions. All files compile
without warnings through lcompile.py. No definition or existing statement was changed.

## Proved and sorry left

Holes closed: the original body of `Algebra.popescu_special_chart_polynomial` no longer
contains a hole. Holes added: `Algebra.popescu_special_chart_map_injective`, node
`lem-weil-pbc-popescu-special-chart-map-injective`, is the only named theorem left with
`:= by sorry` in the delivery. Its docstring gives the complete substitution,
conormal coefficient comparison, quotient descent, and left-inverse argument.

Fully proved new declarations: `Algebra.popescu_special_chart_coefficient_isUnit` and
`Algebra.popescu_special_chart_map_surjective`. The canonical map is an actual definition
with no hole or data chosen from an unproved existence theorem. The generalized private polynomial
compatibility helper is also proved for arbitrary target algebras and maps.

Accounting: one upper hole closed, one narrower hole added; this is a decomposition,
not a sorry-free proof of the original item. The net hole count is zero. In particular,
`#print axioms` shows only `propext`, `Classical.choice`, and `Quot.sound` for the
coefficient-unit theorem, map and surjectivity theorem. The injectivity theorem and
original item additionally use `sorryAx`, precisely through the one remaining hole.

The first worker's `Algebra.popescu_special_chart_polynomial_core` and its proposed
module/node are removed from this delivery: they encoded exactly the entire original
algebra-equivalence assertion as a coefficient-compatible ring equivalence.

## No longer needed

No existing library module is pruned and no original import is removed. The first worker's
proposed `Sheaf.RingTheory.PopescuSpecialChartPolynomialCore` import, module and
`lem-weil-pbc-popescu-special-chart-polynomial-core` node are removed before delivery.

Every old direct proof dependency was considered:
`lem-weil-pbc-popescu-lift-preparation` still supplies the data and conormal hypotheses
used by the injectivity argument, and `def-weil-pbc-module-localization-away` still
supplies localization notions. Their old direct proof edges in this node are replaced
by the canonical-map, injectivity and proved-surjectivity nodes; both old dependencies
remain needed transitively and are not pruning candidates. The unit `sk-thm-p1` and all
of its realized statement and step nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The landing return identified the duplicate quotient-specific `Algebra.polynomial_value`
in the new surjectivity module. That declaration is replaced by the arbitrary-target
and arbitrary-polynomial-map generalization described above. Its application specializes
directly to the localized quotient, so the intermediate unlocalized quotient equality
is unnecessary. Both the generalized lemma and the application compile without warnings.
No existing module was adapted and no existing signature or visibility changed.

The first worker's core theorem has the same hypotheses as the original and asserts a
ring equivalence commuting with all C0 coefficients. This is exactly an algebra
equivalence, so applying `AlgEquiv.ofRingEquiv` was a restatement, not a strictly smaller
lemma or genuine decomposition. Its docstring omitted the promised complete proof, its
node stored a placeholder rather than the verbatim Lean signature, and the item's DAG
proof was not updated to follow that application. These faults are repaired by removing
the core and writing the explicit map and genuine surjectivity proof. The first version
also emitted a heartbeat-option comment warning and a letI warning; neither remains.

The existing zero-base chart theorem was examined, but it only asserts existence of an
isomorphism over the scalar-extension base. It does not specify compatibility with the
C0 coefficient map required here, so it cannot supply this algebra equivalence without
an additional argument. Searches by evaluation, injectivity, elimination and quotient
base change found general Mathlib ingredients, which are used, but no existing
prepared-chart injectivity result. The source calculation was read online in Stacks
Project Tag 07CP, especially its polynomial chart and comparison coefficients.

## New nodes

`def-weil-pbc-popescu-special-chart-map` records the real canonical map in
`Sheaf.RingTheory.PopescuSpecialChartMap`. Coefficients are lifted through localization;
auxiliary classes are explicit quotient classes. The map is defined even without Prepared.

`lem-weil-pbc-popescu-special-chart-map-injective` records the sole remaining proof hole
in `Sheaf.RingTheory.PopescuSpecialChartInjective`. It asserts only injectivity of the
specified map. Its proof constructs a left inverse and uses the prepared conormal basis
to ensure the other charts impose no extra relations.

`lem-weil-pbc-popescu-special-chart-map-surjective` records the proved, strictly weaker
hypothesis result in `Sheaf.RingTheory.PopescuSpecialChartSurjective`. It needs only the
coefficient/generator compatibilities and the actual defining equations, not Prepared.

All new nodes contain verbatim Lean signatures, source, complete proof steps, proof
origins and three kinds of actual recorded search. The upper node's proof and dependency
edges now agree with Lean. No change record is required because existing signatures,
definitions and public imports are unchanged.


## Second reading by G3

1. I compared the delivered item module with the repository version. The original theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. The three new module declarations are new nodes and do not alter existing declarations.

2. I compiled all four delivered modules with `lcompile.py --all`. There are no errors or warnings. The only remaining `sorry` is the named theorem `Algebra.popescu_special_chart_map_injective`; no definition contains `sorry`, and no forbidden `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` appears. The proved declarations use only the permitted foundational axioms; the injectivity theorem and the item transitively use `sorryAx` through that explicitly split theorem.

3. I checked the degenerate cases in the substitution argument: if a_k is nilpotent (including zero), its localization and the target localization are zero rings; if E_k is empty, the k-th equations kill all auxiliary variables after localization; and if there is no k, the assertion has no instance. No nontriviality assumption is needed. For arbitrary compatible c and cmod, surjectivity of epsilon and agreement on constants and original variables determine their coefficient action, so the proposed left inverse is compatible with them. The coefficient comparison follows the calculation in Stacks Tag 07CP.

The split-off injectivity statement is strictly weaker than the item (it proves only injectivity of the canonical map), is required by the item proof, and has a matching node with a complete proof plan and source. The coefficient-unit and surjectivity statements are true, directly used, and have explicit constructions and matching nodes.

4. The generalized private polynomial helper is proved for arbitrary target algebras and maps, avoiding duplication of an existing quotient-specific helper. Imports are minimal for the declarations and proof use, and the old core restatement was removed. No existing library module can replace these prepared-chart statements based on the searches recorded in the report.

5. I checked every new node against its Lean declaration (whitespace-normalized signatures agree, with the definition recorded from the `def` keyword), its source and creation fields, and the union of proof-step dependency edges. The map node covers the coefficient-unit calculation; the surjectivity node describes precisely the polynomial-extensionality, quotient and localization argument now compiled; the injectivity node describes the documented remaining proof. The upper node applies exactly its three new dependencies. The unit route is preserved: the item combines the canonical map, its injectivity, and its surjectivity via `AlgEquiv.ofBijective`; the unit `sk-thm-p1` and its realized nodes remain unchanged.

I added the required second-reading section to the launcher input `report.md` (the generated `coord/reports` copy alone is not the input), and recorded the independent searches, edge-case review, signature checks and axiom probe. The fresh LeanFinder query on localized conormal elimination found general localization/presentation ingredients but no substitute for prepared-chart injectivity; an `rg` search on quotient injectivity, chart polynomials and polynomial compatibility found the known zero-base theorem and private helper discussed above. The zero-base theorem supplies an unspecified algebra equivalence, so it cannot directly prove injectivity of this specified coefficient-compatible map. No split-off theorem can be closed in a few minutes from those declarations. After the first delivery preflight, no Lean source or DAG content was changed during review.
