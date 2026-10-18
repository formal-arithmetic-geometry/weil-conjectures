## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleCoefficientInverseImageMap_comp` with its
signature and docstring unchanged. Three proved private lemmas express the
constant-section unit equation, composition of the direct-image coefficient maps,
and compatibility of adjuncts with the canonical mate. A private abbreviation
names the existing sheaf pushforward composition isomorphism; it constructs no new
mathematical object. The final proof applies the composite adjunction Hom bijection,
its naturality and injectivity. This realizes all four steps of the existing plan.

Replaced the unused public import `SfIntrinsicRealizationTransport` by the precise
statement dependency `ProEtaleInverseImage`; removed unused `ProEtaleConstantRingMap`.
Retained `SupportComparisonPullbackCoherence`, which supplies the comparison in the
statement. Updated the proof fields of both DAG nodes attached to this declaration.
Change record: `coord/changes/proetale-constant-ring-composition-imports-E8.md`.

The final module compiles cleanly in 3.9 seconds. A sandbox probe prints exactly
`propext`, `Classical.choice`, and `Quot.sound` as its theorem's axioms. The sole
downstream module, `ProEtaleDerivedPullbackCoherence`, compiles unchanged against the
delivered module (3.0 seconds). The argument checks arbitrary scheme morphisms and
commutative coefficients without using the finite instance; empty schemes, the
zero ring and identity maps require no separate assumption or exceptional branch.
Sources read: proetale.tex section-morphism (09A5), sites.tex
example-constant-sheaf (0H7J), proposition-sheafification-adjoint (00WH),
lemma-composition-morphisms-sites (03CB), and categories.tex lemma-compose-counits
(0DV0). Mathlib searches via msearch.py used LeanFinder, Loogle and grep; the
useful generic APIs are `unit_conjugateEquiv_symm` and `Adjunction.comp_homEquiv`.
The existing module pullback proof was also read for its direct-image calculation.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.proEtaleCoefficientInverseImageMap_comp`, attached to
`lem-pur-proetale-constant-ring-composition` and the duplicate
`lem-trf-constant-coefficient-composition`.

No sorry remains in the item. No hole was added; no statement was split off.
All private helpers are proved. This is a proof, not a decomposition.

## No longer needed

Removed imports `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`. Their realization, module and
derived operations, finiteCoefficientInverseImageMap_isIso and the related
constant-coefficient comparison theorems are unnecessary for this proof.

Removed `prop-weil-pbc-proetale-constant-ring-map` from the trace-formula node's
proof dependencies and its obsolete tool_uses entry. Its isomorphism and empty-site
clauses are not needed: the canonical maps are already defined as adjuncts in
`def-weil-proetale-inverse-image`, and the direct calculation holds on empty objects.
It remains a statement dependency, since the informal statement describes the maps
as isomorphisms. No unit statement or unit proof step is bypassed. No module is
withdrawn; both attached nodes remain realized by the same proved declaration.

## Where the brief, the DAG or earlier work was wrong

The original public realization-transport import was much broader than the
constant-ring statement requires. The trace-formula proof also unnecessarily used
the coefficient-isomorphism theorem to identify maps already fixed by their
definition. The existing duplicate DAG attachments describe exactly the same Lean
theorem; both proof records now follow the single checked proof. No mathematical
statement, target signature, definition or source claim was changed.

The first compilation attempts encountered a busy compile service; retrying
succeeded. No tool was patched or bypassed.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
