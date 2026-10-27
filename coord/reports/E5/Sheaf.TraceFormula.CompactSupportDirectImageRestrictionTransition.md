## What changed

Filled `WeilConjectures.compactSupportDirectImageRestrictionTransition` without changing
its statement or any public definition, attribute, instance, or import. Added private
proof imports of `RightDerivedFunctor.ShortExactPullback` (cochain derived units and
naturality) and `MapDerivedCategoryMate` (normalized exact-functor composition).

The private proof first establishes the ordinary sectionwise square. It then derives
unit compatibility on all complexes from `CompactSupportDerivedSquareNormalization`,
using K-injective resolutions and cancellation. A categorical diagram chase applies
these equations and the localized transition formula on a K-injective source model;
naturality transports the result to every derived system. Evaluation and coefficient
restriction are never required to preserve K-injectivity. Local irreducibility
attributes prevent irrelevant expansion of constant coefficient sheaves, coefficient
ring maps and the standard derived-category instance during these private proofs;
no shared declaration or exported reduction behavior changes.

The ordinary proof uses explicit carrier equalities for coefficient restriction and
finite direct image when applying the heterogeneous section-identity hypothesis.
The four section conditions are checked as auxiliary proofs, avoiding repeated
normalization of concrete coefficient objects in one proof term.

Validation: the complete candidate passed `lcompile.py` in 43.5 seconds. Temporary
profiling options and the long-line warning were removed for delivery. The delivery
gate compiles the final version and performs the axiom/sorry probe. Edge cases are
preserved by the uniform proof: equal indices, zero transitions, zero objects, empty schemes, arbitrary
unbounded complexes, and nonflat coefficient quotients.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.compactSupportDirectImageRestrictionTransition`
(`lem-trf-direct-image-restriction-transition`). There are zero remaining holes in the
item and zero added holes or split-off statements. Every private helper is proved.
Dependencies may still have their own previously existing holes.

## No longer needed

The proof does not use the abstract existence theorem
`WeilConjectures.SemilinearSections.semilinearDerivedSections`, so the node no longer
lists `lem-coef-semilinear-derived-sections` as a proof dependency. Its abstract
operation fields need not be identified with the actual pro-etale operations.
The public diagram module still imports that library for its existing interface;
no module is asserted globally unused or withdrawn, and no existing import is removed.
The direct resolution-factorization/homotopy construction is replaced by naturality
of the already constructed derived units. No unit statement or unit route changes.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically sound. Its chain-homotopy lift can be
avoided: normalization implies compatibility with the cochain derived units, and
naturality of those units gives exactly the needed localized square. This uses
existing declarations rather than another decomposition.

The current `literature/blueprint/latest/blueprint/sec-trace-formula/` text titles
`sk-thm-trace-transport` “Euler-product form of the trace formula”, whereas its unit
JSON retains the older transport-to-nonfinite-stages text. This is outside the
assigned restriction-square proof; no unit record or target statement is changed.

Searches: LeanFinder returned bounded-below derived-functor comparison APIs, not this
unbounded varying-coefficient square; Loogle did not know the project declaration
`rightDerivedFunctorObjQIso`; Mathlib grep found no exact evaluation/transition result.
The source library supplied `rightDerivedFunctorUnitQ_naturality` and the exact
compositor factorization, which are used directly. Searches are recorded in
`searches.jsonl` by the required search tool.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
