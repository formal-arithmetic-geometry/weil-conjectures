## What changed

Completed the proof of CategoryTheory.nonempty_yonedaDerivedExtComparison without
changing its signature, the comparison structure, or any target statement.
The quotient map comes from a concrete signed recursive Ext class formed using
actual cokernels. Naturality gives quotient descent, classification gives a
bijection, and transport gives the abelian group laws. Naturality for the product
projections, diagonal pullback, and addition pushout proves the Baer-sum formula.
The specified geometric construction exists by actual products, pullbacks and
pushouts, including the degree-one overlap case. Mathlib supplies injective
vanishing with no enough-injectives assumption.

Retained and finished the earlier sandbox work. Repaired classification's
explicit composition degree, redundant dsimp calls, and the association and
identity simplifications in the common-head pushout equation. Classification
now uses effacement by a monomorphism and dimension shifting through Mathlib's
Ext exact sequences. Its proof and DAG explain this route explicitly. The comparison theorem
docstring now describes this completed route rather than the superseded plan.

Moved the existing YonedaExtension data unchanged into YonedaExtensionData so
proof imports remain acyclic. The item publicly imports the data module; every
old name, signature, universe and visibility is preserved. Change record:
coord/changes/yoneda-extension-data-extraction.md. No consumer adaptations are
needed. The four current direct importers retain the same public declarations.
All seven modules compile with lcompile.py --all; no warning or error remains.
The earlier session also compiled five consumers individually against the extracted
data and completed comparison. On resumption the current direct consumers are
ComplexExtDiskSphere, YonedaPullbackSplice, YonedaZeroSplice and
IntegralConstructibleCompactness; IndConstructibleExtensions now uses a separate
degree-one classification module. No consumer source changes are delivered.

The 2026-10-19 continuation checked the extracted data and comparison structure
against the current repository: their declarations and bodies are byte-identical.
All seven Lean modules have zero sorry occurrences and meet the 100-character
line limit. The compilation successes above are retained results from earlier
sessions. Two fresh required dry runs stopped before compiling the first module
because the compile server returned no answer after 566 and 542 seconds; a
third dry run compiled the complete set and passed preflight (31d1cbf7b3).
No compiler diagnostic or source defect was returned.

## Proved and sorry left

Closed the original one hole:
CategoryTheory.nonempty_yonedaDerivedExtComparison
(node lem-coef-yoneda-derived-ext-comparison).
Holes closed: 1. Holes added: 0. Split-off unproved statements: 0.
There are no remaining sorry declarations in any of the seven delivered modules.

All introduced intermediate results are proved, including:
- CategoryTheory.YonedaExtension.derivedClass_naturality
  (lem-coef-yoneda-class-naturality);
- CategoryTheory.YonedaExtension.derivedClass_splice
  (lem-coef-yoneda-class-splice);
- CategoryTheory.YonedaExtension.derivedClass_classification
  (lem-coef-yoneda-class-classification);
- CategoryTheory.YonedaExtension.pushout_extension,
  CategoryTheory.YonedaExtension.pullback_extension, and
  CategoryTheory.YonedaExtension.baerSum_exists
  (lem-coef-yoneda-baer-existence);
- CategoryTheory.YonedaExtension.head_shortExact, tailSequence_exact,
  tailSequence_first_mono, tailSequence_last_epi, shortExact,
  extClass_eq_zero_iff, and derivedClass_zero_iff
  (def-coef-yoneda-recursive-class).

Every definition is a real construction. No arbitrary extension is chosen from
an unproved existence result. The classification and Baer-existence statements
that earlier sandbox reports listed as holes are now completely proved.

## No longer needed

Removed these original proof-only imports from the item:
Mathlib.Algebra.Homology.DerivedCategory.Basic,
Mathlib.Algebra.Homology.DerivedCategory.Fractions,
Mathlib.CategoryTheory.Localization.CalculusOfFractions,
Sheaf.CategoryTheory.PushoutShortExactSequence, and
WeilConjectures.CategoryTheory.PushoutShortExactSequence.
Classification retains the Mathlib Fractions import for left-factorization;
Baer existence imports the proved source-library pushout theorem directly.
The duplicate Sheaf pushout wrapper is not imported anywhere in this delivery.
Removed the unused CalculusOfFractions and Sheaf pushout imports from the new
classification module as well.

The original planned nodes lem-pc-right-fraction-representation and
lem-pc-right-fraction-common-refinement are not used by the completed route:
effacement and the Ext exact sequence replace explicit common-refinement
classification. No global pruning of these nodes is claimed if other items use
them. def-weil-abstract-derived-category and
lem-pc-quasi-isomorphisms-multiplicative-system remain below classification,
through Mathlib's left-factorization theorem. The pushout theorem remains below
Baer existence; the removed parent tool_uses approval is still requested as a
generic black-box tool for that new node. No approval has been added by C2.
The unit has empty realized.statement and realized.steps lists at this auxiliary
node, and its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original dependency declarations contain no direct classification theorem
for concrete finite extension sequences. Mathlib does supply enough to prove it
without an enough-injectives assumption: efface individual positive Ext classes
using a left fraction, then dimension-shift. Equality uses a common first
monomorphism obtained by pushout, a further effacement of the tail-class
difference, and induction on the degree. This replaces the planned explicit
common-right-roof construction. No mathematical statement is weakened.
Corrected the recursive-class node signature to use the declaration parser's
`def` signature, excluding the `noncomputable` modifier; the Lean code is unchanged.

The inherited report incorrectly described two still-open obligations; both now
have complete proofs. The degree-one and higher-degree constructions handle
arbitrary endpoint isomorphisms and object and morphism universes. In degree one
classification constructs an actual endpoint-fixed short-complex map, and the
split-zero criterion is proved by the contravariant Ext exact sequence.

## New nodes

- def-coef-yoneda-extension-data: the unchanged finite exact-sequence data moved
  into its own module to break proof-import cycles.
- def-coef-yoneda-recursive-class: actual cokernel heads and tails, their induced
  maps, and the signed recursive class, with the proved split-zero criterion.
- lem-coef-yoneda-class-naturality: proved by induction on the degree, using maps
  of actual heads and tails and Mathlib extClass_naturality.
- lem-coef-yoneda-class-splice: proved using the canonical map from the specified
  splice tail to the actual cokernel tail and associativity of Ext composition.
- lem-coef-yoneda-class-classification: proved by individual effacement,
  dimension shifting, common heads and tail zigzags, as detailed in its node.
- lem-coef-yoneda-baer-existence: proved using actual products and endpoint
  pullback/pushout constructions, independently of the quotient comparison.

All six nodes inherit the item's chapter and unit. The searches recorded in the
existing sandbox found no duplicate concrete interfaces. Search evidence is in
searches.jsonl; the change record is named above. None of these nodes leaves an
unproved statement for another session.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
