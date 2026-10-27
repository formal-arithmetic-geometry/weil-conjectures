## What changed

Added the proved `CategoryTheory.brownHypothesesFor_iff` in the item module. For any
scheme and commutative condensed coefficient, it identifies Brown's bundle with
thickness, essential smallness, and compactness of every constructible finite-Tor
object for a chosen coproduct structure. Its forward proof uses a small equivalent
category and the unit isomorphism to transport compactness from the representatives.
Its reverse proof uses the existing structural theorem and the proved generic
generation argument. The existing six-case finite-field assembly now applies the
criterion. Existing public signatures, definitions, visibility and imports stay
unchanged.

Updated the parent proof plan and added the criterion's node. The source is the
formal assembly in paragraphs 1--2 of the current Brown-hypotheses blueprint proof.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.

`CategoryTheory.brownHypothesesFor_iff` is proved, node
`lem-sfb-brown-hypotheses-criterion`. Every existing helper remains proved.
The only remaining sorry is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`, with its original signature and disputed marker.
This is a proved formal reduction criterion and retained partial packet; it does not
claim a proof or a holed decomposition of the arbitrary-field assertion.

Current resumed-session validation, 2026-10-24:

The required initial `deliver3.py Q3 Sheaf.SixFunctorsBasics.BrownHypotheses`
invocation passed server preflight and printed
`DELIVERED Sheaf.SixFunctorsBasics.BrownHypotheses at 9c8df9275cc`.
Unlike the earlier attempts, the current delivery gate accepts this diagnostic
packet for independent review. This supersedes the retained historical claim
that the packet cannot be submitted. Submission does not close the disputed
original hole or constitute independent mathematical approval.

The prescribed `lcompile.py` returned the successful cached result for the item:
16.3 seconds, exit 0. Re-read the current finite-field compactness, structural and
smallness signatures, the standing setting and Brown unit. The setting still
explicitly imposes no further field hypothesis. A fresh prescribed leanfinder
query returned eight derived-category bounds/representative results, none
covering the arbitrary-field compactness assertion.

Retained scratch diagnostics are outside the delivered Lean tree.
`scratchpad/DerivedObstruction.lean` proves
`CategoryTheory.not_compact_in_fullSubcategory_of_positive_ext` and
`CategoryTheory.not_brownHypothesesFor_of_positive_ext`. With exact countable
products, nonzero maps from a constructible finite-Tor source to every positive
shift of one heart object obstruct the Brown bundle. The proof constructs the
coproduct/product witness and lifts the coproduct universal property into the
actual localizing full subcategory. Its earlier successful compile took 19.6
seconds; both axiom reports list only `propext`, `Classical.choice`, and
`Quot.sound`. Neither theorem uses the holed `brownHypotheses` declaration.
The field-cohomology witness itself is not formalized; no unconditional Lean
counterexample is claimed.

No signature, definition, quarantined parent, launcher script, budget or claim
was changed in this resumption. The earlier gate failures are historical, not
the outcome of this submission. Original holes closed: 0 of 1; holes added: 0;
split-off holes: 0; pruned modules: none.

## No longer needed

Removed the redundant structural-theorem application in the finite-field assembly:
the reverse criterion supplies those structures itself. No imports, modules or existing
DAG dependencies are removed. The criterion uses
the existing structural, generic generation and isomorphism-compactness proofs.
The private assembly remains the reverse-direction implementation. The finite-field
compactness and smallness declarations are still needed for the supported
specialization, and the four quarantined DAG parents still cite Brown hypotheses.
Their absence from the live Lean tree does not authorize withdrawing this module.

## Where the brief, the DAG or earlier work was wrong

The sole existing theorem is STATEMENT-DISPUTED. The current blueprint's standing
setting explicitly permits an arbitrary positive-characteristic field, whereas the
available compactness declarations require a geometric finite-field datum, a finite
or separably closed field, or an explicit Ext bound. No hypothesis of the item
provides that missing finiteness input. The admissibility predicate also contains a
separate all-continuous-map algebraic-closure coefficient absent from the six-case
finite-field compactness interface. The existing specialization therefore cannot
prove the original assertion, and this delivery does not weaken it or introduce a
new false compactness lemma. The criterion makes the unresolved compactness input
explicit while proving that the ambient and generation clauses add no obstruction.

Current-source checks on resumption:

- `literature/blueprint/latest/blueprint/sec-six-functors-basics/` followed by
  `sk-def-sfb-dc-setting/_section.md` explicitly says that no further hypothesis
  on the field is imposed. Therefore a finite-cohomological-dimension assumption
  cannot be silently recovered from the standing setting.
- `Sheaf.SixFunctors.BrownHypothesesSmall.det_brown_hypotheses_small` provides
  thickness and smallness on compact locally Noetherian schemes, but its six
  coefficient alternatives omit the separate all-continuous-map algebraic closure.
- `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` and its dependency
  `Sheaf.Paper.BrownHypothesesGeneration` take `FiniteFieldDatum` and the structure
  morphism to its algebraic closure `D.k`. They cannot be instantiated with an
  arbitrary input field or an arbitrary input scheme.
- The adopted source's `UpperShriekLocalizing` compact-generation theorems for
  rational, integral and algebraic-closure coefficients each require
  `Finite k ∨ IsSepClosed k`. Its finite-coefficient `CompactConstructible` theorem
  requires `HasFiniteCohomologicalDimension`. None follows merely by unpacking the
  input binders of `brownHypotheses`.
- All four recorded DAG parents remain in the current rework table and quarantine.
  The archived `LocalizingExceptionalAdjoint` actually applies `brownHypotheses`
  twice; `ExceptionalInverseImageExistence` applies it once. Their missing live
  files are not evidence that the disputed theorem can be withdrawn.

The Stacks Project compactness criterion, tag 0948, Lemma 21.52.5
(https://stacks.math.columbia.edu/tag/0948), supplies unbounded compactness under
both a cohomological bound and commutation of cohomology with sums. Its bounded-below
criterion, Lemma 21.52.3, is weaker and cannot supply the unbounded conclusion here.
This confirms the distinction in the available interfaces; it is not a formal
Lean counterexample to `brownHypotheses`. The independent source reference for exact
countable products is Bhatt--Scholze, *The pro-etale topology for schemes*, section 3.1
(https://people.mpim-bonn.mpg.de/scholze/proetale.pdf); the adopted library implements
this as `CondensedRing.countableAB4Star_mod`. No unproved assertion of arbitrary-field
compactness was added to make the retained theorem appear proved.

Further investigation in the resumed Q3 session: the adopted source already proves
`DerivedCategory.not_preservesColimitsOfShape_of_forall_hom_ne_zero` in
`WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`. Its proof uses
`CochainComplex.isLimitFanMkProjSingleFunctorObjShift` and
`DerivedCategory.isLimitFanMkQObj`: with exact countable products, the coproduct of
successive positive shifts of a heart object is also their product. An object with
nonzero maps to all those shifts cannot be compact. This is the precise obstruction,
not merely a missing Mathlib search result.

A concrete mathematical test datum is `p = 3`, `ell = 2`,
`k = algebraicClosure(F_3)(t_1,t_2,...)`, `X = Spec k`, and the constant coefficient
`F_2`. The identity structure morphism is separated and finite type. The constant
rank-one coefficient sheaf in degree zero is constructible of Tor amplitude `[0,0]`.
For every positive `n`, the Kummer cup symbol `(t_1)...(t_n)` gives a nonzero class
in `H^n(k,F_2)`: apply successive valuation residues in those variables, with the
remaining variables in the coefficient field, to obtain `1` in `H^0`. Its shifts
belong to the very localizing closure in the conclusion. Exact countable products
identify their coproduct with their product in the ambient pro-etale derived
category. This gives a map from the rank-one sheaf with infinitely many nonzero
projection components, whereas every map from a compact source into this coproduct has
only finitely many nonzero projection components. Thus the requested compactness fails. This paragraph is a
natural-language counterexample; no Lean formalization of the Kummer/residue
calculation is claimed. The generic structural obstruction was independently compiled with only
`propext`, `Classical.choice`, and `Quot.sound` in `scratchpad/Obstruction.lean`;
that scratch file is outside the delivery Lean tree. The scratch theorem
`CategoryTheory.not_brownHypothesesFor_of_coproduct_is_product` then applies this
obstruction directly to the Brown bundle, transporting its representative compactness
to any constructible finite-Tor source in the localizing closure. All three scratch
theorems compiled together in 7.4 seconds, exit 0, and `#print axioms` lists exactly
the same three permitted axioms for each. This is a conditional counterexample
criterion, not a formal construction of the proposed field-cohomology witness.
No false replacement statement or assumption of arbitrary-field compactness is added.

The current-source parent audit enumerated all four JSON parents from `stmt_deps`,
`proof_deps` and proof-step `uses`, and read the two archived proofs that actually
apply the theorem. Both retain arbitrary-field signatures. The current rework rows
preserve the four archived modules. Consequently neither zero live importers nor
these callers permits dropping or restricting this theorem as a proof-only repair.

Edge cases of the new criterion: it imposes neither a nonempty skeleton nor distinct
representatives. The empty scheme, zero coefficient ring, zero objects, and a small
model with repeated isomorphic objects are included. All compactness assertions use
the same explicit coproduct witness as their bundle, and generation uses the
canonical inherited shift. No arbitrary object data is chosen from an unproved
existence assertion.

## New nodes

`lem-sfb-brown-hypotheses-criterion` records the proved field-independent equivalence.
It is a formal lemma of its own in the blueprint assembly, not a replacement hole
for the original theorem. Its proof and exact Lean statement are recorded, with
three kinds of search. Its dependencies are compactness, the structural theorem
and the generic localizing-closure generation theorem; it has no sorry.

Change record: `coord/changes/Q3-brown-hypotheses-formal-criterion.md`.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
