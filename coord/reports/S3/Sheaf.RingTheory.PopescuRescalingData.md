## What changed

Reduced `Algebra.exists_popescu_rescaling_data`, without changing its signature, to two
strictly separate constructions. `PopescuCoefficientRescaling` produces the rescaled
parameters and their Artinian coefficient lifts, but no ideal H or quotient equivalence.
`PolynomialParameterQuotientChart` is a generic construction of H and the polynomial
quotient equivalence from an explicit P[t] chart; it knows nothing about A, singular
ideals, rescaling, kernel equalities or coefficient enlargement.

The original module combines them with a complete Lean proof. It derives the S-generator
formula by multiplicativity and constructs u₀ from the coefficient quotient. Polynomial
ring-hom extensionality, checked on coefficients and variables, proves the evaluation
identity for every element of R. The DAG's proof route now records these two steps and
this assembly. The source read was Stacks smoothing.tex, lemma-resolve-general (07FJ),
items item-choose-pii, item-modify-pii, item-choose-deltai, item-set-map-R, and
item-eighth-resolve, including the justifications of both inductions.

## Proved and sorry left

Closed the original hole `Algebra.exists_popescu_rescaling_data`
(node `lem-weil-pbc-popescu-rescaling-data`) by decomposition, not a complete
sorry-free proof of its dependencies.

Added one hole:

- `Algebra.exists_popescu_coefficient_rescaling`
  (`lem-weil-pbc-popescu-coefficient-rescaling`).

Also proved the new generic theorem `Algebra.exists_polynomial_parameter_quotient_chart`
(`lem-weil-pbc-polynomial-parameter-quotient-chart`) completely from Mathlib. Its proof
constructs H and e explicitly, proves the reduction-kernel formula using
MvPolynomial.ker_map and Ideal.map_pow, extends parameter generation via a localization
lift, and cancels the unit variables to identify HQ. This adds no hole.

The combining module has no remaining sorry. Both new theorems have complete source-based
proof docstrings and independent modules/nodes. Their statements were checked at d=0;
the quotient chart also admits n=0 and gives zero quotient rings. The coefficient theorem
retains all original hypotheses, including N>0, the extended-prime equality and the old
coefficient diagram. No arbitrary data is selected in a definition from either theorem.
All three modules compiled using lcompile.py.

## No longer needed

Removed proof imports from the combining module:

- `Sheaf.AlgebraicGeometry.Ogoma`.
- `Sheaf.RingTheory.EssentiallySmoothComp`.
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`.
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`.
- `Sheaf.RingTheory.RegularRingSmoothAscent`.
- `Sheaf.RingTheory.RegularSequencePolynomialVariables`.
- `Sheaf.RingTheory.RegularSequencePowers`.

These remain needed by the rescaling induction and are imported in its new module.
No original mathematical dependency is claimed pruned from the targets' transitive
closure: all are needed in the two lower constructions. The parent's direct proof
node dependencies have moved to those constructions. No unit realization is bypassed.

The parent no longer uses these old nodes directly (their requirements are retained in
the lower constructions):

- `lem-weil-pbc-flat-local-hom-faithfully-flat`.
- `lem-weil-pbc-faithfully-flat-ideal-contraction`.
- `lem-weil-pbc-flat-height-formula`.
- `lem-weil-pbc-field-regular-ring`.
- `lem-weil-pbc-polynomial-ring-smooth`.
- `lem-weil-pbc-regular-ring-smooth-ascent`.
- `def-weil-regular-scheme`.
- `lem-weil-pbc-localization-noetherian`.
- `def-weil-pbc-localization-at-prime`.
- `def-weil-pbc-finitely-presented-algebra`.
- `lem-weil-pbc-regular-local-generators-regular-sequence`.
- `lem-weil-pbc-regular-sequence-polynomial-variables`.
- `lem-weil-pbc-regular-sequence-powers`.
- `lem-weil-pbc-ogoma`.
- `def-weil-pbc-regular-sequence`.
- `lem-weil-pbc-popescu-enlarge-solution-modulo`.
- `lem-weil-pbc-essentially-smooth-composition`.
- `lem-weil-pbc-localization-base-change`.
- `def-weil-pbc-essentially-smooth-ring-map`.
- `def-weil-pbc-algebra-hom-quotient`.
- `def-weil-pbc-mv-polynomial-ring`.

## Where the brief, the DAG or earlier work was wrong

The local read-only clone does not contain literature/stacks-project/smoothing.tex;
a read-only source copy was fetched into this item's sandbox for inspection. The
existing proof's omitted polynomial quotient and rescaling glue was not provided by a
single existing declaration. The two new statements expose those separate gaps.
LeanSearch returned Internal Server Error and was recorded as unavailable, never as
no match. LeanFinder and local-library grep found no combined rescaling theorem;
Loogle found MvPolynomial.ker_map as a component API for the quotient construction.

## New nodes

`lem-weil-pbc-popescu-coefficient-rescaling` states the parameter and coefficient
induction of 07FJ, leaving polynomial quotient formation to the other new node. Its
proof includes faithful-flat contraction, correction in m_L^(n-N), explicit common
denominator clearing, 07FI enlargement, Ogoma, and small smooth-model transport.

`lem-weil-pbc-polynomial-parameter-quotient-chart` states a generic polynomial
quotient construction. Its proof extends parameter generation to the new localized
chart, uses the unit variables to change generators, and identifies the coefficient
reduction kernel. It contains none of the rescaling or Artinian coefficient claims.

No statement or definition was changed, and no change record is required.

## Second reading by S3

1. Compared the full parent-module diff with the repository: the existing theorem
   signature is byte for byte identical; its docstring and public imports are unchanged.
   Only the proof and private proof imports differ. Both additional modules are new.
   No existing statement or definition changed; no change record is needed.
2. All three modules compiled in import order through lcompile.py without errors or
   warnings. Scratch copies with #print axioms show only propext, Classical.choice and
   Quot.sound for exists_polynomial_parameter_quotient_chart; the coefficient theorem
   and parent additionally use sorryAx, as expected from the listed open dependency.
   The sole explicit sorry is exists_popescu_coefficient_rescaling. No forbidden
   declarations or hollow definitions occur. H and e are constructed by ideal maps and
   the first isomorphism theorem. The parent eliminates existentials inside a proof;
   no data definition selects an arbitrary witness of an unproved existence theorem.
3. Read the remaining coefficient statement and its docstring against smoothing.tex,
   lemma-resolve-general, including both induction justifications and the explicit
   denominator formula. It supplies the rescaling and coefficient portion; H and the
   quotient equivalence are independently constructed in the proved generic theorem.
   This is a decomposition with zero net holes closed, not a complete proof. Checked
   d=0 (empty inductions and zero parameter ideal) and quotient-chart n=0 (zero rings).
   N>0 ensures the Artinian target is nonzero. Repeated LeanFinder with “regular system
   of parameters scaling Artinian coefficient solution flat local ring”: regular-sequence
   and flat-base-change hits do not supply the coefficient induction. Loogle found no
   MvPolynomial.quotientEquiv declaration under that name. Local searches for rescaling,
   denominators, enlargement and quotient equivalences found component APIs and
   downstream charts, not a replacement for the open theorem.
4. Read the parent proof downward: the induction supplies an explicit polynomial chart;
   the proved generic theorem constructs its quotient; ring-hom extensionality proves
   evaluation by checking coefficients and variables. Proof imports are private.
   The open induction retains the imports for its stated proof plan. Read sk-thm-p1.json
   realized: this construction below the unit level bypasses no statement or step node.
   Every old direct proof dependency is explicitly listed above; none is claimed
   transitively pruned.
5. All three node Lean statements match their module signatures exactly. The parent's
   changed JSON fields are only proof, proof_deps and proof_origin. The new nodes
   include source, creation, blueprint route, dependencies, searches and exact signatures.
   Their plans agree with the quotient construction, open induction and parent assembly.

Second reading changed only this report: expanded the complete old direct-dependency
list and recorded the independent review. No Lean repair was necessary.
