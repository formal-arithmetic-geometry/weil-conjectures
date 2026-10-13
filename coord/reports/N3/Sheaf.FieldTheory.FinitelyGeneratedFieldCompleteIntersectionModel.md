## What changed

Replaced the sorry in
`FieldTheory.exists_completeIntersection_fractionField_model` with a complete Lean
assembly of the original argument. The statement and every public import are unchanged.
Added two proof-only imports: `Sheaf.FieldTheory.TriangularFieldModelPresentation` and
`Sheaf.FieldTheory.TriangularFieldModelWeakRegularity`.

The construction now has a concrete polynomial list, rather than an unspecified
complete-intersection witness: variables 0 through d-1 are the transcendence variables,
variable d is T, and variable d+1+i is the distinguished variable of the i-th monic
polynomial. Coefficients involve only earlier variables. No object is chosen in a
definition from a sorried existence theorem. Existential witnesses are eliminated only
inside the proof of the original existential conclusion.

Split the unfinished work into the construction of an embedded triangular presentation
(original steps 1-8) and a generic weak-regularity theorem (step 9). The latter is about
arbitrary monic equations and has no field-extension hypotheses. Proved the actual
assembly: weak regularity plus properness of the ideal gives regularity, the explicit
list supplies the dimension count, injectivity gives a domain, and fraction
representations give surjectivity of Mathlib's fraction-ring lift and the exact formula.

Updated the original node's proof, proof_deps and proof_origin, and added nodes for the
explicit definition and the two remaining theorems. The unit sk-thm-p1 and its realized
route are unchanged; this item is below its realized statements and steps.

## Proved and sorry left

Closed the original hole in
`FieldTheory.exists_completeIntersection_fractionField_model`.
Also proved `FieldTheory.triangularFieldModelEquations_length`.
The explicit definition `FieldTheory.triangularFieldModelEquations` contains no sorry.

Added exactly two holes, each with proof exactly `:= by sorry` in its own module:

- `FieldTheory.exists_triangularFieldModel_presentation`, node
  `lem-weil-pbc-triangular-field-model-presentation`.
- `FieldTheory.triangularFieldModelEquations_isWeaklyRegular`, node
  `lem-weil-pbc-triangular-field-model-weak-regularity`.

This is a decomposition, not a complete proof from sorry-free dependencies: one upper
hole closed and two strictly different lower holes added. The presentation theorem
asserts neither regularity nor an isomorphism of fraction fields. The regularity theorem
asserts no existence of a presentation or map to an extension field. Their combination
and the entire fraction-field extension step are proved in Lean.

Edge cases checked mathematically: r=0 gives just hT-1; d=0 uses k as the initial
polynomial ring; an inseparable finite extension still has the minimal-polynomial power
basis; a constant monic equation 1 may give a zero quotient, so the generic lemma
correctly asserts only weak regularity. The main proof obtains properness separately
from the map to the nonzero field K. All four delivered modules compile with lcompile.

## No longer needed

No existing imports were removed. The original file had no proof-dependency imports;
its public imports supply its unchanged signature and visibility.

The planned dependency `def-weil-pbc-separable-algebraic-extension` and its module
`Mathlib.FieldTheory.Separable` are not needed by this argument. A minimal polynomial
only requires algebraicity, and the construction works for inseparable extensions.

The original direct proof dependencies are now routed as follows (this is rerouting,
not pruning of their underlying mathematical work):

- Transcendence basis, algebraic element, minimal-polynomial quotient isomorphism,
  monic quotient freeness, tower product basis, polynomial ring domain, free module,
  localization-away presentation and localization-away definition are used in the
  presentation node's proof plan.
- Polynomial ring domain, localization-away presentation and definition, polynomial
  ring definition, regular-sequence definition and monic-polynomial nonzerodivisor
  are used in the weak-regularity node's proof plan.
- The module-localization and regular-sequence definitions remain direct dependencies
  of the main proof; the polynomial-ring definition remains a statement dependency.

Thus no other original supporting node or module is claimed as globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The brief described proof-dependency modules as already imported. This item actually
contained only its six public Mathlib imports. The planned Mathlib ingredients provide
power bases, localization presentations and individual nonzerodivisors, but do not
state the assembled triangular presentation or the regularity of its whole sequence.
Those two missing pieces are now separate, explicitly stated items with full proofs in
words. The original DAG's separable-extension dependency was unnecessary: step 2 uses
minimal polynomials in an arbitrary algebraic extension.

LeanSearch returned Internal Server Error for all three attempted queries. Recorded
that service as unavailable, not as no match. LeanFinder, Loogle, and local Mathlib,
source-library and DAG searches were run; they found ingredients but no assembled
triangular-model result. Blueprint search for triangular constructions found unrelated
matrix/trace/purity nodes, with no duplicate of the new statements.

WANTED: literature/stacks-project/algebra.tex, proofs of Tags 07BV and 08JZ, and
literature/stacks-project/more-algebra.tex, proof of Tag 07E1. The local literature
checkout was absent. Read the primary Stacks pages at
https://stacks.math.columbia.edu/tag/07BV,
https://stacks.math.columbia.edu/tag/08JZ and
https://stacks.math.columbia.edu/tag/07E1 instead, together with the original node's
numbered proof and the pinned Mathlib source signatures. No change records or forced
adaptations are required.

## New nodes

`def-weil-pbc-triangular-field-model-equations`:
`lean/Sheaf/FieldTheory/TriangularFieldModelEquations.lean`. The explicit list
construction and its proved length formula; no holes.

`lem-weil-pbc-triangular-field-model-presentation`:
`lean/Sheaf/FieldTheory/TriangularFieldModelPresentation.lean`. The tower, denominators,
quotient presentation, injection and fraction-representation part of Tag 07BV.

`lem-weil-pbc-triangular-field-model-weak-regularity`:
`lean/Sheaf/FieldTheory/TriangularFieldModelWeakRegularity.lean`. The general successive
nonzerodivisor part, separating it from nontriviality of the final quotient.

## Second reading by N3

1. I compared all delivered Lean modules with the repository versions. The original
   theorem signature and existing declarations are unchanged byte for byte; the only
   interface additions are the three explicitly recorded new nodes.

2. I compiled all four modules with `lcompile.py --all`; they compile without errors or
   warnings. The construction contains no hollow definition, and the only remaining
   `sorry`s are the two named split theorems, each with a matching DAG node and a
   complete natural-language proof in its docstring. Explicit `#print axioms` checks
   on every delivered declaration show only `propext`, `Classical.choice`, and
   `Quot.sound`, plus `sorryAx` for the two split theorems and their main user. The
   explicit list definition and its length lemma are sorry-free.

3. I checked the split statements on edge cases `r = 0`, `d = 0`, and constant monic
   equations. The presentation theorem supplies only injection and fraction
   representations; the weak-regularity theorem makes no nontriviality claim, so these
   cases do not overstate either result. Searches found no duplicate declaration in the
   project or Mathlib. I searched with the alternate phrases “successive monic
   equations in distinct polynomial variables” (LeanFinder),
   `"IsWeaklyRegular", "Polynomial"` (Loogle), and integral/finite injection and
   monic-regularity patterns (grep). The source-library theorem
   `MvPolynomial.isWeaklyRegular_ofFn_X_sub_C` covers linear equations only;
   `isWeaklyRegular_append_of_surjective` supplies a useful future assembly lemma,
   but neither closes the arbitrary triangular monic statement in a few minutes.
   Noether normalization supplies integral injections, without this presentation.
   I checked the construction against [Stacks Tag 07BV](https://stacks.math.columbia.edu/tag/07BV)
   and its localization presentation against [Tag 08JZ](https://stacks.math.columbia.edu/tag/08JZ).

4. The proof follows the recorded route: the two split lemmas provide the triangular
   presentation and weak regularity, then the main proof establishes properness,
   regularity, the dimension count, the domain, and the fraction-field equivalence.
   The unit `sk-thm-p1` route is unchanged. The two added imports in the main module are
   proof-only imports; no existing import was removed.

5. I checked the three new node records against their Lean declarations and proof
   dependencies. Their statements and statuses agree with the files, and the original
   node records the revised proof route and dependencies. Only its `proof`,
   `proof_deps`, and `proof_origin` fields changed. For every delivered node,
   `proof_deps` equals the union of the steps’ `uses` fields. The old dependencies
   removed from the direct proof are all accounted for under “No longer needed”.
   `Mathlib.RingTheory.Regular.RegularSequence` remains necessary in the presentation
   module because it defines `Ideal.ofList`, used in the public statement.

I changed only this second-reading report section; no Lean proof or statement required
repair.
