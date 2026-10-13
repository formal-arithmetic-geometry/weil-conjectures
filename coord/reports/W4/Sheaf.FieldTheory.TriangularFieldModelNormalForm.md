## What changed

Replaced the inherited false finite k-basis assertion with
`Sheaf.FieldTheory.TriangularFieldModelLocalizedNormalForm`, whose coefficients lie in the
explicit ring `Localization.Away h`. The target statement and all existing public imports
are unchanged. Added two private proof imports: the localized normal-form module and
`Mathlib.RingTheory.AlgebraicIndependent.Adjoin`.

The target proof constructs the embedding of the polynomial ring into k(x), extends it to
the localization using `IsLocalization.Away.liftAlgHom`, and proves its injectivity using
the localization criterion. It composes the coefficient equivalence with this embedding
pointwise and proves coordinate injectivity and the evaluation identity in Lean.

## Proved and sorry left

Closed the one original hole: `FieldTheory.triangularFieldModel_normal_form`
(node `lem-weil-pbc-triangular-field-model-normal-form`). No sorry remains in the item.
Added one hole: `FieldTheory.triangularFieldModel_localized_normal_form`
(node `lem-weil-pbc-triangular-field-model-localized-normal-form`). This is a decomposition,
not a claim that the target is axiom-free or that the net hole count decreased.

The remaining assertion is the successive monic quotient and coefficient evaluation step
over D=k[X][1/h]. It does not assert an embedding of D, use algebraic independence, mention
k(x), or assert the target's injective coordinate map into k(x). The target supplies those
parts by a concrete construction and injectivity proof. The new lemma is documented with
the localization base case, induction step, quotient identifications, basis multiplication,
evaluation calculation, and degree-zero case.

## No longer needed

No existing library module or mathematical dependency is pruned. Removed the redundant
public import `Mathlib.LinearAlgebra.Pi` from the new localized module; the remaining
public imports provide all types and instances needed by its statement. The localization-presentation,
monic-quotient and tower-basis nodes remain dependencies of the new localized normal-form
node. The item's former proof dependencies are redistributed between its embedding proof
and that node, rather than removed from the argument.

Removed the earlier sandbox-only `TriangularFieldModelBasisData` module and its node, and
replaced their false assertion. Also discarded the stale sandbox report about
`TriangularFieldModelNormalFormCoord` and `TriangularFieldModelNormalFormEval`; those files
are not part of this delivery. No library module is retired.

## Where the brief, the DAG or earlier work was wrong

The inherited basis-data theorem asserted a finite basis over k and omitted monicity,
degree and evaluation-assignment hypotheses. It is false even with the target hypotheses:
for d=1, m=0, h=1, and a transcendental x, the quotient by T−1 is k[X], which cannot
have a one-element k-basis. The correct finite basis is over D=k[X][1/h]. The new assertion
includes the monicity, degree, variable values, vanishing, and coefficient-evaluation
hypotheses it needs. No such false assertion is left in the delivered files.

Checked edge cases: m=0 has the singleton coefficient space D; d=0 localizes the scalar
ring; a degree-zero monic p_i equals 1 and contradicts vanishing in K. If h=0, an algebra
homomorphism D→K cannot exist, since D is the zero ring. The main theorem already assumes
h≠0 and constructs its homomorphism explicitly.

The source read was Stacks Tags 07BV and 08JZ online, specifically the triangular monic
quotient after denominator clearing and the localization presentation. The unit route is
unchanged; this node is an internal step, not a realization of a unit statement or step.

## New nodes

`lem-weil-pbc-triangular-field-model-localized-normal-form`, in
`dag/nodes/sec-proper-base-change/`, states the localized coefficient equivalence and its
evaluation formula, in a separate module with exactly one named sorry. Its dependencies
retain the existing localization, monic quotient and tower product basis leaves. There
are no changes to existing definitions, statements, or signatures and no change records.


## Second reading by W4

1. Compared both delivered modules with repository sources. The localized module is new.
   The sole existing theorem has its complete signature byte for byte unchanged, including
   hypotheses, quotient, scalar field, and evaluation conclusion. No definition changed.
   Corrected one extra space immediately before its proof delimiter.
2. Compiled both modules locally in import order. Both compile without errors or warnings.
   Scratch copies with `#print axioms` show only propext, Classical.choice, Quot.sound,
   and sorryAx for each theorem. The target contains no sorry; the only delivered sorry
   is the named localized normal-form theorem. There are no forbidden declarations or
   hollow definitions. The existential equivalence is eliminated inside a proposition's
   proof; no public definition chooses arbitrary data from the open theorem.
3. Read the new theorem and its full docstring proof against the explicit equation
   construction and Stacks [07BV](https://stacks.math.columbia.edu/tag/07BV) and
   [08JZ](https://stacks.math.columbia.edu/tag/08JZ). Successive division by monic
   polynomials over D gives the claimed coefficient equivalence and evaluation formula.
   Tested m=0 (one D-coordinate), d=0 (scalar localization), degree-one relations
   (elimination of that variable), degree-zero monic relations (inconsistent hzero),
   h=0 (no algebra map from its zero localization to K), and noninjective phi
   (normal-form uniqueness holds in the quotient even if evaluation loses information).
   Independent leanfinder and loogle searches found monic-quotient coefficient and
   power-basis ingredients, not this simultaneous triangular quotient theorem. Local
   rg in Mathlib, upstream WeilConjectures and lean/Sheaf found no duplicate. The split
   removes the algebraic-independence and field-embedding parts, which the target now
   proves explicitly; it is strictly part of the argument, not a renamed target.
   Closing the entire split requires the successive quotient identifications and is
   not a short direct application of the search results.
4. Read the proof top down: Mathlib constructs the polynomial-field embedding, extends
   it to the localization and proves injectivity; the split supplies only localized
   coefficients; pointwise composition supplies the target coordinate injection and
   evaluation formula. Removed the unused public Pi import from the new module.
   Existing public imports all support the unchanged interface (in particular
   RegularSequence defines Ideal.ofList). The target's former direct dependencies
   localization-away-polynomial-quotient, triangular-field-model-equations,
   monic-quotient-free, tower-product-basis, algebra-hom-quotient and mv-polynomial-ring
   are now in the split's plan rather than pruned from the mathematical argument.
   Checked dag/units/sk-thm-p1.json: neither node realizes a unit statement or step;
   the unit route is unchanged.
5. Checked both nodes against Lean: proof steps, dependency unions and origins match
   the embedding proof and the remaining successive-division argument. The new node
   has its source, self-contained statement, three search kinds, split status,
   creation provenance, blueprint origin, chapter/unit, and verbatim Lean signature.
   No existing node statement or interface changes. Verdict: pass as a decomposition,
   one original hole closed and one localized coefficient hole added, net zero.

Second-reading changes: removed the redundant public Pi import, restored exact signature
whitespace, and expanded the pruning and verification report. The mathematical proof and
new statement were retained.
