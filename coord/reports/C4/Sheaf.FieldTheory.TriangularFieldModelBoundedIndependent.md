## What changed

Proved `FieldTheory.triangularFieldModel_bounded_independent` without changing its
signature, by induction on the number of tower variables. The base case explicitly
evaluates the quotient back into `Localization.Away h`; localization extensionality
makes this a left inverse to psi. At a successor, construct the preceding localization
map by `liftAlgHom`, descend each last coefficient, and use the induction hypothesis.

Added `Sheaf.FieldTheory.TriangularFieldModelCoefficientDescent`, containing the proved
`FieldTheory.triangularFieldModel_coefficient_descent`. Its only monicity and degree
hypotheses concern the last polynomial; the preceding relations are arbitrary. It
constructs a map from the simultaneous quotient into `AdjoinRoot` over the preceding
quotient, then extracts the last coefficients with the monic power basis. No quotient
isomorphism or iterated basis construction is needed. The item imports this module and
`Mathlib.RingTheory.Localization.Algebra` privately. Updated both proof routes in the DAG.

Both modules compile together without warnings. The new proof constructs every map
explicitly and chooses no data from an existence theorem. The source pages read are
Stacks 07BV (lemma-colimit-syntomic), the triangular monic argument, and 08JZ
(lemma-localize-at-element), the localization presentation.

## Proved and sorry left

Closed the sole original hole: `FieldTheory.triangularFieldModel_bounded_independent`
(node `lem-weil-pbc-triangular-field-model-bounded-independent`).

Also proved the new `FieldTheory.triangularFieldModel_coefficient_descent`
(node `lem-weil-pbc-triangular-field-model-coefficient-descent`).
No sorry remains in either delivered module; no holes were added. This is a proof,
not a decomposition. The monic power basis and localization facts used are Mathlib proofs.

## No longer needed

The independence proof no longer needs:
- `lem-weil-pbc-tower-product-basis` (`Module.Basis.smulTower`): extract one coefficient
  at a time and induct, instead of constructing a product basis.
- `lem-weil-pbc-localization-away-polynomial-quotient`
  (`IsLocalization.Away.mvPolynomialQuotientEquiv`): construct the base-case left
  inverse directly and use localization extensionality.

`lem-weil-pbc-monic-quotient-free` remains needed by the proved coefficient-descent
lemma. No existing source import was removed: all four original public imports supply
statement-level definitions, including `Ideal.ofList` from RegularSequence.
Removed the exploratory direct proof imports `Mathlib.Data.Fin.Tuple.Basic` and
`Mathlib.Algebra.MvPolynomial.Eval` from the item, since its imported modules already
expose them. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or signature change. The planned simultaneous/successive quotient
isomorphisms are unnecessary for independence: a single explicitly constructed map into
the last monic quotient suffices. No changes to definitions or other modules were required.
The blueprint ancestry tool returns no ancestor when following the existing nodes'
`created.item` module strings; the new node records the explicit ancestry already given
by the localized-normal-form node, ending at `thm-weil-pbc-finite-etale-lifting`.

## New nodes

`lem-weil-pbc-triangular-field-model-coefficient-descent`, in
`dag/nodes/sec-proper-base-change/`, records the last-variable coefficient descent
proved in `Sheaf.FieldTheory.TriangularFieldModelCoefficientDescent`. It is a proper
one-step tool: its conclusion is zero in the preceding quotient, not zero in the
localization, and it requires no monicity or degree assumptions for earlier relations.
Checked zero preceding quotient, zero h, zero last degree, empty earlier exponent sets,
and n=0. All are handled by the proof, without additional hypotheses.
Blueprint searches for triangular, monic, bounded monomial and last-variable coefficient
found no existing blueprint statement of this tool. The three Mathlib search kinds were
run through msearch; LeanSearch was unavailable, while Loogle and grep supplied the
monic power-basis ingredients. There are no change records or forced adaptations.

## Second reading by C4

1. I compared both delivered Lean modules and the existing bounded-independence module
   against the repository versions. Existing declaration signatures are unchanged; the
   added coefficient-descent declaration is recorded by its new DAG node. Verdict: pass.
2. I compiled both modules with `lcompile.py --all` and checked that neither contains
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof terms
   use only ordinary definitions and the permitted imported results. Verdict: pass.
3. I reviewed the new coefficient-descent statement, including zero quotient, zero h,
   zero last degree, empty earlier exponent types, and n = 0. It is a strict one-step
   reduction and is not a restatement of the target; no existing library declaration
   duplicates it. Verdict: pass.
4. I checked the proof from the target downward: the base case uses an explicit
   localization evaluation, and the successor uses explicit `liftAlgHom` and the new
   last-coefficient reduction. The old product-basis and localization-presentation
   dependencies are pruned as reported, while the unit route remains represented by the
   target and its coefficient step. Verdict: pass.
5. I checked that the bounded-independence node's proof steps, dependencies, and origin
   match the Lean proof, and that the new node has the required statement, source,
   searches, proof, and Lean record. Verdict: pass.

I changed only this report section during second reading; no Lean proof or statement
required repair.
