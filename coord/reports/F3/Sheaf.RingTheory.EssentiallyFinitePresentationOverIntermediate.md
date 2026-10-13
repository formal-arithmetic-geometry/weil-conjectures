## What changed

Proved `RingHom.essentially_finite_presentation_over_intermediate` with its original signature
and docstring unchanged. Added proof imports of `Mathlib.RingTheory.FiniteStability` and
`Mathlib.RingTheory.Localization.Basic`.

The proof chooses a finite set of essential generators of `S` and writes their images in `T`
as fractions over `P`, using `Algebra.EssFiniteType.finset` and `IsLocalization.surj`.
Private helpers `RingHom.finiteCompatibilityIdeal` and
`RingHom.FiniteCompatibilityQuotient` construct the ideal and quotient of
`MvPolynomial s (S ⊗[R] P)` with the two finite families of generator equations.
These are actual constructions, with no data chosen from an unproved existence theorem.
Mathlib supplies finite presentation under base change, adjoining finitely many variables,
and quotienting by a finitely generated ideal.

The proved private helper `RingHom.finiteCompatibilityQuotient_isLocalization` establishes
the localization identification without any finite-presentation hypothesis on `P`.
It constructs quotient evaluation, takes the image of `U` as the new submonoid, and constructs
both inverse comparison maps by `IsLocalization.lift`. The quotient equations identify the
variables as denominator inverses. Cancellation by those units proves agreement on the
essential generators. Adjoin induction and localization uniqueness extend agreement to `S`;
tensor, polynomial, quotient, and localization extensionality complete the inverse check.
An algebra equivalence then transports the localization structure to the specified map.

The existing DAG plan is realized directly: finite generators and fractions (step 1), the
explicit finitely presented quotient (step 2), and inverse localization maps (steps 3–4).
No node, public definition, existing statement, or other module changes.

## Proved and sorry left

Closed the one original hole in
`RingHom.essentially_finite_presentation_over_intermediate`
(node `lem-weil-pbc-essentially-finite-presentation-over-intermediate`).
The private localization helper is also fully proved. No `sorry` remains and none is added;
zero statements are split off. This is a complete proof, not a decomposition.

The final single-file compile succeeds without errors or warnings. The delivery dry run
also checks the axioms of all declarations against the three allowed axioms.

## No longer needed

None. No original imports are removed, and no planned dependency node or module is pruned.
The proof uses the finite-generation, finite-presentation, and localization ingredients of
the existing plan through their Mathlib declarations. No auxiliary module is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The unit route stays intact. The arbitrary cardinalities of
`U` and the denominators of `S` cause no additional finiteness requirement: only the images
of the finite set of essential generators receive polynomial variables. Empty generator
sets, zero rings, and noninjective localization maps are admitted throughout; uniqueness
of maps from localizations, rather than injectivity, supplies the inverse identities.

The library searches confirmed that Mathlib has nonlocalized finite-presentation cancellation
but no direct essentially-finite-presentation cancellation lemma. The existing planned
localized construction can nevertheless be proved entirely using Mathlib.

## Second reading by F3

1. **Statements unchanged.** Compared the delivered module with the repository version. The target theorem signature and all existing declarations are byte for byte unchanged; only proof imports, private helpers, and proof terms were added.

2. **Proof compiles and uses permitted axioms.** Compiled the module with `lcompile.py`; it succeeds without errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The construction uses explicit ideals, quotients, polynomial evaluation, and localization maps, so no data is selected from an unproved existence theorem.

3. **Statements and dependencies reviewed.** The private localization helper is a strictly intermediate result needed to construct the target witness; its equations are the finite generator and denominator relations from the stated argument. No public split-off statements or new DAG nodes were added, and searches found no existing Mathlib or Sheaf declaration duplicating the target.

4. **Proof route and pruning reviewed.** The proof follows the unit route: choose essential generators and fractions, form the finite compatibility quotient, prove its localization identification, and obtain finite presentation by base change, polynomial extension, and finitely generated quotient. Both proof-only imports are minimal for the declarations used; no old dependency node is made unnecessary.

5. **DAG and unit agreement.** The target node's declaration, statement, and proof dependencies remain aligned with the Lean proof, and the unit's realized route is preserved. No node or statement changes were required.

I changed only the proof implementation and its two proof-only imports; no mathematical statement, definition, DAG node, or public import was changed.
