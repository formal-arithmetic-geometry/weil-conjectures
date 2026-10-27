## What changed

Proved `ModuleCat.coinduction_total_hom_model` in
`Sheaf.Algebra.Homology.CoinductionTotalHomModel` without changing its statement,
public imports, or existing docstring. All added constructions and lemmas are private.
The additive instance for coextension is supplied locally inside the theorem proof.

The proof constructs the total-Hom transposition and its inverse using Mathlib's
restriction/coextension adjunction maps, proves their inverse and differential
identities, and verifies naturality and both homotopy clauses. Restriction preserves
acyclicity; transposing a null-homotopy proves coinduced K-injectivity.

Evaluation and insertion identify restricted coinduction with total Hom from A[0].
Product projections identify this with the existing monoidal internal Hom complex;
the source differential vanishes and only source degree zero contributes. The
K-injective derived comparison and uniqueness of right adjoints then give the stated
ordinary derived internal Hom on every specified representative. The existing node's
last proof step and proof origin are updated to describe this actual comparison.

Change record: `coord/changes/coinduction-total-hom-model-proof-scopes.md`.
Preflight requested it for the added section and scoped elaboration commands;
there are zero downstream Lean modules and no consumer adaptations.

## Proved and sorry left

Closed: `ModuleCat.coinduction_total_hom_model`
(node `lem-trf-coinduction-total-hom-model`): 1 of 1 original holes.
Added holes: none. Remaining holes in the item: none. Split off: none.
Every private helper is proved or explicitly constructed without `sorry`.
The module compiled successfully through lcompile.py (37.6 seconds).

## No longer needed

None. All five original public imports remain because the statement needs them.
The original four dependency nodes remain used. No module is withdrawn, and no unit
statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original final proof step referred to an arbitrary-K-injective-representative
clause of the recorded ordinary derived-Hom definition. That Lean declaration is
an abbreviation for the existing derived closed internal Hom, so the comparison
requires proof. This delivery supplies it through the already constructed derived
adjunction, without introducing a second RHom construction or changing the statement.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
