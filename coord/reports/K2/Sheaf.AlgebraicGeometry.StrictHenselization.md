## What changed

Proved both holes in `lean/Sheaf/AlgebraicGeometry/StrictHenselization.lean`.
The affine inclusion equivalence is proved by lifting pointed morphisms with
`AffineEtale.Spec.preimage` and explicitly transporting each affine pointed
neighbourhood along `Scheme.isoSpec`. The properties theorem combines this
equivalence with affine cofinality, transfers cofilteredness via Mathlib's fully
faithful initial functor lemma, and maps the opposite ring colimit limit cone
through `Scheme.Spec`.

Added the proof-only import `Mathlib.CategoryTheory.Filtered.Final`.
Kept existing public imports and every existing signature and definition unchanged.
Updated the existing DAG node's proof, proof dependencies, and proof origin to
record the compiled argument. No new declarations or nodes.

## Proved and sorry left

Closed 2 of 2 original holes:
- `AlgebraicGeometry.Scheme.strictHenselizationAffineInclusion_isEquivalence`.
- `AlgebraicGeometry.Scheme.strictHenselization_properties`.

Both belong to `def-weil-pbc-strict-henselization-limit`. No sorry remains in
the module and no holes were added. This is a proof, not a decomposition.
Local compilation succeeds without errors or warnings. The delivery dry run
checks all declarations for nonstandard axioms.

## No longer needed

None. No import was removed; the proof uses affine cofinality and each existing
public Mathlib import supports the definitions or statements. The original node
had no proof dependencies; the updated dependencies record the actual argument.
The full-subcategory colimit comparison node remains needed for its cofilteredness
and representative-equivalence clauses. No blueprint unit statement or step is
bypassed (the unit's realized statement and step lists are empty).

## Where the brief, the DAG or earlier work was wrong

The node's proof and proof_deps were empty despite the module documenting the
argument. They now record the Lean proof. No mathematical statement, definition,
or target was changed. All required machinery exists in Mathlib and the already
proved affine-cofinality module; no new intermediate theory was necessary.

## Second reading by K2

1. I compared the delivered module with the repository version. Existing declarations and definitions are byte-for-byte unchanged; the only source change is the proof-only import `Mathlib.CategoryTheory.Filtered.Final` and the two theorem proofs.

2. I compiled `lean/Sheaf/AlgebraicGeometry/StrictHenselization.lean` with the prescribed launcher. It succeeds with no errors or warnings, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and the two proved theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

3. No statements were split off and no new declarations were added. The two existing theorem statements are unchanged and are the exact target statements. No duplicate intermediate statement was introduced.

4. The proofs take the short available route: Mathlib category-of-elements fullness/faithfulness and affine spectrum isomorphisms prove the equivalence; the existing affine-neighbourhood initial/final theorem and Mathlib cofiltered transfer prove the representative-category properties; `Scheme.Spec` preserves the colimit limit. The proof-only import is used. The DAG proof dependencies were pruned to the existing affine-neighbourhood-cofinal node, which is the project declaration directly used by the proof; the previously listed generic leaves were not used directly.

5. The unit route is preserved: the strict henselization definitions, affine representative equivalence, cofilteredness, and Spec limit remain exactly those of the unit. The DAG proof, dependencies, and origin now match the Lean proof.

I changed only the proof-dependency metadata and this report. No holes remain and none were added; no modules were pruned.
