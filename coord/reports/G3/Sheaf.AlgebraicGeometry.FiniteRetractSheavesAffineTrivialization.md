## What changed
The original finite-family theorem is reduced by genuine finite-set induction to a single
sheaf retract theorem in the new module
`Sheaf.AlgebraicGeometry.SingleFiniteRetractSheafAffineTrivialization`.
The empty family is handled by the affine-open basis. In the insertion case, refine the
intersection of the previously obtained open and the new single-sheaf open to an affine
neighbourhood; restrict all the isomorphisms using coproduct and unit comparisons.
Two private isomorphism constructions provide restriction of finite free sheaves and
composition of restrictions. Neither contains a hole or chooses data from an open theorem.
The existing public imports and existing theorem signature are unchanged.

## Proved and sorry left
Hole closed: `AlgebraicGeometry.Scheme.exists_affine_trivialization_of_finite_retracts`
(node `lem-pc-finite-retract-sheaves-affine-trivialization`).
Hole added and left: `AlgebraicGeometry.Scheme.exists_affine_trivialization_of_finite_retract`
(node `new-pc-single-retract-sheaf-affine-trivialization`).
This is a decomposition: one upper hole closed, one strictly simpler single-object hole
added, net zero holes. The finite-family combination and empty case are proved. The
original theorem still depends on sorryAx through the named single-object theorem.
No other sorry remains or is added. The earlier nonempty-family hole was removed before
delivery; it was never an existing library declaration.

## No longer needed
The original node's direct proof dependencies
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-finite-projective-standard-free-cover` are no longer used directly by the
finite-family proof. Its proof_deps now contains only the new single-retract node.
The corresponding plain imports `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
and `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover` were removed from the item;
they remain the planned dependencies of the single-retract theorem in its new module.
No module is pruned from the total import closure.

## Where the brief, the DAG or earlier work was wrong
The first worker's nonempty-family lemma merely moved virtually the entire argument to
another hole. Its docstring also lacked the complete proof required for a hole, and the
item's proof_deps retained nodes no longer directly used. Replace that lemma with the
single-object local argument and prove the real finite-family reduction.

## New nodes
`new-pc-single-retract-sheaf-affine-trivialization` isolates the one-object affine
idempotent/projective-module argument from the proved finite-intersection argument.
It has a complete proof docstring, source, all three required search kinds and a verbatim Lean signature.
No existing statement or definition changes; no change record is needed.

## Second reading by G3
1. Compared the complete original module with the delivery using diff and checked the
   original theorem signature byte for byte by assertion. Existing signatures, definitions,
   visibility and public imports are unchanged. Verdict: pass.
2. Compiled both delivered modules locally in import order through lcompile.py. Inspected
   both definitions: restriction-free uses the preserved coproduct and unit isomorphism;
   nested restriction is an Iso.refl construction, checked by Lean. No hollow definition,
   forbidden declaration or arbitrary witness construction exists. The sole hole is the
   named single-retract theorem. Axiom probes are recorded below. Verdict: pass.
3. Read the new single-retract statement and complete proof docstring. Tested empty U
   (hx impossible), zero/rank-zero retracts, singleton families, and differing ranks.
   The single-object step is true and strictly part of the original argument. Searched
   LeanSearch (unavailable: Internal Server Error), LeanFinder, Loogle and Mathlib/upstream/local sources with direct-summand, idempotent,
   restriction and local-freeness terminology. No applicable exact theorem was found;
   the nearby locally-free-to-summand result is the reverse implication and the free-locus
   theorem adds Noetherian hypotheses. Formalizing the affine splitting/localization
   transport remains substantial work, rather than a quick closure. Verdict: pass.
4. Reviewed the proof from the original theorem downward. The finite-set induction uses
   Mathlib affine refinement, restriction functors, preserved coproducts and unit comparison.
   Every removed old dependency is listed above. The unit sk-thm-picard-duality has empty
   realized statement/step arrays; this below-unit refinement bypasses no realized node.
   Existing public imports support the interface; new plain imports carry the proof route.
   Verdict: pass.
5. Updated the original node's proof and proof_deps to the actual finite induction, and
   proof_origin to the repair. The new node records the single-object theorem's exact
   signature, statement dependencies, sources, proof steps, search results, blueprint
   provenance and planned dependencies. Verdict: pass.
Changes made: removed the near-restatement nonempty lemma and node; added the single-sheaf
module and node; proved the full finite-family reduction and restriction comparisons;
corrected dependency records and the decomposition/progress report.

Axiom verification: scratch copies with #print axioms compiled locally. Both private
restriction constructions use only propext, Classical.choice and Quot.sound (or fewer).
The finite-family theorem and the single-object theorem use only those three axioms and
sorryAx, the latter arising from the explicitly listed single-object hole.

Dry-run repairs: retained the original open command byte for byte and qualified the
Limits names inside the private construction. Added the actual unavailable LeanSearch
attempt so all required search kinds are recorded without inventing a verdict.
