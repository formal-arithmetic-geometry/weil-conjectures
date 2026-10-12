## What changed

Completed `AlgebraicGeometry.derived_single_hom_evaluation` in
`Sheaf.AlgebraicGeometry.DerivedSingleHomEvaluation`, preserving its signature and docstring.
Added the proof-only import `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`.

The proof follows all three steps of `lem-sc-derived-single-hom-evaluation`:
it constructs the unit-Hom evaluation after precomposition with Q, descends it through
fully faithful localization precomposition, and constructs the comparison for every
K-injective target using the resolution augmentation. Naturality of the derived comparison,
the Hom-complex bifunctor, and the supplied evaluation gives the required equality.

Three private helpers contain fully implemented categorical calculations:
`evaluationIso` constructs the evaluation isomorphism by composing supplied isomorphisms;
`evaluationIso_hom_app` computes its component; `evaluation_compatibility` proves the
naturality and cancellation equation. None introduces a postponed proof or new assumption.
Abstracting these calculations avoids unfolding the sheaf Hom-complex construction during
elaboration. The heartbeat setting is scoped to the existing theorem.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.derived_single_hom_evaluation`
(node `lem-sc-derived-single-hom-evaluation`). Added zero holes; zero sorries remain in
the delivered module. This is a proof from the existing planned declarations, not a
new decomposition. The private helpers are all implemented or proved.

Uses `CategoryTheory.derivedInternalHom_comparison` from
`def-pur-derived-internal-hom` and `CategoryTheory.quasiIso_homComplex_map` from
`lem-pur-rhom-well-defined`, with Mathlib localization and the existing functorial
K-injective-resolution API. This delivery does not claim to close their transitive dependencies.

## No longer needed

None. No imports were removed and no planned nodes or modules were bypassed.
Both original public imports are required by the statement. The added proof-only import
supplies the quasi-isomorphism theorem used to construct c. The node's existing proof and
proof_deps already describe this exact route and need no update. The unit record
`sk-thm-picard-duality` has empty realized node lists; no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's three-step plan fits the unchanged statement. The earlier sandbox attempt
left the final compatibility equation as a sorry, failed to simplify the opposite identity
in the Hom-complex map, and used broad unfolding on the concrete evaluation isomorphism.
The identity is now simplified with an explicitly typed functor identity, and the component
and compatibility calculations are proved for abstract functors before specialization.
No mathematical statement or definition was corrected. No new nodes or forced adaptations.

## Second reading by W2

1. Compared the delivered module with the repository version. The theorem signature and
   docstring are byte-for-byte unchanged; only a proof-only import, private proof helpers,
   and the theorem proof were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The
   proof contains no `sorry`, axiom, unsafe, opaque, extern, or hollow definition. The
   helper calculations use only categorical identities and the supplied comparison
   theorems.
3. Checked the existing node and searched the repository for overlapping Hom evaluation
   declarations. No new statement was split off, and the proof uses the planned
   `derivedInternalHom_comparison` and `quasiIso_homComplex_map` route.
4. The proof is pruned to the shortest available route in this module. Both public imports
   are statement dependencies; `QuasiIsoHomComplexMap` is private to the proof. No planned
   dependency is bypassed and no import can be removed.
5. The node's statement, proof steps, proof dependencies, and origin agree with the Lean
   proof. The unit's realized lists are empty, so no unit step is bypassed.

Changed after this reading: appended this review record only. No Lean, node, or change
record required repair.
