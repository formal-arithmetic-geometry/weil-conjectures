## What changed

Reduced `AlgebraicGeometry.perfect_rhom_tensor_comparison` without changing its signature.
The dual object is identified by equality with the actual RHom object; evaluation,
comparison, bidual, coevaluation and base change are explicitly constructed.
The coevaluation equation and uniqueness are proved by the inverse comparison and
cancellation. The existing dualizable evaluation criterion proves both triangle identities;
unitors are cancelled to construct the specified ExactPairing.

Two proved private categorical helpers use the rigid tensor Hom equivalences and Yoneda
bijectivity to prove that adjuncts of evaluation are invertible. They prove biduality and
base change, the latter using ExactPairing.map along the given monoidal functor. This works
for every CoreMonoidal structure, hence in particular every stipulated canonical model.
The local calculations are isolated into two smaller modules, one theorem per module.
Proof-only imports were adjusted and the item's DAG proof follows the actual Lean proof.

## Proved and sorry left

Closed the only original hole: `AlgebraicGeometry.perfect_rhom_tensor_comparison`
(node `lem-pc-perfect-rhom-tensor-comparison`). There is no sorry in its module.
Added exactly two holes, both whole public named theorem proofs:

- `AlgebraicGeometry.exists_perfect_rhom_dual`
  (`lem-pc-perfect-rhom-tensor-comparison-dual`): quasi-coherence and perfectness of RHom(K,O).
- `AlgebraicGeometry.perfect_rhom_evaluation_isomorphisms`
  (`lem-pc-perfect-rhom-evaluation-isomorphisms`): invertibility of the evaluation comparison
  for every ambient derived object, without requiring the second argument quasi-coherent.

This is a decomposition (one upper hole closed, two lower holes added), not a complete
axiom-free proof of perfect duality. The existing imported
`AlgebraicGeometry.dualizable_evaluation_criterion` remains a dependency; its sorry is not
changed or added by this delivery. Both private Yoneda helpers are completely proved.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`,
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct`,
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`,
`Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom`, and
`Sheaf.Paper.DerivedInternalHomRestrictOpen`.

The bounded-flat, strictly-perfect Hom and open restriction lemmas are retained as proof
imports and proof dependencies of the two new local-calculation modules; they are relocated,
not pruned from the argument. DerivedPullbackTensorProduct remains publicly reachable through
the original DerivedPullbackMonoidalModel statement import, which is unchanged.

The proof no longer needs `lem-pc-flat-complex-derived-pullback` or its module
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`: transport of exact pairings replaces the
termwise base-change step. No claim is made that this module becomes globally unreachable,
since other targets or paths may still import it. There is no separate base-change or bidual
intermediate theorem left to prove. The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The available local dependency statements do not directly state the global perfect dual or
the canonical evaluation comparison. The two new statements isolate precisely those gaps.
The existing node's base-change calculation is unnecessary once the exact pairing is known:
a monoidal functor preserves it and its evaluation represents the internal dual by Yoneda.

The local `literature/stacks-project/cohomology.tex` is absent on this machine. Read the
source at https://stacks.math.columbia.edu/tag/08DQ, /tag/0FPC and /tag/0GM7 instead.
The statements and local-calculation proof sketches agree with those sources. The new
lemmas were checked on K=0, finite-free degree-zero complexes, finite-projective direct
summands, shifts, empty schemes, and arbitrary unbounded second arguments. No positivity,
properness, flatness of g, or boundedness of the second argument is used. Naturality of a
chosen adjunction changes canonical adjuncts only by natural isomorphisms; the helpers prove
bidual/base-change invertibility directly for the adjunctions in the unchanged signature.

LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder returned
only generic complex/derived-category isomorphisms; Mathlib grep found no scheme-level RHom
comparison. No statement or definition was changed; no forced adaptations are required.

## New nodes

`lem-pc-perfect-rhom-tensor-comparison-dual`, module
`Sheaf.AlgebraicGeometry.PerfectRHomTensorComparisonDual`, isolates the strictly-perfect dual
calculation and locality of quasi-coherence/perfectness (Stacks 08DQ). Its equality fixes the
underlying object, so it supplies no arbitrary witness data.

`lem-pc-perfect-rhom-evaluation-isomorphisms`, module
`Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms`, isolates the global evaluation
isomorphism from the local finite-projective tensor-Hom calculation (Stacks 08DQ and 08DM).
Its ambient-object quantifier is needed by the existing dualizability criterion. It supplies
neither coevaluation, triangle identities, biduality, nor base change; those are composed in
the item's complete Lean proof. No change records are needed.

## Second reading by D2

1. I compared the delivered item module against the repository version. The target signature
   is byte for byte unchanged; the two additional modules and node files are the only additions.
   Verdict: passed.
2. I compiled all three delivered modules with `lcompile.py`; they compile without errors. The
   item has no `sorry`, and the only remaining `sorry`s are the two named split-off theorems,
   each with a matching node and source proof docstring. No forbidden declarations or hollow
   definitions occur. Verdict: passed subject to the two explicitly recorded split-offs.
3. I checked the split-off statements against the imported declarations and the edge cases
   recorded above. The dual theorem fixes its underlying object by equality, and the evaluation
   theorem has exactly the ambient quantifier required by the criterion; neither duplicates the
   item statement. Verdict: passed.
4. I checked the proof route and imports. The proof uses the two new local-calculation nodes,
   the existing dualizable evaluation criterion, Yoneda, and the rigid tensor equivalences.
   Removed imports and the no-longer-needed flat pullback node are listed above. Verdict: passed.
5. I checked the DAG node statements, proof steps, proof dependencies, origins, and the unit's
   realized route against the Lean proof. The unit statement and realized steps remain intact.
   Verdict: passed.

Changed during second reading: added this review record only; no Lean declarations or DAG
statements were altered.
