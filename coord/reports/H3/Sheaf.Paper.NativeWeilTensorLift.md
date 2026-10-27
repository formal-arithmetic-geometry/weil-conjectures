## What changed

Reduced `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_lift` without changing its
signature or any existing public import. The proof now constructs its closed structure from
an adjoint tensor bifunctor and monoidal coherence, then derives the required uncurrying
identity on every derived arrow.

The private lemma `uncurry_of_tensor_unit` proves the substantive formal step for arbitrary
categories. For `g = uncurry_W(f)`, the adjunction identity gives
`unit_A ≫ Hom(K,g) = f`. Naturality of the supplied `eta` moves `F(g)` through its comparison,
and naturality of the ordinary inverse adjunction converts the unit-mate formula to the
original all-arrow equation. Thus the split statements do not assume that equation.
`tensorSliceIso` handles the difference between a tensor bifunctor restricted to a fixed
right factor and Mathlib's tensor-right functor. Transport of the adjunction along this
identity-component isomorphism preserves its unit and counit components.

The private lemma `lift_of_tensor_adjoints` also performs witness elimination, tensor-equality
substitution and closed-structure assembly in arbitrary categories. The concrete native theorem
specializes this proved helper. Profiling found that performing the same dependent substitution
inside the concrete derived categories exhausted elaboration heartbeats; the generic formulation
avoids unfolding those category definitions. No shared definition or compilation limit changed.

Added two separate modules, with one named theorem each:
`Sheaf.Paper.NativeWeilTensorAdjoints` and `Sheaf.Paper.NativeWeilTensorCoherence`.
No existing dependency, source-library declaration, target, shared definition or interface
was changed. Updated the item's DAG proof and recorded both new nodes.

All three sandbox modules compiled together with `lcompile.py --all`. Static checks
verified the original signature and public imports, new-node signature matches, dependency
unions, line lengths, and the reported hole counts. The delivery tool reruns compilation
and its preflight checks on the final packet.

## Proved and sorry left

Original item: one hole. Its body is now a complete proof from the following two statements.
This is a decomposition, not a proof with a net reduction in admitted obligations.

Closed upper hole:
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_lift`
  (`lem-sf-native-weil-tensor-lift`).

Added holes, each exactly `:= by sorry` in its own module:
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_adjoints`
  (`lem-sf-native-weil-tensor-adjoints`): tensor bifunctor, parameter-natural adjunctions,
  invertible tensor comparison, and its inverse's formula on adjunction units. It supplies
  no monoidal constraints, tensor unit, coefficient-unit identifications or native symmetry.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_coherence`
  (`lem-sf-native-weil-tensor-coherence`): monoidal constraints, coefficient units and
  coherent forgetting on an already supplied adjoint tensor and its fixed unit mate.
  It constructs no tensor adjunction and assumes no all-arrow transposition equation.

There are zero holes in the item module and two holes in the added modules: closed 1,
added 2, net -1. Neither private helper has a hole; no definition contains a hole.
The original theorem retains its exact hypotheses and conclusion.

## No longer needed

Removed the item's private import of `Sheaf.Paper.WeilFrobeniusActionResolutions`:
its declarations are not needed by the formal combining proof. The action-site realization
remains a mathematical dependency in the two new nodes' proof plans; it is not withdrawn.
The new statement modules import only what their statements require.

The full ringed transposition theorem is not applied to prove the all-arrow identity:
that identity is proved formally from the unit mate. Tensor-only ringed descent suffices
in the coherence node's plan. The existing public import of
`Sheaf.Algebra.Homology.RingedForgetTensorTransposition` is preserved, so neither that
module nor its dependencies are claimed pruned from the targets' import closure.
All five original mathematical dependencies remain in the source construction plans,
except that the full transposition theorem is replaced by its tensor-descent part where
only coherence is needed. No module or DAG node is withdrawn; pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No false original statement or target change was found. The previous plan described a
transport of the entire ringed uncurrying law to arbitrary derived arrows. That last part
can instead be discharged from the comparison on adjunction units by the formal argument
above. The two remaining construction statements have different mathematical roles and
neither reproduces the original theorem under another name.

The unit-mate proof is valid without boundedness, constructibility, faithfulness or
conservativity. Its zero-object specializations are the same adjunction identities.
The new construction plans explicitly retain the empty-scheme and zero-complex cases;
no nonzero-object hypothesis was introduced. No unit's realized statement or proof route
was bypassed.

## New nodes

`lem-sf-native-weil-tensor-adjoints`: the adjoint-construction and invertible-mate parts
of the original node's action-site argument, sourced to the blueprint's
internal-Hom/transposition paragraph and Stacks 06YS, 08J9 and 0A97. The Lean statement
separates these assertions from every monoidal constraint.

`lem-sf-native-weil-tensor-coherence`: the constraint-descent and degree-zero coefficient
unit parts of that argument, sourced to the same blueprint paragraph and Stacks 06YS
and 0FPT (`lemma-symmetric-monoidal-derived`). The tensor functor is retained by equality,
and the supplied comparison is retained, including its unit normalization.

Searches ran through `msearch.py`: Lean Finder returned general closed/monoidal transport,
Cartesian Frobenius-mate and rigid adjunction results; Loogle returned adjoint uniqueness,
adjunction naturality and `MonoidalCategory.ofTensorHom`; the Mathlib grep for the native
names and `TensorCoherence` returned zero hits. Local source searches found the ringed
closed and forgetful comparison theorems and ordinary tensor identification, but no native
construction with these prescribed representatives. Whole-blueprint searches for tensor
adjunction and tensor coherence found no duplicate of either new statement.

No change record is required: only the item module, two new theorem modules, and their
own node files are changed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
