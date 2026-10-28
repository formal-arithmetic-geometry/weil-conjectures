## What changed

Marked `WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_on_good_representatives`
`STATEMENT-DISPUTED`: its bridge `β` is entirely arbitrary, including the zero morphism.
The original theorem, its signature, its proof hole and its imports are preserved.

Added two fully proved private diagnostics in the item module:
`forall_bridge_iff_zero` and
`scalarTowerTensorLimitSquare_arbitrary_bridge_iff_zero`.
The latter uses exactly the displayed scalar/tensor composites on complete inputs,
with the canonical `scalarTensorCompleted` isomorphism. Neither diagnostic invokes
the disputed theorem or its `DerivedSigmaModel` hypothesis. Updated the item's node
proof record with the obstruction and the actual diagnostic argument. No public
interface or other existing module was changed. The final module compiled successfully
through `lcompile.py` in 5.2 seconds, with no compiler messages.

## Proved and sorry left

Closed **0 of 1** existing holes; added **0** holes; split off **0** statements.
This delivery is a statement dispute with a proved diagnostic, not a proof or a
reduction of the original assertion.

Proved privately:
- `forall_bridge_iff_zero`: if `e : A ≅ B`, then
  `(∀ β : A ⟶ B, β ≫ f = g) ↔ f = 0 ∧ g = 0`.
- `scalarTowerTensorLimitSquare_arbitrary_bridge_iff_zero`: the exact corresponding
  characterization for the two displayed scalar/tensor coordinates, on complete
  inputs, using the existing canonical comparison as `e`.

The only remaining hole is
`WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_on_good_representatives`
(node `stage3-pur-scalar-tensor-limit-good-representatives`).

## No longer needed

None. No imports, modules, declarations or dependencies were withdrawn. In particular,
this item still has both the DAG parents
`stage3-pur-scalar-tensor-limit-transport-assembly` and
`stage3-pur-scalar-tensor-limit-strict-equation-assembly`; zero current callers would
not justify withdrawal. Its existing parent proof is not replaced by another hole.

## Where the brief, the DAG or earlier work was wrong

**STATEMENT-DISPUTED: the arbitrary bridge quantifier does not express the canonical
scalar/tensor comparison.**

For a fixed pair of representatives write `f` for the postcomposition following β
and `g` for the right-hand coordinate. The statement demands `β ≫ f = g` for every β.
Putting β = 0 gives g = 0. If the three inputs are complete, the canonical
`scalarTensorCompleted` is an isomorphism e between the two bridge objects. Putting
β = e.hom and cancelling e gives f = 0. Conversely those two zero equations suffice
for every β. This entire equivalence, specialized to the actual project composites,
is the compiled private diagnostic. It uses no strict compatibility assumption.

The intended mathematical nonzero test is the identity coefficient embedding
E = L, with both representatives the degree-zero completed integral coefficient unit
on a nonempty characteristic-zero field spectrum. Its tensor is the unit and all
these objects are complete. Under their normalized unit identifications the scalar
reduction and the tensor realization have nonzero identity coordinate. The zero
bridge and the canonical identity bridge therefore cannot both satisfy the stated
formula. The vanishing diagnostic is formalized; this particular nonzero geometric
specialization is an informal edge-case check, not a claimed Lean counterexample.

The source normalization describes the *specified* scalar/tensor comparison, not
all morphisms with its source and target. A repair must choose that comparison or
state its independent strict representative normalization and adapt both parents.
Merely restricting β to an isomorphism still does not specify the comparison.
I have not weakened the theorem or introduced another name with its hole.

The current server queue row was `proof / route`, with one hole and no build-error
or rework record for the module. The direct Lean importer is
`Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly`. The other DAG parent,
`Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly`, is currently held by A8;
its existing arbitrary-bridge hypothesis is not silently changed in this delivery.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport": "c9b7292bb96de6aad18029144fedc251a876617b"}, "results": {"Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly": {"hash": "852ed0565aa9cc152bba17a7f1cbc31a07ff28bd", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:15:52+0800", "transitive": 0, "version": 1}
```

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
