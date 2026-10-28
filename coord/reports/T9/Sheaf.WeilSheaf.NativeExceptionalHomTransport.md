## What changed

Filled all three proof obligations in `Sheaf.WeilSheaf.NativeExceptionalHomTransport`, preserving every existing public signature, definition and public import. Added a proof import of the cyclic-Hom functoriality API and the new proved module `Sheaf.CategoryTheory.CyclicDerivedCanonicalRightBoundary`.

The new module transfers the existing arbitrary-resolution right-derived cyclic-Hom theorem to the canonical K-injective implementation. Unique unit-preserving comparison isomorphisms identify the two derived models. The underlying comparison commutes with shifts; endpoint naturality transfers the Frobenius action and normalized boundary. The native proof then composes exact open extension with canonical proper pushforward, using the already normalized native forgetting comparison. The degree-zero component comes from that same composite; its underlying generic proof uses naturality and the zero-shift axiom.

The proof uses the already proved private canonical-unit shift lemma through `import all Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`. The component proofs construct the three ordinary conjunction projections in the forward direction using `run_tac`; the kernel checks each full resulting declaration. This avoids the expensive backward elaboration of the same terms. Local irreducibility guards for `DerivedCategory`, `HasDerivedCategory.standard`, the derived functors and the unrestricted native functor keep intermediate interface comparisons small. These attributes are local to the proof file.

No existing module besides the assigned item was edited. No data, target, instance or public import was changed.

## Proved and sorry left

Closed the three original holes:

- `WeilConjectures.NativeExceptionalForgetful.counitHomTransport_action_compatible`.
- `WeilConjectures.NativeExceptionalForgetful.counitHomTransport_forget_compatible`.
- `WeilConjectures.NativeExceptionalForgetful.counitHomTransport_boundary_compatible`.

Added the proved supporting theorem `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedCanonicalRight_functorial` and proved private helpers. Holes closed: 3 of 3. Holes added: 0. No `sorry` remains in either delivered module. Existing imported theorem obligations remain with their original modules and nodes.

Final sandbox compilation succeeded: the canonical bridge in 10.2 seconds and the native item in 44.6 seconds. The final unused simp argument was then removed; delivery validates that cleanup and records the final checks.

## No longer needed

No existing public import was removed. No node or module is withdrawn. The proof uses the exact and right-derived component theorems of `CyclicDerivedHomExactSequence` directly instead of its `cyclicDerivedHom_finite_composite_functorial` wrapper, because that wrapper fixes a different implementation of right derivation. The wrapper remains needed elsewhere and is not pruned. No declared dependency module is claimed globally unnecessary.

All three component nodes retain the exact-open, normalized-proper and canonical-comparison dependencies used by the common proof.

## Where the brief, the DAG or earlier work was wrong

The planned direct specialization of finite-composite functoriality was not definitionally available: its proper factor uses `rightDerivedFunctorOfQuasiIsoResolutions`, whereas the actual native and ordinary compact-support functors use canonical `rightDerivedFunctor`. Unit normalization identifies the implementations but does not make them definitionally equal. The new fully proved comparison bridge repairs that gap, without moving the obligation to another hole.

The bridge uses only isomorphisms uniquely determined by the universal property. The middle boundary is also supplied by a uniqueness theorem. It makes no arbitrary data choice from a mere existence theorem. Its argument applies unchanged to the zero functor, trivial action and degree zero; boundary naturality uses isomorphisms at bounded endpoints, so no unproved boundedness preservation by arbitrary proper pushforward is assumed. Only the exact open extension's boundedness is used before taking the composite.

## New nodes

`lem-sf-cyclic-derived-canonical-right-boundary` records the proved implementation bridge, including its unit equation, fixed canonical shifts, action, degree-zero and boundary components. Its statement is general derived-functor compatibility, not a renamed native compact-support obligation. The three existing component nodes now record the actual proof routes. No change record is needed: existing statements and definitions were preserved.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 3 INFRA, 1 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.CategoryTheory.CyclicDerivedCanonicalRightBoundary": "7ea3e65facbbbc51bd37775732ea7897a1170ee8", "Sheaf.WeilSheaf.NativeExceptionalHomTransport": "4681ce6262955bbe4eb08e52d6da0185ca5c9071"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit": {"hash": "38d8da350553c21ab8acf4601f5ef60e14e4c474", "status": "INFRA"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitCarrier": {"hash": "fb6270c564098f04a50c5a335d01313dec994c64", "status": "INFRA"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitGraded": {"hash": "95f9b1a6e1c5a4b4db865352370f39808acd2d82", "status": "INFRA"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness": {"hash": "0e4c52d3e1311304c4ad0b61faf22e3ef3dbbb90", "status": "OK"}}, "seconds": 91, "time": "2026-10-28T11:27:14+0800", "transitive": 0, "version": 1}
```

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
