## What changed

Proved `CategoryTheory.ringExtension_finiteSupport_product` in
`Sheaf.Algebra.Homology.RingExtensionFiniteSupportProduct`, with its signature and
public imports unchanged. Added proof-only imports of
`Mathlib.CategoryTheory.Adjunction.Additive` and `Mathlib.Data.Int.Interval`.
All six helpers are private and fully implemented/proved; none is an instance or
an exported definition. Canonical scalar extension is constructed directly, rather
than chosen from an existence theorem. The proof does not use `F.map`.

Restricted the original fan to `Finset.Icc a b`, used preservation of finite products
by additive functors, restored the zero factors, and transported along `hF`.
The pure-tensor formula follows directly from `toSheafify_naturality` and the
definitional pure-tensor formula for `ModuleCat.extendScalars.map`.
Updated the existing node's proof, proof_deps, and proof_origin accordingly.

Searches: LeanFinder for additive functors preserving finite-support products returned
`Functor.preservesFiniteProductsOfAdditive`; Loogle for `TensorProduct.piRight` returned
the expected finite-product equivalence and its formulas; grep confirmed finite-product
preservation in `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
The relevant Mathlib signatures and the existing change-of-rings construction were read.

## Proved and sorry left

Closed the sole hole: `CategoryTheory.ringExtension_finiteSupport_product`
(node `lem-pc-ring-extension-finite-support-product`). Added zero holes and split off
zero statements. No `sorry` remains in any delivered Lean module.

The complete file compiles without warnings through `lcompile.py`.
`#print axioms CategoryTheory.ringExtension_finiteSupport_product` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
The proof handles an empty interval (`a > b`), singleton intervals, arbitrary zero
factors inside the interval, and zero rings without any additional hypotheses.

## No longer needed

Removed the proof edge to `lem-weil-pbc-tensor-finite-product` (Mathlib leaf
`TensorProduct.piLeft` / `Mathlib.LinearAlgebra.TensorProduct.Pi`). Neither that
comparison nor `TensorProduct.piRight` is needed by this proof; the categorical
finite-product preservation theorem replaces the explicit tensor calculation.
The lemma can still be needed by unrelated branches; this is pruning of this item's
proof dependency, not a claim that it is globally unreachable.

No pre-existing import was removed. A redundant direct import of
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` added during development was
removed after a clean compile; `Mathlib.CategoryTheory.Adjunction.Additive` already
makes the needed additive-functor API available.
Evaluation equivalences on the one-object site and invertibility of the sheafification
unit are also unnecessary: the proof works directly with sheaf module morphisms.

## Where the brief, the DAG or earlier work was wrong

The statement is valid unchanged. The DAG's evaluation-and-tensor-comparison route
was longer than necessary: additivity suffices to preserve the finite restricted
product. The private scalar-extension construction is the elementary underived
part of the existing `derivedChangeOfRings` proof, without importing or invoking
its derived existence result. The unit record has no realized statement or steps
for this node, so no unit route is bypassed. The existing declaration's docstring
is retained, and the revised DAG records the actual proof.

## Second reading by N4

1. **Interface: pass.** Compared the sole delivered module with the repository using
   `diff`; independently compared the existing theorem header byte for byte through
   `:= by`. Its signature, universes, visibility, public import, and original
   definitions are unchanged. The six added helpers are private. There are no
   interface change records or forced adaptations to review.
2. **Proof and axioms: pass.** Independently compiled the complete module with
   `lcompile.py` (5.8 seconds, no warnings). A scratch copy with `#print axioms
   CategoryTheory.ringExtension_finiteSupport_product` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned the delivered
   source for holes and prohibited declarations/options: none. Read all six helper
   bodies: the fans, lifts, scalar-extension objects, and morphisms are constructed
   directly; no data is chosen from an unproved existence theorem.
3. **New statements and edge cases: pass.** No public statement or split-off hole
   is added. Checked the private universal-property reductions in both directions,
   the directions of the transport isomorphisms, and the pure-tensor naturality
   equation. An empty interval still has the empty finite product, and every omitted
   factor is zero; singleton intervals and additional zero factors inside the
   interval need no special argument. Zero rings are allowed. The proof deliberately
   constructs projections independently of `F.map`, as the unchanged statement
   requires. Searched the library for alternative scalar-extension functors and
   Mathlib for product restriction/zero-factor lemmas, using different vocabulary
   (`finite.*(support|zero)|product.*IsZero` through `msearch.py`, plus direct `rg`).
   The existing underived construction inside `derivedChangeOfRings` agrees with
   these helpers; its derived existence theorem is neither needed nor used.
4. **Route and pruning: pass.** Read Mathlib's additive finite-product preservation
   instance and the upstream change-of-rings construction. The finite-product route
   is already shorter than the old tensor-Pi comparison. Independently compiled
   scratch variants deleting each new import: removing `Mathlib.Data.Int.Interval`
   loses `LocallyFiniteOrder ℤ`; removing `Mathlib.CategoryTheory.Adjunction.Additive`
   loses `Adjunction.left_adjoint_additive`. Thus both proof-only imports are needed.
   The existing public import supplies the statement's definitions. The old
   `proof_deps` has exactly one unused edge, `lem-weil-pbc-tensor-finite-product`,
   already listed under No longer needed; no original module import can be pruned.
   Read `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists
   are empty, and no realized unit node is bypassed. The retained original docstring
   describes the former tensor-Pi route; the report and revised DAG describe the
   actual additive route.
5. **DAG: pass.** Compared the node JSONs: only `proof`, `proof_deps`, and
   `proof_origin` changed. The union of the steps' `uses` equals `proof_deps`.
   `def-pc-perfect-rhom-base-change-map` supplies the object equalities and pure
   tensors; `def-pur-sheaf-tensor-product` supplies the concrete scalar-extension
   construction and naturality. The revised steps match the Lean proof. There are
   no new nodes to audit.

Second-reading changes: appended this independent review only. No Lean proof or
node repair was necessary. Confirmed one hole closed
(`CategoryTheory.ringExtension_finiteSupport_product`), zero holes added, and zero
statements split off.
