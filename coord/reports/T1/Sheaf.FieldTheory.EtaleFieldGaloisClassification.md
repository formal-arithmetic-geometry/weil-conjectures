## What changed

Proved `FieldTheory.finite_separable_extension_galois_classification` in
`lean/Sheaf/FieldTheory/EtaleFieldGaloisClassification.lean`, with its signature unchanged.
Three private, fully proved helpers implement transitivity of embeddings, the stabilizer
identity, and equivariant equivalence of transitive actions with equal stabilizers.

The proof follows the existing three-step plan. `IsSepClosed.lift` gives an embedding and
Mathlib's `AlgHom.fintype` gives finiteness. `AlgEquiv.liftNormal` extends the isomorphism
between the two embedding images to an automorphism: it packages the extension and
bijectivity steps in the plan. Stabilizers are fixing subgroups, open by
`IntermediateField.fixingSubgroup_isOpen`. The existing proved
`openSubgroup_fixedField_finite_separable` supplies the fixed field of the stabilizer,
its finiteness, separability, and fixing subgroup identity. A quotient-of-stabilizer
construction gives the required equivariant equivalence. Finally, the fixed-field
identity forces the image of an equivariant map into the chosen embedding's range;
restriction followed by the inverse range equivalence constructs the field map.
Transitivity proves equality on all embeddings, and injectivity of the chosen embedding
proves uniqueness.

The public declaration signature remains unchanged. The second reader replaced the
public infinite-Galois import with public KrullTopology plus a plain proof import,
and removed redundant direct SeparableClosure and Topology.Algebra.Group.Basic imports.
IsSepClosed stays public because it defines IsSepClosure. No new module or node is needed.
The existing node now records the actual three-step proof and its dependencies.
The import change record is
`coord/changes/etale-field-galois-classification-imports.md`.

## Proved and sorry left

Closed the sole hole, `FieldTheory.finite_separable_extension_galois_classification`
(node `lem-exc-etale-field-galois-classification`). Added zero holes. There are no
`sorry` declarations in the delivered module. The three private helpers are fully proved.
This is a proof, not a decomposition; no intermediate theorem with `sorry` was added.

## No longer needed

Removed direct imports `Mathlib.FieldTheory.SeparableClosure` and
`Mathlib.Topology.Algebra.Group.Basic`; both remain available transitively from the
statement imports. `Mathlib.FieldTheory.Galois.Infinite` is now a plain proof import,
with `Mathlib.FieldTheory.KrullTopology` the public signature import.

Removed from the item's `proof_deps`:
`lem-exc-etale-embedding-extension-sepclosed` and
`lem-exc-etale-algebraic-endomorphism-bijective`.
The proof directly uses `IsSepClosed.lift` and `AlgEquiv.liftNormal` instead of
applying those leaves separately. The remaining three dependency nodes match
exactly the cited Mathlib openness/fixed-field declarations and the proved
open-subgroup theorem. No Sheaf or WeilConjectures module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The plan's basis-and-roots proof of finiteness is
already Mathlib's `AlgHom.fintype`; the extension and invertibility argument is already
`AlgEquiv.liftNormal`. The proof uses the first clause of the open-subgroup theorem;
its otherwise unused converse universe is specified explicitly to avoid an unresolved
universe metavariable. The unit `sk-prop-h2` has no realized entry for this node and
its route is unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the complete delivered module with the repository using `diff`.
   The existing declaration's signature and docstring are byte for byte unchanged.
   The only new declarations are three private proved helpers. No public data
   construction or target meaning changes. Public imports were repaired as described
   in the change record; both direct importers, EtaleFieldPointFunctor and EtaleFieldPointFunctorEssSurj, use plain proof imports and compile against the delivered module without adaptation.
2. Compiled the module locally with `lcompile.py`; no errors or warnings.
   A scratch copy with `#print axioms` for the theorem and each private helper reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no `sorry`, axiom, unsafe/opaque declaration, extern, or implemented_by.
   The fixed field is the actual `IntermediateField.fixedField H` construction;
   the algebra map uses a codomain restriction and the inverse of a proved range
   equivalence. No arbitrary data is chosen from an unproved existence theorem.
3. No statements were split off and no holes were added. Checked the three private
   helpers: normality extends the image isomorphism; fixing the image is equivalent
   to fixing its embedding; equal point stabilizers give bijective orbit maps from
   G/H. The pointed pretransitive hypotheses exclude empty actions. For trivial G
   both pointed actions are singletons; for regular actions H is trivial; for L=K
   there is one embedding. Searches in both library roots and Mathlib under
   orbit/stabilizer/quotient terminology found the orbit-stabilizer components used
   here, with no missing proof needed.
4. Read the proof from the three conclusion clauses downward. Existing Mathlib
   lifting and finiteness results give the short field-theory route; the explicit
   quotient argument establishes essential surjectivity; the fixed-field identity
   followed by restriction establishes full faithfulness. Kept the correct proof.
   Pruned redundant imports and the two replaced Mathlib dependency leaves.
   Read `dag/units/sk-prop-h2.json`: its realized statement and step lists are empty,
   and this item does not replace any realized unit step or chapter route.
5. Read the item's node and all five old dependency nodes. Repaired `proof`,
   `proof_deps`, and `proof_origin` to describe the actual Mathlib lifting route,
   quotient helper, and range factorization. The three retained dependencies match
   their declarations; the unchanged mathematical statement and source are retained.

Changed during second reading: import cleanup, existing-node proof-route correction,
complete pruning report, and the import change record. No proof body needed repair.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The theorem statement,
docstring, and all existing declaration signatures are unchanged byte for byte. The
only additions are three private proved helpers; the import change is recorded above.
Verdict: pass.

2. Compiled the module and the axiom scratch copy with `lcompile.py`. There are no
errors, warnings, `sorry`, forbidden declarations, or hollow definitions. Every
checked declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
Verdict: pass.

3. Checked the proof route and edge cases (trivial Galois group, L = K, and finite
Galois extensions). The helpers prove transitivity, stabilizer equality, and the
quotient orbit equivalence directly; no split-off statements or nodes were added,
and no existing library theorem duplicates them. Verdict: pass.

4. Read the proof downward from the target. `IsSepClosed.lift`, `AlgHom.fintype`,
`AlgEquiv.liftNormal`, the fixing-subgroup openness theorem, and the fixed-field
theorem give the shortest available route. The unit route is preserved. Redundant
public imports and two superseded proof dependencies are pruned as documented.
Verdict: pass.

5. Checked the item node against the Lean proof: its three proof steps, retained
dependencies, and proof origin describe the actual lifting, fixed-field, quotient,
and range-factorization arguments. No statement change or new node is needed.
Verdict: pass.

Changed: no proof body changes; retained the import cleanup, corrected DAG proof
metadata, and documented the complete pruning and axiom checks above.


## Second reading by T1

1. Compared the delivered module with the current repository using `diff` and a
byte-for-byte signature assertion. The existing theorem signature and docstring
are unchanged. The only new declarations are three private proved helpers.
The public import cleanup has its change record. The current direct importers,
`Sheaf.AlgebraicGeometry.EtaleFieldPointFunctor` (P2) and
`Sheaf.AlgebraicGeometry.EtaleFieldPointFunctorEssSurj` (E2), compile unchanged
against the delivered module in a scratch overlay. Verdict: pass.

2. Compiled the delivered module with `lcompile.py` without errors or warnings.
Compiled a scratch copy printing axioms for the public theorem and all three
private helpers: each uses only `propext`, `Classical.choice`, and `Quot.sound`.
Scanned every delivered Lean file for forbidden declarations and `sorry`: none.
The fixed field is explicitly `IntermediateField.fixedField H`; the field map
is a codomain restriction followed by the inverse range equivalence. No hollow
construction or data selected from an unproved existence statement. Verdict: pass.

3. No statements were split off and no holes were added. Read all three helper
proofs, including the left-coset relation orientation, quotient injectivity,
surjectivity, and equivariance. Pointed pretransitive actions are nonempty;
for trivial G they are singletons, and the regular-action case has trivial
stabilizer. For L = K the embedding action is a singleton. Independent Loogle
and LeanFinder searches under point-stabilizer/equivariant-action terminology,
and `rg` in Mathlib and both library roots, found the orbit-stabilizer components
already used here; no exact replacement for the helper was found. Verdict: pass.

4. Read downward from all three conclusion clauses. Nonemptiness and finiteness
use existing Mathlib results; `AlgEquiv.liftNormal` packages the automorphism
extension. The fixed-field theorem, quotient equivalence, and range restriction
prove the converse and full faithfulness. Retained the correct proof bodies.
The two removed proof dependencies and redundant direct imports are completely
listed in `No longer needed`; no project module is pruned. Read the unit record
`sk-prop-h2`: its realized statement and step lists are empty, and the item
preserves its route. Verdict: pass.

5. Compared node JSON with the repository: only `proof`, `proof_deps`, and
`proof_origin` changed. Read all five former dependency records and checked the
three retained ones against their Mathlib declarations or the proved
`openSubgroup_fixedField_finite_separable`. The node describes precisely the
lifting, openness, fixed-field, quotient, and range-factorization proof; its
statement and Lean record are unchanged. No new nodes required. Verdict: pass.

Changed in this reading: corrected the stale direct-importer name in the report
and import change record to EtaleFieldPointFunctor, verified both current
importers, and appended this independent review. No Lean proof repair needed.
