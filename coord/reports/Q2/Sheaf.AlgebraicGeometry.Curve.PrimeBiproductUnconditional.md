## What changed

Proved `AlgebraicGeometry.IsCurve.prime_biproduct_unconditional_iff` with its statement
unchanged. Added the proof-only import `Mathlib.Algebra.Category.Grp.Biproducts`.
Six proved private helpers construct product coordinates and test subsingletonness,
finiteness, surjectivity, injectivity and bijectivity for additive functors.
The main proof supplies cohomology pullback as a natural transformation and combines
the five predicate equivalences. Updated the existing node's proof, proof_deps and
proof_origin to follow this argument. No public declaration or definition changed.

## Proved and sorry left

Proved `AlgebraicGeometry.IsCurve.prime_biproduct_unconditional_iff`
(node `lem-pbc-f1-prime-biproduct-unconditional`): 1 of 1 original sorries closed.
Every private helper is proved. No sorry remains and none is added or split off.
The argument covers empty index types through the empty product and does not require
an affine or proper instance unless the corresponding predicate supplies it.

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
and `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
The original sole public import is retained and needed by the statement.
The proof does not use `lem-weil-pbc-cohomology-pullback-functorial` or its module
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`: the required naturality
is already proved as `Etale.cohomologyMap_map` in the publicly imported source API.
The proof also does not need `def-weil-pbc-etale-constructible-sheaf` as a proof
dependency, or the module `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
The supplied `Scheme.IsConstructibleSheaf` proofs discharge C5 directly; its
statement dependency remains unchanged. Both unused proof dependencies are removed
from this node's proof_deps. This does not claim they are unused by other targets.
No derived-global-sections bridge, constructibility closure theorem, or separate
`Ext.addEquivBiproduct` proof is needed. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original prose proposed deriving constructibility of H from the summands,
although the theorem already assumes it. It also named the larger pullback
functoriality node, although only its already-proved naturality component is used.
The revised proof uses exactly the declared Ext-based cohomology predicates and
needs no comparison with derived global sections. No statement is disputed.

## Second reading by Q2

1. Compared the sole delivered module with the repository version. The existing
   theorem signature is byte for byte unchanged; no definition or public import
   changed. The six added helpers are private proved theorems. PASS.
2. Compiled the delivered file with `lcompile.py`: no errors or warnings. Compiled
   a scratch copy with `#print axioms` for all six helpers and the main theorem:
   each uses only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`,
   forbidden declaration, or hollow definition occurs in the delivered file. PASS.
3. There are no split-off statements or new nodes. Read every helper's proof:
   the zero elements justify surjective evaluation; empty products are singletons;
   singleton families reduce to the corresponding component. Naturality and the
   inclusion/projection retract justify both map tests without extra hypotheses.
   Searched the source library and Mathlib for componentwise biproduct map tests,
   and Loogle for `"piMap"`: the generic product-map lemmas do not replace the
   coordinate identification or the reverse implications. PASS.
4. The proof goes directly through Mathlib's `Functor.mapBiproduct` and
   `AddCommGrpCat.biproductIsoPi`, with existing `Etale.cohomologyMap_map`.
   Checked C1, C2, C5, C7 and C8 against `Curve.Assertions`: properness,
   affineness, extension squares and open immersions are retained, and C5 uses
   precisely the supplied constructibility assumptions. Both unused old proof
   dependencies and their imports are listed above. The `sk-thm-p1` unit's
   `realized` route is retained: this closes a componentwise reduction below it.
   The retained public import supplies the statement API; the added plain import
   supplies the product identification used only in proofs. PASS.
5. Compared the existing node JSON with the repository version: only `proof`,
   `proof_deps`, and `proof_origin` changed. The three proof steps match the
   coordinate construction, natural-transformation map tests, and predicate
   assembly; `proof_deps` equals the union of their `uses`. Statement and
   statement dependencies are unchanged. No new node is needed. PASS.

Second reading changed only this report: corrected its inaccurate claim that no
imports were removed and recorded the independent checks. Lean and DAG needed
no repair.
