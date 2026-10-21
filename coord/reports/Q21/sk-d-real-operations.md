# Worker report: sk-d-real-operations

## Files written

- dag/nodes/sec-purity-real-sheaves/sk-d-real-operations.json: definition, split; no complete Mathlib match. All formulas of the imported statement are retained; only explicit references to the existing notions were inserted.
- dag/units/sk-d-real-operations.json: only realized and realized_by filled. The unit has no proof steps.
- citations.json: verbatim statements for every cited node in every proof step.
- report.md: this report.

There are zero new nodes and zero new Mathlib leaves. No Lean was written and no compiler, Lake or build tool was run. All writes are in the assigned sandbox.

## Attachments

No complete attachment. I searched lean/WeilConjectures by the blueprint id, the operation terminology and the named declarations. Basic.lean:321 and :336 contain AlgebraicGeometry.WeilGroup.constLine and .tateLine with real bodies, but these only supply the final two definitions. Mathlib.RepresentationTheory.Irreducible supplies Representation.IsIrreducible, and the project's Mathlib/RepresentationTheory/Irreducible.lean:59 supplies Representation.IsConstituent. LinearAlgebra.lean:205 and :217 supply detLine and semisimplification. None of these project declarations states all clauses, and documentation listing other operations is not a theorem asserting the full package. Thus the partial Lean coverage is not an ATTACH claim. The algebraic sum, tensor, dual, invariant and coinvariant definitions are in Mathlib, which is not a project attachment.

## WANTED

None. The source of this definition is the available current blueprint, not an unavailable external theorem. Its additional verification is explicitly agent-written. No SGA source is used.

## What was wrong or incomplete

The imported definition had only sk-d-real-weil as a statement dependency, despite using the already existing notions of ordinary representation operations, composition series and semisimplification. I added sk-d-linear, def-mg-weil-composition-series and def-mg-weil-semisimplification; I did not cite def-real-weil-representation-operations because that node depends on this item. I retained the main-20261015 formulation of constituent as an irreducible subquotient, rather than reverting to the master unit's older formulation in terms of a chosen composition series. The two formulations agree by the written argument. The unit's statement and route were not rewritten.

There is no statement dispute: no hypothesis, defining formula or conclusion was altered. The inserted references do not change meaning. The finite-dimensionality qualification on composition factors remains exactly where the current source places it. The sketch does not assert that invariants or coinvariants under an arbitrary subgroup carry a whole-Weil-group action; such an assertion would require normality. The proof explicitly avoids adding it.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for coinvariants, constant Weil, composition series, semisimplification and Tate line found existing partial coverage: def-real-weil-representation-operations, def-wf-constant-weil-twist, def-mg-weil-composition-series and def-mg-weil-semisimplification. The first omits constant and Tate lines and depends on this item; the second defines the sheaf twist rather than the entire representation-operations package. No blueprint node found states the complete item in another form, so same_as is empty. I reused the existing generic definitions and the existence and Jordan–Hölder theorems instead of creating nodes for clauses of this item.

## Mathlib searches

All six searches in mathlib_searches were actually run with the prescribed msearch.py and their results read; searches.jsonl is retained. Both semantic phrasings returned only partial algebraic results, finite-group character results or root-system results. Loogle gave the exact individual dual and coinvariant definitions. I read Mathlib RepresentationTheory/Basic.lean:589-642 and :678-689, Invariants.lean:76-84 and Coinvariants.lean:54-58. They agree with these algebraic formulas but do not also provide the Weil degree character and complete constituent package. Therefore the complete item is not a Mathlib leaf. These elementary operations remain explicit definitions in the item and in sk-d-linear; no redundant node is created.

## Review by Q21

I read the current source literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-operations/_section.md in full, compared the older master source and the chapter and unit records, and checked delivery-errors B–E against the resulting files. The main snapshot explicitly defines constituents by irreducible subquotients and then asserts the finite-dimensional composition-series interpretation. The proof carries that assertion rather than moving it to a new node. All four steps have fewer than 2000 characters.

For step 1 I opened sk-d-linear and sk-d-real-weil. The former actually states the componentwise sum, diagonal tensor, induced exterior action, top exterior determinant and simplicity condition; the latter supplies the Weil group and coefficient-vector-space setting. The dual action is verified directly by the displayed inverse-order calculation, not taken from a definition that does not assert it. This is an elementary verification of the defined operation.

For step 2 I opened all four cited statements. lem-mg-composition-series-exists asserts existence for nonzero finite-dimensional Weil representations; I apply it only to the nonzero cases of V, N and V/M, all finite-dimensional subspaces or quotients with the induced group action. The zero cases use the empty chain directly. def-mg-weil-composition-series actually specifies a finite strict invariant filtration with nonzero simple quotients. I construct such a series containing N⊂M and give the equivariant quotient map, its surjectivity and kernel explicitly. lem-mg-jordan-holder actually gives matching factors with multiplicity for any two series of V. That is exactly what is required to compare the constructed series with an arbitrary chosen one. def-mg-weil-semisimplification actually defines the direct sum of the successive quotients; the factorwise maps and permutation give the sum isomorphism. None of these uses the proof of a cited node or treats a definition as an existence theorem. The existence and Jordan–Hölder citations are generic algebra tools from another unit, declared in split_report.tool_uses with their reasons.

Step 3 uses no black box: closure of the fixed-vector set follows from linearity, and the quotient means quotient by the explicitly specified linear span. This checks the definitions rather than invoking exactness or any invariant/coinvariant comparison. I checked that no subgroup normality or exactness claim is slipped in.

For step 4 I reopened sk-d-real-weil: its exact sequence gives the degree homomorphism and geometric kernel. sk-d-linear supplies the characteristic-zero coefficient convention. The actual action is the explicit one-dimensional space with multiplication by b to an integer exponent, not an unspecified chosen representation. The homomorphism calculation uses additivity of degree. Nonzero b permits negative powers; nonzero q permits every integer Tate twist. The kernel action is trivial, so the geometric continuity condition is met. The Tate exponent agrees with geometric Frobenius of degree one, not arithmetic Frobenius.

Small cases checked: V=0 (not irreducible, no constituents, empty semisimplification), rank one (one factor), two equal simple summands (multiplicity two retained), a nonsplit two-dimensional unipotent representation of the infinite cyclic group (two trivial factors, not asserted isomorphic to its semisimplification), N=0 and M=V, I={1} (both vector spaces V), I the whole group, b=1, n=0, and negative n. Exterior degree zero and degrees larger than dim V retain the usual exterior construction, and det(0) is the zeroth exterior line. There is no finite-group, semisimplicity or normality hypothesis introduced.

I also traversed the current dependency lists of the reused composition definitions and theorems and checked that none leads back to the item; def-real-weil-representation-operations would be unsuitable as an item dependency. citations.json quotes the actual current statements verbatim. No new statement needs independent source or small-case review. No unsupported Stacks tag or SGA source is cited. The remaining validation is the required server dry run followed by direct delivery.

## Unfinished work

None in the stage-1 split. The maintainer performs the independent review after delivery.
