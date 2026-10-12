## What changed

Proved `AlgebraicGeometry.picZero_torsion_base_change` from a new Jacobian point comparison theorem. Added the proof-only import and the new module `Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison`.

## Proved and sorry left

Closed one upper hole and added one strictly intermediate hole: this is a decomposition, with net zero holes removed. The target theorem `picZero_torsion_base_change` has a complete proof. The new theorem `pic_zero_jacobian_point_comparison` remains `sorry`; it is a strict intermediate comparison statement and has node `lem-sc-piczero-jacobian-point-comparison`.

## No longer needed

Removed direct imports (their geometric work is deferred to the comparison bridge):

- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`
- `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible`
- `Sheaf.AlgebraicGeometry.BaseChangeCurve`
- `Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne`
- `WeilConjectures.AlgebraicGeometry.Curve`
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
- `WeilConjectures.AlgebraicGeometry.Regular`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`

The geometric route remains in the bridge, including the relative-dimension-one lemma restored during second reading. No module is claimed globally pruned. The unnecessary public import of `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` was also removed from the bridge; the main proof obtains kernel operations through its abelian-variety estimate import. The compiled main proof only uses the comparison, abelian-variety estimate, and residue-field injectivity.

The old target node's proof dependencies no longer directly used by the target proof are:
`thm-sc-jacobian-representability`, `lem-sc-base-change-curve`, `lem-sc-smooth-regular`,
`lem-weil-separably-closed-geometrically-connected`, `sbc-lem-smooth-geometrically-reduced`,
`lem-sc-curve-base-change-relative-dimension-one`, `lem-sc-jacobian-base-change-compatible`,
and `def-sc-pic0`. The geometric lemmas are now dependencies of the comparison bridge;
`def-sc-pic0` remains a statement dependency and its definitions remain publicly available.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof omitted a formal intermediate theorem expressing the multiplicative Jacobian comparison square. This delivery states that missing bridge explicitly.

## New nodes

`lem-sc-piczero-jacobian-point-comparison` records the Jacobian/Picard comparison needed by the compiled target proof. Its Lean module is `Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison`.


## Second reading by D2

1. **Unchanged interface — pass.** Diffed the delivered target against the repository;
   its complete declaration signature is byte-for-byte unchanged. Its only changes are
   proof code and proof-only imports. There are no changed existing definitions or
   statements, and no change records are required. Compared the existing node field by
   field: only `proof`, `proof_deps`, and `proof_origin` differ.
2. **Kernel-checked reduction — pass with the reported hole.** Both modules compile
   locally with `lcompile.py --all`. The only delivered `sorry` is the named theorem
   `AlgebraicGeometry.pic_zero_jacobian_point_comparison`; there is no new definition,
   arbitrary witness chosen to define data, forbidden declaration, or anonymous hole.
   Scratch `#print axioms` probes for both declarations show exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. In the target, `hn` excludes n=0 and
   divisibility by the characteristic; the kernel universal property lifts torsion and
   the comparison square identifies its image. Injectivity uses the injective field
   embedding and `Scheme.SpecMap_comp_injective`.
3. **Split statement — pass, not closed.** Matched all hypotheses of the new node to Lean:
   algebraically closed fields and their algebra map, a smooth proper connected curve,
   subgroup models whose sets equal `picZero`, and the specified pullback homomorphism.
   Its conclusion is a commutative abelian variety with multiplicative point equivalences
   and a naturality square. It contains no n, injectivity assertion, or torsion lifting
   assertion, so it is the geometric part of the argument rather than a renamed target.
   Over the identity field extension the square is the identity comparison; for genus
   zero both degree-zero Picard groups and the Jacobian point groups are trivial.
   Smooth connected curves here are nonempty and dimension exactly one, excluding the
   empty scheme and Spec k. Read its source/proof docstring and matched its node.
   Independent leanfinder search for tensor-compatible natural point equivalences found
   only commutative-ring Picard results; loogle found general `RepresentableBy.homEquiv`
   naturality, not this geometric comparison; msearch grep found no Mathlib counterpart.
   Repository searches and reading `exists_jacobian`,
   `exists_picardZero_equiv_picardFunctorDegree_zero`,
   `exists_mulEquiv_of_isPicardZeroMul`, and `jacobian_compatibility` confirm these are
   ingredients, not a duplicate of the bridge. Completing the geometric assembly is
   beyond a short repair; the complete sourced proof remains documented.
4. **Route and pruning — pass after repair.** The proof retains the original Jacobian
   comparison and abelian-variety torsion route. Read
   `dag/units/sk-prop-ext-invariance.json`: its realized statement and three step entries
   are empty; this delivery changes no unit realization and bypasses no assigned node.
   The bridge keeps the geometric dependencies of the old route. Restored the missing
   proof-only relative-dimension-one import, and removed the bridge's unnecessary public
   GroupScheme.Defs import. The No longer needed section now lists every old target
   proof dependency removed from its immediate proof, without claiming global pruning.
5. **DAG agreement — pass after repair.** The target node's steps match the Lean comparison,
   residue-field injectivity, and finite-etale kernel lifting. The new node has its source,
   self-contained statement, statement dependencies, searches, split status, origin,
   creation/blueprint records and verbatim Lean signature in its own new module.
   Added `lem-sc-curve-base-change-relative-dimension-one` to its first proof step and
   proof_deps, spelling out that geometric integrality and the curve hypotheses first
   give the variety-of-dimension-one interface required by that lemma, then applying it
   to the identity base change. The node's dependency union agrees with its proof steps.

Second reading changed only the bridge's imports, its missing dimension dependency and
explanation, and this report. Holes closed: `AlgebraicGeometry.picZero_torsion_base_change`.
Holes added/left: `AlgebraicGeometry.pic_zero_jacobian_point_comparison`
(node `lem-sc-piczero-jacobian-point-comparison`). This is one decomposition, net zero;
no fully axiom-free theorem or global module pruning is claimed.
