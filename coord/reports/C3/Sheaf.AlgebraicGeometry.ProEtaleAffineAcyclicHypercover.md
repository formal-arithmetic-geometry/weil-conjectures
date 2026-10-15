## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_hypercover` by combining a geometric finite-basis realization theorem with a fully proved componentwise lifting lemma. Added the proof-only imports `ProEtaleAffineAcyclicHypercoverGeometry` and `ProEtaleAffineAcyclicHypercoverWeak`.

## Proved and sorry left

Closed the target theorem. Added one decomposition sorry, `AlgebraicGeometry.Scheme.ProEt.exists_affine_hypercover_geometry`, in node `lem-weil-pbc-proetale-affine-acyclic-hypercover-geometry`; its proof is the finite-basis and disjoint-union geometric construction. The component lifting theorem `AlgebraicGeometry.Scheme.ProEt.weaklyContractible_of_components` is proved without sorry.

## No longer needed

No stated proof dependency was removed. The temporary construction and matching modules were withdrawn before delivery because the final proof does not import them.

## Where the brief, the DAG or earlier work was wrong

The DAG plan requires substantial categorical transport from formal coproduct hypercovers to the pro-etale slice. That transport cannot be discharged from the currently stated APIs in this session, so it is isolated as one strictly smaller geometric theorem. The finite-product lifting step is elementary and is proved directly.

## New nodes

`lem-weil-pbc-proetale-affine-acyclic-hypercover-geometry` records the geometric realization split. `lem-weil-pbc-proetale-affine-acyclic-hypercover-component-lifting` records the proved componentwise lifting lemma.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged. The component lifting proof is checked by naturality of sheaf morphisms and the bijective evaluation maps. The geometric theorem is a strictly smaller decomposition carrying the finite-basis and matching construction; it remains the sole sorry.

## Second reading by C3

1. **Signatures and accidental changes.** Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and proof bodies changed. The two added helper modules contain the newly split declaration and the componentwise proof.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The target proof is a genuine reduction through the geometric and component-lifting declarations. The component-lifting declaration has no `sorry`; the geometric construction is the one documented split-off `sorry`. No forbidden declarations or hollow definitions occur.

3. **Split statements.** Checked both split statements against the target reduction and searched the library for duplicates. The component-lifting statement is strictly the section-surjectivity part of the argument. The geometric statement supplies the construction and matching data while omitting the assembled weak-contractibility clause. The geometry node's circular target dependency was removed, and its proof dependencies now match its stated construction.

4. **Pruning and route.** The target now records the two helper nodes as its proof dependencies and follows the unit route through finite-basis construction, coproduct realization, and component lifting. The original geometry imports are replaced by proof-only imports of the two helper modules; no unused delivered import remains.

5. **DAG agreement.** Updated the target node's `proof`, `proof_deps`, and `proof_origin` to match the Lean proof, and corrected both helper node proof descriptions. The unit realization remains unchanged.

Changed during second reading: repaired DAG proof metadata and removed the circular statement dependency; corrected the component node's proof description.
