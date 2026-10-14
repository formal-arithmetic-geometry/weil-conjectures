## What changed

Updated the proof of `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` with an explicit type annotation on the local subfunctor `G`. The direct continuous-function sheaf, equivariance subfunctor, natural isomorphism, and forgetful-functor reflection proof remains intact and compiles.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` is proved. No `sorry` remains in the delivered module, and no new holes were added.

## No longer needed

None. The existing proof dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The checked-out library already contained a completed proof of this item from an earlier landing, despite the brief describing it as containing `sorry`. This delivery preserves that proof and only makes the local subfunctor type explicit.

## Second reading by F2

1. **Comparison.** Compared the delivered module with the repository version. The theorem signature, imports, definitions, and all existing declarations are byte-for-byte unchanged; the only difference is an explicit local type annotation for `G : Subfunctor (functionPresheaf c N.V)`.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no errors and no `sorry`. A probe with `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. No forbidden declarations occur.
3. **Split-off statements.** No statements were split off and no new holes were introduced. The existing DAG node statement is unchanged and is exactly the theorem proved by the module.
4. **Pruning and route.** The proof uses the direct continuous-function sheaf, equivariance subfunctor, natural isomorphism, and forgetful-functor reflection route recorded by the node. The sole public import remains needed; no imports or proof dependencies can be removed. The unit route is unaffected.
5. **DAG agreement.** The node's proof steps and proof dependencies agree with the implementation, and the retained restricted-scalars signature agrees with the landed duplicate-removal change record.

The second reading changed only the local type annotation for `G` and this report. The repository already contained the completed proof, so this delivery closes no additional hole; it preserves the previously proved target.
