## What changed

Proved `CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_flat_affine`
in `Sheaf.AlgebraicGeometry.AffineFlatDescent`, with its signature unchanged.
Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections`
for the proved pushout-to-tensor equivalence and its formula on pure tensors.

The proof evaluates transport on `V ×_S X` to construct a coaction on global
sections. Transport naturality, the identity law and the cocycle prove its
counit and coassociativity. The existing, proved `Algebra.DescentDatum.descendedEquiv`
then constructs the invariant algebra and the required tensor isomorphism.
Applying spectrum and pasting affine identifications produces the pullback square;
invariance of its generators gives transport compatibility for arbitrary test schemes.
The tensor calculations adapt the proved source-library `exists_affine_descent`
in `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Descent`.
This latter module is not imported.

Updated the existing node's proof steps, dependency assignments and proof origin
so they record the direct transport construction. The unit has no realized nodes
in this part of the argument; no unit statement or step was bypassed.

## Proved and sorry left

Proved `CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_flat_affine`
(node `lem-galois-affine-flat-descent-effective`): 1 of 1 original sorries removed.
No sorry remains in the module and no new theorem, module or sorry is introduced.
Single-file compilation succeeds. A scratch copy with `#print axioms` shows
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Holes closed: `CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_flat_affine`.
Holes added: none; net reduction: one, with no decomposition.

## No longer needed

None: no existing import, node or module is pruned. The existing proof dependencies
are all retained. The proof uses global sections directly instead of introducing
chosen ring presentations and a classical descent isomorphism. The diagonal counit
comes directly from `transport_self`, so the original plan's invertible-idempotent
calculation is unnecessary; it did not have a separate node or module.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The transport formulation already includes
the diagonal identity, so the counit argument is shorter than the old DAG plan.
Surjectivity is not used, as the existing docstring predicts; its binder and the
statement are retained unchanged. The surjectivity hypothesis is registered as a local instance; the argument
requires only flatness. No linter is disabled.


## Second reading by Y2

1. **Unchanged interface: PASS.** Compared the complete delivered module against
   the repository with `diff`. The existing theorem signature is byte for byte
   unchanged, including `hf`, `hs`, and `D.IsEffective`; its docstring and all
   definitions are unchanged. The only import addition is plain, proof-only
   `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections`.
   No statement change or change record is needed.
2. **Proof and axioms: PASS.** Locally compiled the delivered file without errors
   or warnings (10.3 seconds). Compiled a separate scratch copy with `#print axioms`
   for the theorem: exactly `propext`, `Classical.choice`, and `Quot.sound`.
   Searched the delivered Lean for forbidden declarations, options and `sorry`:
   none. Read the universal transport construction, diagonal identity, cocycle,
   tensor inductions, descended algebra, pasted pullback, and final invariance
   argument. The last argument applies to arbitrary test schemes, as required
   by the unchanged definition of `IsEffective`.
3. **Split statements: PASS (none).** There are no new declarations, nodes or
   residual holes to audit. The existing algebra descent theorem is used directly;
   no renaming of the item's hole or unproved intermediate is introduced.
4. **Shortest route and pruning: PASS.** Searched `lean/Sheaf` and the upstream
   descent modules for effectivity and affine descent, and ran a distinct Loogle
   query `"DescentDatum", "effective"` (zero hits). The upstream
   `exists_affine_descent` is specialized to an etale topological invariance
   construction, rather than arbitrary transport data, so it cannot directly
   replace this argument. The proof uses its existing tensor infrastructure via
   the small GlobalSections module instead of importing that larger construction.
   Each import supports the signature or proof. Every old proof dependency is
   still used; `## No longer needed` is complete. Read `dag/units/sk-prop-h2.json`:
   its realized statement and step lists are empty and remain untouched; no unit
   step is bypassed.
5. **DAG agreement: PASS.** Compared both node files: only `proof` and
   `proof_origin` differ. The union of the new proof steps' `uses` equals
   `proof_deps`, which is unchanged. The five steps accurately describe the
   actual Lean argument, including the shorter diagonal counit and the final
   transport compatibility. Source, statement, Lean signature and unit stay fixed.

Second reading changed the report only: recorded the independent checks and the
explicit hole accounting. No repair of Lean or DAG was necessary.
