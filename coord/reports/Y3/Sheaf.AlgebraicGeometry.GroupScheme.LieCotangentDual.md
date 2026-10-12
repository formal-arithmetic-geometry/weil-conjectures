## What changed

The target theorem is reduced to the existing rational tangent–cotangent duality, a proved residue-field rationality lemma, a scalar-transport equivalence, and a new Lie-to-tangent bridge. The bridge remains a named theorem with a documented `sorry`; the target theorem itself compiles from these strict intermediate statements.

## Proved and sorry left

Proved `exists_lie_identity_cotangent_dual_equiv` and `identity_residue_rational` (including bijectivity and the identity-section factorization), and proved the private scalar transport equivalence. Closed one original hole: `exists_lie_identity_cotangent_dual_equiv`. Added one hole: `exists_lie_identity_tangent_linearEquiv` (node `lem-ag-lie-identity-tangent-equiv`). This is a decomposition, with zero net holes closed; the added residue theorem `identity_residue_rational` is fully proved. The target also depends on the already open rational tangent-cotangent theorem.

## No longer needed

Removed the original direct imports of `Sheaf.AlgebraicGeometry.SchemeTangentSpace` and `Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality` from the target module: the former is reached through `LieIdentityTangentEquiv`, and the latter is replaced by the more directly usable `RationalPointTangentDerivationIdentification`. The old proof dependency `lem-sc-rational-tangent-cotangent-duality` is no longer used directly; its role is supplied by `lem-sc-rational-point-tangent-derivation-identification`. The other old dependencies remain through the intermediate declarations. Removed the unused `Mathlib.RingTheory.Ideal.Cotangent` import from the residue module. No unit route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The direct geometric proof of the Lie–tangent bridge is substantial and is not available as a single existing declaration. It was split off as a strictly smaller statement. The residue-field step also needs the factorization through `fromSpecResidueField`, which was made explicit in the new intermediate theorem.

## New nodes

`lem-ag-lie-identity-residue-rational` records the proved residue-field rationality and identity-section factorization.

`lem-ag-lie-identity-tangent-equiv` records the remaining Lie/tangent identification theorem.

## Earlier second reading (a previous round; superseded)

The target theorem compiles and its statement is unchanged. The residue-field theorem is strictly smaller and proved from the identity-section equation. The Lie/tangent theorem is strictly smaller than the target and is the only remaining `sorry`; it is the next proof item.

## Second reading by Y3

1. **Comparison.** Compared the delivered target module with the repository copy. The target declaration signature is byte-for-byte unchanged; the two added modules are new split-off declarations. Verdict: pass.

2. **Compilation and trust.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is `exists_lie_identity_tangent_linearEquiv`, and it is named with node `lem-ag-lie-identity-tangent-equiv`. A scratch-copy `#print axioms` check gives only `propext`, `Classical.choice`, and `Quot.sound` for the residue theorem, and those plus `sorryAx` for the target and the bridge. No forbidden declarations or hollow definitions occur. Verdict: pass, with that documented split hole.

3. **Statements.** Checked the residue rationality and Lie-to-tangent statements against the target reduction and their docstrings. They are strictly smaller intermediate claims, and the residue theorem is proved by the section and stalk-map identities. Additional LeanFinder, Loogle, and Mathlib grep searches, and `rg` in both library roots, found no existing full bridge; the existing infinitesimal-point equivalences supply part of its construction. The trivial group, zero cotangent space, and nonsmooth group schemes require no extra assumptions. Verdict: pass.

4. **Pruning and route.** The proof uses the rational tangent-cotangent theorem, the residue theorem, and the Lie-to-tangent bridge. The direct `SchemeTangentSpace` import is no longer needed in the target module because the bridge imports it. Removed the unused cotangent import from the residue module. The unit route is retained through tangent and cotangent duality.

5. **DAG.** Updated the target node proof and proof dependencies to match the actual composition, and corrected both split-node proof descriptions and dependencies. Verdict: pass.

Changed the residue module import and blueprint tag, and corrected the three DAG proof records. No Lean statement was changed.
