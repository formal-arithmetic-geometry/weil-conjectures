## What changed

Replaced the target theorem's proof hole by a real composition of three smaller interfaces. Added modules for top-exterior invertibility, construction of the determinant isomorphism, and extensionality on lifted wedges. The target now combines the three invertibility facts, existence, and uniqueness by `Iso.ext_inv` and the extensionality theorem.

## Proved and sorry left

The target declaration `determinant_shortExact` is reduced and compiles. Three strictly smaller named statements remain sorry: `exteriorSheaf_top_isInvertible`, `determinant_shortExact_exists`, and `exteriorTensor_lift_hom_ext`.

## No longer needed

The target proof no longer imports `Sheaf.AlgebraicGeometry.Modules.LocalSplittingFiniteFree` or `Sheaf.LinearAlgebra.ExteriorTopDirectSum` directly; those are imported by the existence interface. No stated node is pruned because the unit route's local splitting and top-direct-sum steps remain represented by that interface.

## Where the brief, the DAG or earlier work was wrong

The original module had no usable direct construction in the library: its stated plan describes local gluing but does not provide a single morphism that can be assembled in the target proof. The missing glue was split into existence and extensionality interfaces, each strictly below the target.

## New nodes

`lem-sc-exterior-sheaf-top-invertible`, `lem-sc-determinant-short-exact-exists`, and `lem-sc-exterior-tensor-lift-hom-ext` are added, with one module per node.

## Earlier second reading (a previous round; superseded)

I reread the target statement and all three added signatures. The target preserves every hypothesis and conclusion and uses the existence interface only for construction, the top-power interface only for the three invertibility conjuncts, and the lift-extensionality interface only for uniqueness. Each added statement is strictly smaller than the target and follows a separate local step of the blueprint route.

## Second reading by X2

1. I compared `DeterminantShortExact.lean` with the repository version. The target theorem signature is unchanged byte for byte; only its proof and proof-only imports changed. The three added modules are new declarations, and their signatures match their DAG nodes.

2. I compiled all four modules with `lcompile.py --all`; compilation succeeds with no errors. The target proof has no `sorry`; the three explicitly named split-off interface theorems retain their documented `sorry`s. No definitions contain `sorry`, and no forbidden declarations were added.

3. The split-off statements are strictly smaller than the target: top exterior invertibility, existence with the wedge formula, and extensionality from lifted wedges. They preserve the hypotheses and conclusions needed by the target and have corresponding DAG nodes and source/proof documentation. I checked rank-zero and empty-scheme edge cases at the statement level; no statement change is needed.

4. The target proof uses the existence and extensionality interfaces, while the existence interface retains the local-splitting and top-direct-sum imports required by the unit route. The target no longer directly imports those implementation modules, so the removed direct imports are recorded above; no unit step is bypassed.

5. DAG `proof`, `proof_deps`, and `proof_origin` for the target and all three new nodes agree with the Lean declarations and report. No existing declaration statement was weakened or strengthened.

I changed only this report section after the earlier reading: no Lean source or DAG content required repair.
