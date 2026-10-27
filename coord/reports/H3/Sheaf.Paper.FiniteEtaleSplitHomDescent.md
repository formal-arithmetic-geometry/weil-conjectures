## What changed

Prove the two outstanding declarations in `Sheaf.Paper.FiniteEtaleSplitHomDescent` without changing any public signature or definition. Construct actual splitting charts from finite-etale local splitting. Normalize module pullbacks to literal restrictions using `profinitePointModuleForgetPullbackIso` and the proved source-library localization comparison. Glue underlying abelian-sheaf morphisms with Mathlib's sheaf of morphisms, and descend the module action by joint faithfulness. Prove local surjectivity by descent of the zero cokernel. All additional helpers are private and fully proved; all new imports are proof-only.

Update the existence, local-surjectivity and main descent node proofs to match this argument. No other existing module is changed.

## Proved and sorry left

Closed:
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_exists` (`lem-sfb-finite-etale-split-hom-descent-existence`).
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_local_surjective` (`lem-sfb-finite-etale-split-hom-descent-local-surjective`).

Two original holes closed, zero holes added, zero split-off statements, zero holes remaining in the item. The complete module compiles through `lcompile.py` in 33.9 seconds, with profiling removed. The existing `finiteEtaleSplitHom_epi` and `finiteEtaleSplitHom_descent` proofs are preserved. Empty bases and degree-zero charts are included; no surjectivity of p is used.

## No longer needed

No original import was removed. The following planned proof dependencies are unused by this proof:

- `lem-weil-proetale-weakly-etale-localization` / `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: the adopted source-library restriction comparison directly computes the inverse image needed here.
- `lem-pur-sheaf-hom-cover-gluing` / `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`: Mathlib `Presheaf.IsSheaf.hom` glues the underlying maps, after which the module action descends locally.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence` / `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: no conversion to sectionwise modules is required. Its existing statement-dependency entries are retained unchanged.
- The old main-node reference `lem-sfb-internal-module-localization-hom`: no such node or declaration exists; the required comparison is proved privately from the published module-forgetful comparison and its composition law.

These are pruned from this proof route only; no source-library declaration is removed and no global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The main node's proof text still described an unsplit section-module argument and cited the absent `lem-sfb-internal-module-localization-hom`, while its proof-dependency list described the later existence/epi split. The updated main proof now simply combines those actual declarations. The local-surjectivity node's old final step cited a Hom-gluing theorem although cokernel descent suffices.

The local scalar-extension comparison is canonical: extension along the invertible condensed coefficient map is naturally restriction along its inverse. Consequently the underlying abelian inverse image and its existing localization API suffice for both outstanding obligations. No additional hypothesis, new axiom, unproved data choice, or change of unit route is needed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
