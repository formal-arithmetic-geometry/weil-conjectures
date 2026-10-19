## Worker report

This module states the finite-coefficient projective-bundle formula and equality of its canonical component maps under base change. All data definitions have real bodies; only `projectiveBundleFormula` has a postponed proof, whose docstring contains the eight-step DAG proof.

Theorem-to-node correspondence:

- The datum `P : PurityFiniteSetting` fixes the prime characteristic, finite field, algebraic closure, coefficient prime different from the characteristic, finite coefficient extension, and positive level. `P.Coefficient` is precisely the standard size lift of O_E/(varpi_E^r). The annihilator `P.diagonalExponent` is ell^r; its existing annihilation theorem works at every positive level, without a ramification-divisibility hypothesis.
- `B`, `b`, and the instances `IsSeparated b`, `LocallyOfFiniteType b`, `QuasiCompact b` give the separated finite-type k-scheme. `n : Nat` includes zero. `F : B.Modules` and `hF : projectiveBundleRank B n F` give constant rank n+1 by the dependency's existing locally-free predicate.
- `G : ProjectiveBundleTautologicalSystem n` is the dependency's normalized presentation of the canonical geometry, not an arbitrary scheme or line bundle. Its bundle is relative Proj of the actual symmetric graded algebra; its line is the glued degree-one twist, and its comparisons are normalized on the quotient generators. The theorem applies to every such presentation. The dependency's `exists_projectiveBundleTautologicalGeometry` supplies one for each input, with a coherent system. `G.invertible` supplies the line-bundle witness.
- `t : OrdinaryFiniteTwistTransport` is the existing root- and pure-tensor-normalized comparison interface. It is not a freely chosen map. The theorem works for every normalized realization; its existence is the finite-twist pullback theorem.
- `projectiveBundleChern` is `Etale.kummerFirstChern` of `Scheme.Pic.ofIsInvertible D.L`. Comparison inverse image gives exactly the pro-etale Kummer class in the recorded dependency. `projectiveBundleCupPower` starts at the identity and tensors recursively with this same class, giving the ordered model `P.diagonalTwistEtale T a` of A(a)[2a].
- `projectiveBundleSummandEtale` is RHom(A(a)[2a],A). Because the specified Tate sheaf is locally free of rank one, this is canonically the sheaf dual A(-a)[-2a] specified in the coefficient conventions. No arbitrary coefficient object or orientation is chosen. `projectiveBundleSummand` applies the exact comparison inverse image to that same finite coefficient object.
- `projectiveBundleCupEvaluation` evaluates the actual cup power on its opposite twist. `projectiveBundleSummandPullbackEtale` is the transpose of pullback of evaluation, using the normalized positive-line comparison. Its pro-etale version uses the canonical comparison square and the ordinary derived pullback.
- `projectiveBundleComponent` is the ordinary pro-etale pullback/direct-image adjunct of that evaluated cup power. `projectiveBundleMap` is `Sigma.desc` of these exact components, indexed by `Fin (n+1)`. The first conclusion is `IsIso` of this specific map.
- The remaining conclusion quantifies over every separated finite-type k-scheme B', every k-morphism g (the equation g ≫ b = b'), and every presentation F' isomorphic to g*F. Taking F'=g*F and the identity gives precisely the stated case; allowing isomorphic presentations makes no mathematical restriction. The base-change datum is the dependency's `G.baseChange`, so its map and tautological theta are the canonical ones. `projectiveBundleTargetBaseChange` uses the actual derived mate exchange and constant-coefficient comparison. Its invertibility and that of the source comparison are explicit, and the equality for each `a : Fin (n+1)` is the commuting base-change square for the actual component. These equalities determine the equality of finite coproduct maps, since derived pullback preserves coproducts. This includes degree zero.
- The category throughout is the ordinary uncompleted derived category of module-valued sheaves on the small pro-etale site, in its existing fixed-scalar coordinates. Its site object universe remains u+1 and its morphism universe remains u. No constructibility, smoothness, purity isomorphism, or additional geometric admissibility is assumed.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `Coefficient`, coefficient and field data.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: `SheafOfModules.IsFiniteLocallyFreeOfRank`, through the geometry dependency's `projectiveBundleRank`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`: `ProjectiveBundleTautologicalSystem`, `ProjectiveBundleRealization`, `ProjectiveBundleBaseChangeDatum`, and their normalized fields.
- `Sheaf.Paper.KummerAdditivity`: `Etale.kummerFirstChern`, `ProEtale.kummerComparisonPullback`, `ProEtale.kummerCoefficientPullback`.
- `Sheaf.Paper.PbcCoefficientTwists`, reexporting `FixedFinitePositiveCoefficientTwist`: `diagonalExponent`, its annihilation and unit theorems, and `diagonalTwistEtale`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports the finite fixed-scalar ordinary operations. The actual fixed-scalar `ProEtale.upperStar`, `lowerStar`, `derivedUpperStarLowerStarAdjunction`, `derivedBaseChangeMap` and exact-derived comparison are the published operations, not new definitions of a site or coefficient category.
- The existing étale tensor, internal Hom, unit, symmetry, tensor pullback and normalized line-pullback interfaces form the displayed arrows. All recorded, stated proof-dependency modules are imported privately.

Edge cases checked: n=0 has one summand and the zeroth cup power is the identity; its dual-unit evaluation is canonical. The empty base and empty total scheme remain allowed, including the zero global-section ring in the invertibility witnesses. Positive coefficient levels need not be divisible by the ramification index. No freeness or chosen primitive root is imposed globally. Arbitrary rank n+1 vector bundles, not only trivial bundles, are covered by the normalized relative-Proj geometry. Base change includes identities, arbitrary k-morphisms, and arbitrary isomorphic realizations of the pulled-back bundle. The base-change equality is equality of named maps rather than merely an assertion about isomorphic objects.

Searches (2026-10-18):

- LeanFinder via msearch: "Projective bundle formula in etale cohomology with finite coefficients powers of the first Chern class". Eight hits, including `Proj.pow_apply`, `Proj.one_apply`, `Proj.awayMap_awayToSection`, `Proj.pullbackAwayιIso_hom_awayι`, algebra differential projectivity and group-resolution declarations. None states the cohomological formula.
- Loogle via msearch: "AlgebraicGeometry, ProjectiveBundle". No hits; the service reports unknown identifier AlgebraicGeometry.
- Mathlib grep via msearch: `projective.?bundle|chern.?class`, AlgebraicGeometry. No hits.
- A second LeanFinder search for "projective bundle formula powers of Kummer Chern class derived pushforward constant coefficients" returned only algebraic Proj localization formulas.
- Direct rg in the upstream WeilConjectures source and the side-project Sheaf source for the node id, projective-bundle formula, cup powers, Chern powers, and cup products found no existing formula. Existing geometry, finite Tate powers, Chern classes, and ordinary operation interfaces are reused. `dag/lean_names_upstream.json` has no entry for this item. Search output is retained in the sandbox `searches.jsonl`.

Unstated proof dependencies (no recorded module to import): `lem-pur-compact-product-proper-support-compatibility`, `thm-pur-rank-one-thom`, `lem-pur-divisor-class`, `lem-pur-supported-cup-functoriality`, `lem-sf-derived-homology-long-exact`.

No statement correction, new independent notion, or dependency-record repair is used. Helpers in the owning module are the component constructions already specified by this theorem's statement and proof.

Implementation validation: the concrete derived-tensor unit comparison initially caused a kernel timeout. The component construction now uses coefficient-polymorphic helpers, specialized to the actual quotient ring, and a generic ordered cup recursion whose family is the existing positive Tate model. No mathematical object, assumption or normalization changed.

LeanSearch via msearch for "projective bundle formula etale cohomology powers Chern class" returned Proj power/basic-open formulas, projectivization notation, vector-bundle projections and etale base-change stability, with no cohomological formula.

Validation: scompile.py compiled the full sandbox module and library module cleanly (13.6 s and 14.1 s respectively). The generic coefficient helpers specialize to the given finite quotient and do not add a mathematical assumption. All public helpers, including these coefficient-polymorphic versions, are listed in lean.declarations.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
