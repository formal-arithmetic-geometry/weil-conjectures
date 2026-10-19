## Worker report

The module `Sheaf.AlgebraicGeometry.FppfFiniteSurjectiveRefinement` states
`AlgebraicGeometry.exists_finite_surjective_fppf_refinement` with proof `sorry`.
It has no definitions with postponed data. The source is Stacks Project,
`more-morphisms.tex`, Tag 0CP0 (lemma-dominate-fppf-finite).

The Lean statement renders the node clause by clause. `X : Scheme.{u}` is the
scheme, `[CompactSpace X]` is quasi-compactness of its underlying space, and
`[QuasiSeparatedSpace X]` is quasi-separatedness. `I : Type u`, `Xi : I →
Scheme.{u}`, and `f : (i : I) → Xi i ⟶ X` give the small covering family.
The instance binders `[∀ i, Flat (f i)]` and `[∀ i,
LocallyOfFinitePresentation (f i)]` state flatness and local finite
presentation for every member. `hjoint` states joint surjectivity pointwise.
The conclusion supplies `X'`, `p : X' ⟶ X`, and the conjunction of finite,
locally finitely presented, quasi-compact, quasi-separated, and surjective
properties. It then supplies a small index type `A : Type u`, schemes
`U : A → Scheme.{u}`, and maps `j a : U a ⟶ X'`; each is an open immersion,
each has an index `i` and an `X`-morphism `g` expressed by
`g ≫ f i = j a ≫ p`, and the family is jointly surjective on `X'`. No
flatness of `p` is assumed. Empty `I`, `A`, and `X` remain permitted by the
quantifiers and existential conclusion.

The statement uses Mathlib declarations `AlgebraicGeometry.Scheme`,
`CompactSpace`, `QuasiSeparatedSpace`, `AlgebraicGeometry.Flat`,
`LocallyOfFinitePresentation`, `IsFinite`, `QuasiCompact`,
`AlgebraicGeometry.QuasiSeparated`, `Surjective`, and `IsOpenImmersion`.
The Mathlib fppf interface is imported from `Mathlib.AlgebraicGeometry.Sites.Fpqc`;
its `fppfPrecoverage` is the jointly-surjective flat, locally-finitely-presented
precoverage, but it does not state the finite refinement theorem.

Searches made:

* `msearch.py ... leanfinder "finite surjective finitely presented morphism refining an fppf covering of a quasi-compact quasi-separated scheme"` returned only generic cover and jointly-surjective declarations (`QuasiCompactCover`, `Scheme.JointlySurjective`, `Scheme.Hom.cover`), with no refinement theorem.
* `msearch.py ... loogle "AlgebraicGeometry.Scheme.Cover, AlgebraicGeometry.Scheme.fppfPrecoverage, AlgebraicGeometry.IsFinite, AlgebraicGeometry.Surjective"` returned zero hits.
* `msearch.py ... grep "finite.*surjective.*fppf|fppf.*finite.*surjective" AlgebraicGeometry` returned zero hits.
* `rg` over `WeilConjectures` and project `lean/Sheaf` found no declaration for this node; the only nearby declaration is an etale-specific refinement theorem with a different statement.

Edge cases checked: an empty scheme permits an empty covering; an empty
indexing type can be jointly surjective only when the target is empty; the
conclusion permits an empty `A`; identity and singleton covers fit the same
quantifiers. The universe uses one explicit `u` for schemes and index types,
consistent with the size convention.

## Second reading by ND

I reread Tag 0CP0 and the node. Every hypothesis and conclusion above is
present in the source: quasi-compact and quasi-separated `X`, a small family
of flat locally finitely presented jointly-surjective maps, a finite (hence
finite-presentation) surjective `p`, and an open cover with local lifts. The
Lean conjunction records the source properties individually and the displayed
commuting equation is exactly the required `X`-morphism condition. No
hypothesis or conclusion was added beyond the source's explicit finite
presentation requirement, and no flatness of `p` was introduced. The recorded
Mathlib declarations were opened in their source files; none states the full
result. The module compiles cleanly through `scompile.py`, with only the
expected `sorry` proof warning suppressed by the project options.
