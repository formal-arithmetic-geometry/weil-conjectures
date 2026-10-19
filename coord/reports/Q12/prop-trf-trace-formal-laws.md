## Worker report

The delivery states the four formal laws of `prop-trf-trace-formal-laws` in
`Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws`. Every theorem is left `sorry`.
The same module also states the explicit nonadditivity warning and characterizes the
common-stage scalar uniquely. The first three laws bind the recorded global datum `D`,
its coefficient datum `c`, a finite intermediate field `E`, and `n ≥ 1`. They use exactly
`Padic.coefficientExtensionRing c.l E n = O_E / ϖ_E^n` and the recorded finite-coefficient
trace. The field law is a conjunction for exactly `E` and the fixed closure `c.Qbar`. No scheme or sheaf
complex replaces an ordinary coefficient complex.

Hypothesis and clause correspondence:

- The ordinary derived category is `DerivedCategory (ModuleCat A)`. Its localization
  universe is the small Hom universe used by the recorded trace, rather than the larger
  standard localization. `IsPerfectRingComplex` is the recorded bounded finite-projective
  representative predicate. It is never replaced by finite cohomology over a ring.
- The common coefficient binders in clauses (1)--(3) are `D`, `c`, `E`,
  `[FiniteDimensional (Padic c.l) E]`, `n`, and `hn : 1 ≤ n`; primality,
  `ℓ ≠ p`, and the fixed algebraic closure are fields of the recorded datum.
- Clause (1): `P₁`, `P₂`, `h₁`, `h₂` give the two perfect objects; `v₁`, `v₂` are their
  derived endomorphisms; `w : P₁ ≅ P₂` is the isomorphism. `hw` writes
  `v₂ ∘ w = w ∘ v₁` using Lean's left-to-right composition. The conclusion is equality
  of the two existing `finiteCoefficientCategoricalTrace D c E n hn` scalars.
- Clause (2): `P : TwoStepModuleDerived (Padic.coefficientExtensionRing c.l E n)` and `v : P ⟶ P` mean exactly a pair of
  unbounded complexes localized at quasi-isomorphisms on subcomplex and quotient,
  modulo filtration-preserving homotopies. `twoStepTotal` forgets the filtration;
  `twoStepGraded A true` and `... false` are the recorded subcomplex and quotient
  functors. `h`, `h'`, `h''` require all three ordinary objects perfect. The trace
  equation is the trace of the total endomorphism equals the sum of the two graded
  traces. This states the assertion on the inducing filtered object itself; its
  subcomplex--total--quotient sequence induces the distinguished triangle in the
  node. An isomorphic triangle with intertwining endomorphisms has the same equation
  by clause (1). The endomorphism can be any localized filtered morphism, not just a
  chain map. Applying `twoStepModuleQ` includes the stated chain-map special case.
- The warning is a separate theorem `perfectCategoricalTrace_triangle_counterexample`.
  `M` is zero outside degrees 0 and 1, `e₀`, `e₁` identify both terms with `ZMod 4`,
  and its differential is multiplication by 2. `w` has components 0 and 2. The
  distinguished triangle `T` has single complexes in degrees 1 and 0 at its ends and
  middle `Q.obj M`. The maps `ι`, `π` are normalized to the identity in degrees
  1 and 0, respectively, and the first two triangle maps intertwine with their
  derived images. Thus this is the displayed short exact sequence. The triangle endomorphism `f` is zero at both ends, corresponds
  to `Q.map w` in the middle, and its middle trace is `-2 ≠ 0`.
- Clause (3): `ρ` is an arbitrary unital commutative-ring homomorphism, `P` is perfect
  and `v` a derived endomorphism. `LF`, `ε`, `hLF` specify exactly the universal total
  left derived functor of the ordinary termwise extension `ModuleCat.extendScalars ρ`
  on homotopy categories. This is the universal derived construction in the node,
  not an arbitrary functor or assumed tensor comparison. The conclusion supplies
  perfectness `hB` and states the scalar identity with `LF.map v`. No flatness of
  `ρ` is assumed. The additivity instance needed to type the homotopy functor uses
  the existing proved `ModuleCat.extendScalars_additive_sheaf`, with real data.
- Clause (4): the two conjuncts give `Λ = E` and `Λ = c.Qbar`, respectively.
  In each conjunct, `pointFiniteDimensional Λ P` is exactly bounded finite-dimensional
  cohomology. Perfectness is concluded, not added as a hypothesis. The right side
  is the finitely supported integer sum `∑ᶠ i`, with `Int.negOnePow` acting on the
  ordinary finite-dimensional `LinearMap.trace` of the homology endomorphism.
- Common stages: `D` and `c` fix `ℓ ≠ p` and `Ω = c.Qbar`;
  `X : PointFdQbar c.l c.Qbar` and its endomorphism `v` use the recorded
  category. Every finite field `E`, bounded finite-dimensional stage object `P`,
  stage isomorphism `e`, and stage endomorphism `w` intertwining with `v` are
  quantified. `∃! t : Ω` characterizes the scalar by all these presentations: both
  its categorical trace and its cohomological supertrace, included by `E.val.subtype`,
  equal `t`. This includes the original stage, a larger common stage, and arbitrary
  further extensions, including equality of fields. It makes no equivalence claim
  between the common-stage category and the full ordinary category over Ω.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  `CoefficientDatum`; the finite coefficient extension and ring are
  `Padic.coefficientExtensionRing` as in the coefficient-conventions record.
  The broad geometric `TraceFormulaCoefficientConventions` module was not imported:
  it is not used by these ordinary-module signatures, it introduces a competing
  standard localization instance, and its current import closure fails in
  `IntegralCompactSupportCoefficientData` on missing `IsIso` instances for
  `openRestrictionMap` and `completedPullMap`. The smaller recorded finite-field
  and trace modules supply exactly the coefficient data and trace used here;
  no replacement definition of the geometric conventions is introduced.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace`:
  `WeilConjectures.finiteCoefficientCategoricalTrace` and
  `DerivedCategory.perfectCategoricalTrace`, with the exact dual-frame construction
  and scalar extraction; `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`.
- `Sheaf.Paper.PointFdComplexes`: `DerivedCategory.pointFiniteDimensional`;
  `Sheaf.Paper.PointFdQbarCategory`: `DerivedCategory.PointFdQbar` and
  `DerivedCategory.pointFdQbarStage`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `Qh`,
  `HasDerivedCategory`; its homology functors are the ordinary module-valued functors.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: the recorded base-change construction;
  `ModuleCat.extendScalars` is its existing bundled functor. The universal property
  is `Functor.IsLeftDerivedFunctor` from `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`.
- `Sheaf.Algebra.Homology.TwoStepFilteredModuleDerived`:
  `CochainComplex.TwoStepModuleDerived` and `twoStepGraded`;
  the new `Sheaf.Algebra.Homology.TwoStepFilteredTotal` supplies only its total functor.
- Proof imports retain `DerivedCategory.chain_supertrace`,
  `CochainComplex.exists_filteredProjectiveModel`,
  `ModuleCat.scalarExtensionCounit_isIso_of_kFlat`, the bounded-flat K-flat module,
  K-projective Hom bijectivity, projective-flatness and vector-space projectivity.
  Field scalar extension is public through the common-stage category imports.

Edge cases checked: zero complexes and zero endomorphisms; empty cohomology support;
negative as well as positive cohomological degrees (integer sign); nonfree finite
projective terms (the categorical trace is not `LinearMap.trace` on such terms);
nonflat scalar extensions and the zero target ring; unbounded original filtered
representatives with perfect graded pieces; a zero subcomplex or quotient; identical
coefficient stages and different finite-stage representatives. The `Z/4` example
checks `2*2=0`, middle supertrace `0-2=2 mod 4`, null-homotopy of the left square,
and the reason the zero-end triple does not lift as that filtered endomorphism.

Searches for an existing whole statement:

- msearch LeanFinder, `categorical trace perfect derived complexes conjugacy filtered
  additivity scalar extension supertrace`: eight derived-linearity/Ext hits, no match.
- msearch Loogle, `LinearMap.trace, LinearMap.baseChange`: `LinearMap.trace_baseChange`,
  which concerns finite free modules, not derived categorical traces or filtered origin.
- msearch LeanSearch, `categorical trace additivity filtered derived perfect complexes`:
  eight additivity/triangulation hits, no trace-law statement.
- msearch grep, `trace.*(conj|map|add)|supertrace` in `LinearAlgebra/Trace`: zero hits.
- Direct rg in Mathlib monoidal rigid sources and in upstream `WeilConjectures`, and
  `grep -rn prop-trf-trace-formal-laws` upstream: no whole-item match. The upstream
  `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace` was read in full:
  it is the chain finite-free supertrace, has additional braiding hypotheses, and
  does not state these four laws. The side `ChainSupertrace` was read and reused.
- Search of side `lean/Sheaf` for trace formal laws, filtered trace, supertrace and
  `perfectCategoricalTrace`: only the existing defining trace and chain-supertrace
  infrastructure, which this module imports rather than duplicates.

No statement correction or mathematical dispute is claimed.

## New nodes

`def-trf-two-step-filtered-total` defines the canonical functor forgetting a two-step
filtered derived object to its total ordinary derived object. Source: Stacks trace.tex,
filtered derived category at Tag 03TB, and clause (2) of this blueprint proposition.
The existing definition node gives the pair localization and its two graded functors,
but no total functor. The new module uses that exact category and descends the literal
`Arrow.rightFunc ⋙ DerivedCategory.Q` through the filtered homotopy quotient and
localization. Its two postponed compatibility assertions are explicitly in the new
node's statement and have proof docstrings; its definitions contain real data.
LeanSearch/LeanFinder found bicomplex totalization and forgetting differentials, not
forgetting filtrations; Mathlib/upstream/side grep found no corresponding declaration.
The DAG search also checked the existing filtered-calculus nodes: their bounded or
bounded-below categories and sheaf functors do not give this unbounded two-step functor.
Queries and results are recorded in the new node's `mathlib_searches`.

## Second reading by Q12

Author's separate checking pass; the independent reading is the maintainer's delivery
review, as required by the dispatch brief. I reopened the node, source statement and
both modules. Checked the direction of the intertwining equations, the true/false
order of subcomplex and quotient, and the fact that the filtered morphism is localized.
Checked scalar extension uses a universal pair and imposes no flatness. Checked the
field conclusion derives perfectness from the recorded finite-dimensional-cohomology
predicate. Checked the common-stage theorem quantifies over all presenting stages
and maps, and states uniqueness rather than choosing an unspecified scalar. Checked
that the nonadditivity warning includes both zero end maps and the explicit middle
model. Replaced an erroneous Finsum import with Mathlib's Finprod module during compile
repair. Universe inference was tested separately before finalizing the signatures.

Validation: both modules compiled cleanly through scompile.py. The initial dry run
identified only blueprint-path and signature-serialization metadata defects; both were
repaired, and the explicit counterexample maps were additionally normalized.
