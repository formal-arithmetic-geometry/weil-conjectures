## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearScalarDerivedComparison` states
`AlgebraicGeometry.ProEtale.VaryingRing.derivedScalarComparison` and its normalized
level-evaluation clause `scalarD_evaluation`. Both proofs are `sorry`. All other
introduced declarations are actual localizations, the specified mate, or projections
of already supplied exactness data. No data is selected from a bare Nonempty theorem.
There are no new nodes, dependency repairs, or changes to the natural-language statement.

Hypotheses and clauses, read against the node:

- The arbitrary commutative ring sequence is `R : ℕ → CommRingCat.{u + 1}` and
  `φ : ∀ n, R (n + 1) ⟶ R n`. Index n denotes positive level n+1, as in the tower
  dependency. `B : Type (u + 1)` and `[CommRing B]` give the constant ring;
  `ψ : ∀ n, CommRingCat.of B ⟶ R n` and the explicit `hψ` binder assert precisely
  `ψ (n + 1) ≫ φ n = ψ n`. No flatness, finiteness, or surjectivity is assumed.
- The ordinary package named in the statement is the parameter
  `D : OrdinaryScalarComparison R φ B ψ`. Its existence for every compatible ψ is
  the recorded `ordinaryScalarComparison`; its level sections and transitions fix
  exactly sectionwise restriction. The present result applies to every such normalized
  package, with no new comparison hypotheses. `scalarRhoAdditive`, `scalarRhoLimits`,
  and `scalarRhoColimits` project its existing fields. `scalarRho D X` is exactly
  `(D.rho X).mapDerivedCategory` on the existing unbounded system categories.
- For every `f : X ⟶ Y`, the dependency's names `G R φ f` and `P R φ f` mean inverse
  image and total right derived direct image, respectively: these are P_f and S_f
  in this node's prose. Their adjunction is `adj R φ f`. The constant-ring names
  are `StrictTower.G B f`, `StrictTower.R B f`, and `StrictTower.adj B f`.
- `scalarB` is the inverse-image isomorphism obtained by
  `mapDerivedCategoryNatIso (D.b f)`, between the inverse composition identification
  and the forward composition identification. Thus b is the specified localization,
  not a freely chosen isomorphism.
- `scalarD` is definitionally
  `(mateEquiv (adj R φ f) (StrictTower.adj B f) (scalarB D f).inv).natTrans`.
  Mathlib's `mateEquiv` is precisely the displayed unit--inverse-b--counit word.
  The first conjunct of `derivedScalarComparison` states its `IsIso`, for every map.
- `scalarLevel` localizes `D.level` and the exact evaluation functors.
  `scalarLevelD` directly applies the recorded
  `Scheme.proEtaleRingRestrictionDerivedDirectImage` to the constant B and R n
  sheaves, their scalar maps, and the two `StrictTower.constantRingIso`s.
  Its coefficient-square proof is the existing
  `Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)`, reversed.
  `scalarD_evaluation` equates evaluation of scalarD, followed by `StrictTower.evalR`
  and the restricted-level identification, with `scalarLevel`, restricted `evalP`,
  and this exact ring-change comparison. This is the evaluation clause as an actual
  equality of morphisms, with all source/target identifications displayed.
- For every open `j` (only `[IsOpenImmersion j]`), `scalarA` localizes `D.a j`
  through the two exact composition isomorphisms. Its inverse is equated in the
  second conjunct to J_B applied to restricted η^o,C, then J_B applied to b_j,
  then the specified ε^o,B. This is exactly the left open-adjunction mate word.
- The third conjunct quantifies over the four schemes, k,r,p,i,
  `[IsOpenImmersion k]`, `[IsOpenImmersion i]`, `[QuasiCompact k]`,
  `[QuasiCompact i]`, `[IsProper r]`, `[IsProper p]`, and `h : k ≫ p = r ≫ i`.
  It is exactly the proof's expanded alpha preservation equation, using the existing
  `alpha R φ ...` and `StrictTower.alpha B ...` and the specified scalarA/scalarB.
  Neither a cartesian-square assumption nor an identity-left assumption occurs.
  The equality is before proper mating and before evaluation; it asserts no
  faithfulness of derived evaluation.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison`:
  `OrdinaryScalarComparison`, all its rho/additive/limits/colimits/level/b/a fields,
  and the ordinary existence and alpha-normalization theorem/docstring.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, its systems/geometric
  fields, `AdjunctionEvaluation`, and `evaluation_mate` supply the proof interface.
  Its existing `res`/`resD` (from `SemilinearSystemModels`) are the very same actual
  sheaf restriction functors as `Scheme.proEtaleRingRestrictScalars`; they give the
  level notation without introducing a second coefficient restriction.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`:
  `AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus`, together
  with its imported actual `G`, `R`, `adj`, `J`, `jAdj`, `ev`, `evalR`, and `alpha`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `Scheme.proEtaleRingSheafChangeAdjunction` and
  `Scheme.proEtaleRingRestrictionDerivedDirectImage`, including its unique derived
  unit normalization, full signature, and representative proof docstring.
- The scheme-morphism-properties dependency explicitly fixes no new notion; the
  imported Mathlib `IsOpenImmersion`, `QuasiCompact`, and `IsProper` are its notions.
- Proof-only localization and mate imports are
  `Mathlib.CategoryTheory.Localization.Predicate` (`liftNatTrans`, `liftNatIso`,
  `natTrans_ext`) and `Mathlib.CategoryTheory.Adjunction.Mates` (`mateEquiv`).
  The varying-ring operations and proper/open arrows are already publicly imported
  by the ordinary comparison dependency, so no duplicate notion is needed.

Source read: Stacks `sites-modules.tex`, lemma-adjoint-pullback-pushforward-modules
(Tag 03D7), its full adjunction statement and proof, and the current blueprint
`main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`,
coefficient comparisons of tensor evaluation and adjunction units/counits. The six
node proof steps are retained in the two theorem docstrings: exact localization;
evaluation of the mate word; single-level ring-change normalization; joint detection
of isomorphisms; open left mate; localization of intrinsic alpha before proper mating.

Edge cases checked: n=0 is the first positive level, with no missing initial level;
zero rings and zero objects remain allowed; no boundedness or uniform lower bound
is imposed; empty schemes and identity maps/opens are included; general noncartesian
proper/open squares retain the clopen-projector alpha. Nonflat coefficient maps are
allowed throughout. The small pro-etale site keeps object universe u+1 and morphism
universe u. Coefficients live in u+1 and the standard derived localization uses u+2;
no site-universe equality was imposed. A global named specialization
`scalarLocallyBijective` merely applies the existing locally bijective instance at
these universes; this resolves elaboration without adding a hypothesis or sorry.

Searches for an existing complete statement:

- `msearch.py ... leanfinder` with “Derived scalar restriction for semilinear systems
  preserves inverse image and open extension and the direct image comparison is its
  invertible adjunction mate”: eight scalar adjunction hits, beginning with
  `ModuleCat.extendRestrictScalarsAdj`; no simultaneous derived-system assertion.
- `msearch.py ... loogle 'CategoryTheory.mateEquiv, CategoryTheory.IsIso'`: zero hits.
- `msearch.py ... grep 'restrictScalars.*(Derived|derived|mate)|[Ss]emilinear.*[Ss]calar'`:
  zero hits.
- `msearch.py ... leansearch` with “Exact scalar restriction on inverse systems of
  sheaves of modules commutes with derived direct image via its adjunction mate”:
  eight hits on ordinary scalar restriction and adjunctions, including
  `SheafOfModules.restrictScalars` and `PullbackConstruction.adjunction`; no match.
- `rg -n 'semilinearScalarDerived|derivedScalarComparison|lem-sf-semilinear-scalar-derived-comparison'`
  over both named project source roots: no existing declaration.
- Broader source searches located the actual existing constant-ring naturality,
  exact-localization, semilinear evaluation, and ring-change declarations above.
  These are reused rather than restated.

Validation: scompile.py compiled this delivered module in sandbox mode and with its
library module name cleanly (8.3 s and 6.9 s after the final signature update), with
no errors or non-sorry warnings. The prescribed delivery dry run follows this report.

## Second reading by NQ

I reread the item, the dependency signatures, and the complete final file clause by
clause. No second agent was started: the dispatcher's brief expressly prohibits it;
the maintainer's independent review remains the independent reading of the delivery.
The explicit coefficient compatibility hψ was added to both theorem signatures so
that the given compatible maps remain an explicit hypothesis rather than being
silently omitted. The evaluation equation has the ring-change hom on the right and
the two direct-image evaluation comparisons in their recorded orientations. The
open inverse equation has η of J_C ⊣ G_C and ε of J_B ⊣ G_B, with no swapped
adjunction. The alpha equation begins at restricted G_p J_i and ends at J_k^B G_r^B
of restricted input, matching both sides of node proof step 6. The two theorem
proofs alone are postponed; no definition contains sorry. The statement is not
disputed, and no natural-language correction is needed.
