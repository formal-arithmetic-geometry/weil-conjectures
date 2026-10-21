## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.DerivedSquareShiftOnKInjectives`
states `CategoryTheory.derivedSquare_shift_on_kinjectives`, with its proof `sorry`.
Its two computation-map helpers are actual composites of existing canonical maps,
with no postponed data or new mathematical notions. The node changes only in `lean`.

Hypothesis-by-hypothesis correspondence:

- The four abelian categories are `A`, `B`, `A'`, `B'`, each with its own object,
  morphism and derived-localization universes. `[Abelian ...]` is the recorded
  `CategoryTheory.Abelian`; `[HasDerivedCategory ...]` and `DerivedCategory.Q`
  are the recorded unbounded localization, not a bounded-below replacement.
- `F`, `G`, `t`, `r` have exactly the domains and codomains in the node.
  Four `Additive` instances express additivity. `t` and `r` have
  `PreservesFiniteLimits` and `PreservesFiniteColimits`, expressing exactness.
  `δ : F ⋙ r ≅ t ⋙ G` has the node's direction (Lean writes composites in
  order of application).
- Termwise application is `Functor.mapHomologicalComplex (.up ℤ)`.
  The termwise comparison is the existing
  `NatTrans.mapHomologicalComplex δ.hom (.up ℤ)`, directly, rather than a
  second definition. `t.mapDerivedCategory` and `r.mapDerivedCategory` are
  the exact derived functors from the recorded dependency.
- `hA` and `hA'` say that every complex has a quasi-isomorphism `s : K ⟶ I`
  to a complex satisfying `CochainComplex.IsKInjective`. That existing
  predicate says precisely that every map from an acyclic complex is
  homotopic to zero. These hypotheses do not require `s` to be mono:
  the upstream `Abelian.HasKInjectiveResolutions` class additionally requires
  monomorphic resolutions, so it is intentionally not substituted here.
  `ht` says that termwise `t` preserves K-injectives.
- `RF`, `RG`, `ηF`, `ηG` are arbitrary specified presentations, with the
  precise comparison-map directions `Q C(F) ⟶ RF Q` and `Q C(G) ⟶ RG Q`.
  The two `IsRightDerivedFunctor` instances express their right-derived
  universal property at the quasi-isomorphisms. `hηF`, `hηG` express the
  stipulated invertibility on K-injectives.
- `[RF.CommShift ℤ]`, `[RG.CommShift ℤ]` supply the shift comparisons.
  `hshiftF` and `hshiftG` specify that these are the shifts computed using
  shifted K-injectives: on each K-injective `I`, shifting the unit or taking
  the unit at `I[n]` agrees after inserting the canonical shifts of `Q`
  and termwise application. This is only required on K-injectives, exactly
  where the node prescribes the computation. The shifts of `t_D`, `r_D`
  are the existing exact-functor instances, and are not independently chosen.
- `γ : RF ⋙ r.mapDerivedCategory ≅ t.mapDerivedCategory ⋙ RG` is the
  specified comparison. `hnorm` is its normalization for every complex `K`,
  using the two helper maps to insert the factorization isomorphisms.

The helpers have the exact directions in proof step 1. Namely,
`derivedSquareLeftComputation F r RF ηF I` is
`φ_r.inv ≫ r_D.map (ηF.app I)`, and
`derivedSquareRightComputation G t RG ηG I` is
`ηG.app (C(t)I) ≫ RG.map φ_t.inv`.
Thus `hnorm` reads `a_K ≫ γ_(QK) = Q(C(δ)_K) ≫ b_K`.

Clause-by-clause correspondence:

- The first conjunct quantifies over every `E`, every K-injective `I`,
  and every representative isomorphism `e : Q.obj I ≅ E`. It states that
  `a_I` and `b_I` are isomorphisms, and that precomposing `γ_E` with
  `a_I ≫ (RF ⋙ r_D).map e.hom` gives the termwise comparison followed by
  `b_I ≫ (t_D ⋙ RG).map e.hom`. This is exactly the model formula under
  the computation isomorphisms, written without choosing inverses of proofs.
- The second conjunct is the displayed shift equation for all `n : ℤ`
  and `E : DerivedCategory A`. The comparison maps are those of the
  two composite functors. In Lean's composition order it reads
  `γ_(E[n]) ≫ s_B = s_A ≫ γ_E[n]`.
- The third conjunct identifies the two chain-level routes after the
  termwise shift comparisons: `u_(I[n]) ≫ τ_target = τ_source ≫ u_I[n]`.
  Together with the representative formula and stipulated unit shifts,
  this is their common model in the displayed derived shift square.
- The final conjunct identifies both `u_(I[n]).f a` and `(u_I[n]).f a`
  with `δ.hom.app (I.X (a+n))`. It also states the differentials of both
  termwise shifted models explicitly, as `n.negOnePow` times the respective
  images of `I.d (a+n) (a+1+n)`. Thus there is no extra sign on δ, and the
  signed differential is included for both source and target.
- Every formula uses the supplied `γ`; no independently chosen derived
  isomorphism appears.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, including its full class signature.
- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and its `CommShift` instance,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `lem-weil-pbc-exact-functor-derived-factorization` (Mathlib leaf):
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  and their shift compatibility, `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
  The existing interface is usable without repair.
- `lem-weil-pbc-kinjective-shift` (proof dependency, Mathlib leaf):
  the shift instance for `CochainComplex.IsKInjective` and
  `CochainComplex.isKInjective_shift_iff`,
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`; the resolution
  clause uses the shift quasi-isomorphism instance in `ShiftSequence`.
- Additional standard APIs: `NatTrans.mapHomologicalComplex` in
  `Mathlib.Algebra.Homology.Additive`; termwise shift comparisons and signed
  differentials in `Mathlib.Algebra.Homology.HomotopyCategory.Shift`;
  `Functor.IsRightDerivedFunctor` in
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived`.

The source passages were opened in local `sites-cohomology.tex` (the
restriction discussion, `lemma-restrict-K-injective-to-open`,
`lemma-restrict-direct-image-open`) and `derived.tex`
(`lemma-right-derived-exact-functor`, `definition-K-injective`).
The node already records the abstract additive-square/integer-shift refinement;
the declaration docstring carries all six proof steps.

Edge cases checked before writing: shifts zero, plus one, minus one, and even
integers; the zero complex and zero object; identity functors and arbitrary
natural automorphisms δ in an identity square; arbitrary (not just canonical)
representative isomorphisms `QI ≅ E`; categories with different universes.
`n.negOnePow` handles negative integers. No nonzero-object, boundedness,
monomorphic-resolution, common-universe, or left-exactness hypothesis on F/G
has been added. No statement dispute or correction was needed.

Searches actually run using `msearch.py`:

- LeanFinder: “A normalized square of right derived functors computed on
  K injective complexes commutes with integer shifts”: eight hits including
  the exact-functor shift and factorization instances and classical objectwise
  right-derived lemmas; no exact normalized unbounded-square statement.
- Loogle: `"CommShift", "rightDerived"`: twelve online hits, including
  `Functor.IsRightDerivedFunctor.commShift` and
  `NatTrans.CommShift.of_isRightDerivedFunctor`. Their online
  `RightDerivedCommShift`/`RightDerivedCompositionCommShift` modules are absent
  in the pinned library. They also do not include this node's representative
  and degreewise formulas.
- Mathlib grep: `rightDerived.*[Cc]ommShift|[Cc]ommShift.*rightDerived`:
  zero hits in the pinned Mathlib.
- LeanSearch: “Natural comparison of right derived functors computed on
  K injective resolutions commutes with shifts”: eight hits concerning the
  classical objectwise derived functors, not this unbounded square.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for
  K-injective, derived-square and shift/comparison phrases found the existing
  right-derived construction, K-injective model APIs, and specialized squares,
  but no exact match. An upstream grep for this node's id found no declaration.
  The three new declaration names were searched in Mathlib and both project
  source roots and had no collisions. No new DAG notion is needed.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
