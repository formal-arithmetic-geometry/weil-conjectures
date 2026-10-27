## Worker report

Delivered module: `Sheaf.CategoryTheory.Sites.InjectiveSectionsModel`.
Main declaration: `CategoryTheory.SiteInjectiveSectionsModel.injective_sections_model`.
The only postponed proof is this theorem. The two auxiliary definitions, `modelMap`
and `imageIso`, have complete data and name the composites specified by this node.
No new nodes, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-pullback-same-cohomology` (0DD8), especially its bounded-below proof sentence,
and `lemma-pullback-injective-pre-limp` (0D6X). This is the ordinary bounded-below
calculation, not an unbounded or per-degree substitute.

Hypothesis and clause correspondence:

* Small sites in one common universe: `{C D : Type u} [SmallCategory C]
  [SmallCategory D]`, `J : Precoverage C`, `K : Precoverage D`, `hJ`, `hK`
  of the recorded `Precoverage.IsSiteForCoverings`. Arbitrary explicit `w`
  supplies the three derived-category localizations. This retains all choices
  of the common site and coefficient universe; no object/morphism-universe
  equality beyond the node's small-category convention is added.
* Continuous and cocontinuous `u`: `f : C ⥤ D`, `hcover` maps actual covering
  presieves to covering presieves, and `hpullback` preserves pullbacks of a
  covering arrow along an arbitrary arrow. The class
  `f.IsCocontinuous J.toGrothendieck K.toGrothendieck` is exactly part (1) of
  the special-cocontinuity dependency. Local fullness, faithfulness, and
  cover-density from its other clauses are not assumed.
* Induced geometric morphism and its abelian inverse image `L`: use precisely
  `f.sheafPushforwardContinuous AddCommGrpCat J.toGrothendieck K.toGrothendieck`.
  Despite Mathlib's name, this is actual precomposition by `f.op`, hence the
  inverse image of the cocontinuous geometric morphism (00XR). No arbitrary
  functor, chosen geometric morphism, or unconstrained comparison is substituted.
* The existential `_hc`, `_ha`, `_hl`, `_hr` bind proof instances asserting
  Mathlib continuity, additivity, and preservation of finite limits and
  colimits of that fixed precomposition functor. They are conclusions from
  the stated Stacks continuity/cocontinuity hypotheses, never new assumptions.
  They make its termwise/derived exact extensions available in the statement.
  All are proof data; proof irrelevance prevents any dependence on a choice
  of inverse-image objects. They implement the node's instruction to use the
  exact derived extension of `L` without importing downstream helper modules.
* `U : C`, `M : DerivedCategory.Plus (Sheaf K.toGrothendieck AddCommGrpCat)`,
  `a : ℤ`, `[M.IsGE a]` are the fixed object, bounded-below coefficient,
  prescribed lower bound, and vanishing of cohomology below that bound.
  `DerivedCategory.Plus.isGE_ι_obj_iff` and `DerivedCategory.isGE_iff`
  identify the last condition with precisely the displayed cohomology vanishing.
* Existence of `(I,ρ)`: the first conjunct quantifies
  `I : CochainComplex.Plus (...)`, requires `I.obj.IsStrictlyGE a` and
  `∀ n : ℤ, Injective (I.obj.X n)`, and gives
  `Nonempty (DerivedCategory.Plus.Q.obj I ≅ M)`. There is no requirement that
  a resolution or an actual representative be chosen as definition data.
* Every such pair: the second conjunct universally quantifies `I`, its same
  strict termwise bound, termwise injectivity, and `ρ : Q.obj I ≅ M`.
  It does not merely assert the properties for the existential witness.
* `LI` zero below `a`: the first assertion in that universal clause is
  `(L.mapCochainComplexPlus.obj I).obj.IsStrictlyGE a`. This means all terms
  below `a` are zero objects, not just that their cohomology vanishes.
* `Lρ : Q(LI) ≅ LM`: the real definition `imageIso L I M ρ` has exactly this
  type. Its data is the inverse of `L.mapDerivedCategoryPlusFactorsh` at the
  bounded-below homotopy quotient of `I`, followed by `L.mapDerivedCategoryPlus.mapIso ρ`.
  Thus the node's displayed identification is explicit and canonical, not an
  arbitrary existential isomorphism.
* Positive evaluation cohomology of each term: `∀ (n : ℤ) (p : ℕ), 0 < p →
  IsZero ((evaluationFunctor.rightDerived p).obj (L.obj (I.obj.X n)))`.
  Here `evaluationFunctor` is written in full as `sheafToPresheaf ⋙ evaluation`.
  Natural degrees with `0 < p` encode exactly the positive integer degrees;
  the cohomology is the ordinary `rightDerived` of evaluation as in the dependency.
* The comparison unit `α`: `modelMap F I M ρ` is literally
  `F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I) ≫
  F.rightDerivedFunctorPlus.map ρ.hom`. Its source is `Q(F(I))`, and its target
  is `RF(M)` in `DerivedCategory.Plus`, with no replacement by cohomology groups.
* `a_{I,ρ}` is `modelMap` for evaluation at `f.obj U`; its `IsIso` assertion
  states the first displayed derived isomorphism with the specified map.
* `b_{I,ρ}` is `modelMap` for evaluation at `U`, applied to `L(I)`, `L(M)`, and
  `imageIso L I M ρ`; its `IsIso` assertion states the second displayed derived
  isomorphism with the specified map. Both maps exist independently of proving
  invertibility, so their normalization does not depend on a chosen inverse.
* Naturality quantifies `M'`, any bounded-below termwise-injective `I'`,
  `ρ' : Q(I') ≅ M'`, `t : I ⟶ I'`, and an arbitrary `c : M ⟶ M'`.
  The premise `Q.map t ≫ ρ'.hom = ρ.hom ≫ c` is exactly the coefficient
  compatibility, with Lean's left-to-right composition convention.
  The two final equations are, respectively, `a ≫ RΓ(c) = QΓ(t) ≫ a'`
  and `b ≫ RΓ(Lc) = QΓ(Lt) ≫ b'`. No invertibility of `c` or `t` is required.
  The second representative is not forced to have the first one's bound `a`.

Dependencies used, read from their recorded declarations and source docstrings:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the remaining site/cohomology
  conventions use Mathlib `Sheaf`, `sheafToPresheaf`, and ordinary `Functor.rightDerived`.
* `def-weil-size-convention` is metatheoretic, recorded as a convention:
  explicit `u`, `w` and `HasDerivedCategory` express it without a new object.
* `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `CategoryTheory.GeometricMorphism`;
  here the induced geometric morphism is represented by its canonical inverse
  image, rather than an unrelated additional geometric-morphism parameter.
* `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`:
  `CategoryTheory.Functor.IsSpecialCocontinuousForCoverings`; only its cocontinuity
  clause and the two covering-continuity clauses are needed, written explicitly.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; bounded-below versions are
  `DerivedCategory.Plus`, `.Plus.Q`, `.Plus.Qh` from TStructure/Plus.
* `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
  Its recorded companion `InjectiveResolution` is an object-resolution notion;
  the complex here is correctly required termwise injective instead.
* `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus`, `Functor.rightDerivedFunctorPlusUnit`;
  these are the exact recorded match for lem-weil-pbc-right-derived-plus-injective.
* `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`
  exposes the exact derived extension, its termwise factorization and the ordinary units.

Proof dependency imports are retained privately:
`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`:
`CategoryTheory.constant_left_module_inverse_image`,
`Sheaf.CategoryTheory.Sites.PullbackInjectiveEvaluationAcyclic`'s
`CategoryTheory.isZero_rightDerived_evaluation_pullback_injective`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`'s
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`.
The representative-existence Mathlib lemma
`DerivedCategory.Plus.exists_injective_nonempty_iso` is exposed transitively by
PlusExact's RightDerivedFunctorPlus import. No downstream ObjectDerivedSectionsPullback
import is used, avoiding a proof-import cycle with this item's consumer.

Edge cases checked: `M = 0` allows zero or nonzero acyclic injective representatives;
the universal clause covers both. `a` can be negative, zero or positive; no truncation
to nonnegative complex degrees is made. `p = 0` is correctly excluded only from
positive vanishing. `f = 𝟭` gives the expected ordinary injective model on both sides.
An empty site causes no global object-existence assumption: the theorem takes a
particular `U`. Empty covering families and finite covering sites remain allowed by
`IsSiteForCoverings`; global pullbacks and indexed-composition closure are absent.
The coefficient map and chain map may be zero or noninvertible, and `I'` may have
a different lower bound. No statement dispute or correction was found.

Searches before writing:

* `msearch.py leanfinder`, query "Bounded below injective representatives and inverse
  image compute ordinary derived sections naturally under continuous cocontinuous
  functors of small sites": eight hits on cocontinuous sheaf adjunctions and Ran
  constructions; none states this complete model assertion.
* `msearch.py loogle`, query `"rightDerivedFunctorPlusUnit", "IsIso"`: one hit,
  the ordinary unit's injective-complex isomorphism instance. Reused its unit;
  it does not supply both site models or the inverse-image acyclicity clause.
* `msearch.py grep`, query `rightDerivedFunctorPlusUnit|mapDerivedCategoryPlus`,
  subdirectory `Algebra/Homology`: five hits in RightDerivedFunctorPlus, reused.
* `msearch.py leansearch`, query "A bounded below injective complex and its inverse
  image compute derived sections naturally on corresponding site objects": eight
  hits, including DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE and unrelated
  stalk/locally-injective results; no exact statement.
* `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for section models,
  `rightDerivedFunctorPlusUnit`, and inverse-image/sheaf names found the distinct
  downstream `Sites/ObjectDerivedSectionsPullback.lean` and the evaluation-acyclicity
  dependency. The former asserts a comparison of section functors; it does not
  state this node's bound-preserving existence plus all representative models.
* `grep -rn lem-trf-site-injective-sections-model lean/WeilConjectures` found no
  recorded upstream declaration. `rg` for the new names in Mathlib and both
  project roots found no declaration with any of the three new full names.

Validation: `scompile.py Q20 lem-trf-site-injective-sections-model <module>` compiled
both sandbox and actual module successfully, in about 11 seconds each, within the
60-second per-file limit. The first attempt identified a privately imported
`Functor.rightDerived`; adding the explicit public Mathlib RightDerived import
resolved it. No warning remains. All variables and universes are explicitly bound,
and no local notation, private definition, let statement binder, new axiom, or
proved theorem is introduced.

## Second reading by Q20

I reread the node and the delivered file clause by clause after the successful compile.
This is the worker's own second pass; the dispatcher explicitly prohibited starting
another agent, and the maintainer supplies the independent review.

Two checks changed the initial draft: the positive-cohomology functor needed its own
public RightDerived import, and the naturality clause must not require the second
representative to vanish below the first bound `a`. The delivered clause instead
allows every bounded-below injective `I'`. The canonical-map directions were checked:
`imageIso` uses the inverse localization factorization, and `modelMap` applies the
unit before `RΓ(ρ)`. Both naturality equations have these same morphisms on both sides.
The proof-instance existentials neither choose functors nor restrict the hypotheses.
The source text, termwise lower bound, all-representatives quantifier and both ordinary
derived models agree with the unchanged DAG statement.
