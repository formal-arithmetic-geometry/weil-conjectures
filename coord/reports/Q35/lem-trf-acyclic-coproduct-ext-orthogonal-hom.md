## Worker report

The delivery states `CategoryTheory.acyclic_hom_of_coproduct_ext_orthogonal` in
`Sheaf.CategoryTheory.AcyclicCoproductExtOrthogonalHom`, with one `sorry` and no new
definition. The node's statement and all its dependencies and proof steps are unchanged.
The Q89 merge at ledger 2026-10-19 00:40 was a stage-1 split, not a Lean statement:
the current live node has `reviewed` by Q89 but no `lean` or `reviewed_lean`. This
delivery builds on that reviewed eight-step proof, including its resolution-independence fix.

Hypothesis and conclusion correspondence:

- Small site in the chosen universe: `{C : Type u} [SmallCategory C]` and
  `(J : GrothendieckTopology C)`. This is the topology/sheaf component of the
  recorded site convention, with site objects, arrows, coefficient rings and
  modules all small in the chosen universe `u`; no further covering axiom is
  used in the claim. The metatheoretic size convention has no declaration to apply.
- Commutative ring sheaf: `(R : Sheaf J CommRingCat.{u})`. The canonical
  `sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})` forgets commutativity
  solely to use the recorded `ringedSiteModules` category, whose objects and
  arrows are exactly Mathlib's `SheafOfModules` objects and linear maps.
- Module sheaf F and a set-indexed family E: `F : ringedSiteModules.{u} ...`,
  `{I : Type w}` and `E : I → ringedSiteModules.{u} ...`. The independent `w`
  allows a family indexed by any set; only the coproducts used in K are small.
- The specified injective resolution is `(P : InjectiveResolution F)`, the
  dependency's bundled nonnegative resolution. Its complex `P.cocomplex` has
  injective terms and the quasi-isomorphic augmentation from F in degree zero.
  This binds an arbitrary choice of the resolution used in the node's Ext
  definition, not an additional property of F. Existence follows from enough
  injectives; changing the resolution does not change vanishing.
- Positive Ext vanishing for every family member is exactly `hExt`: for each
  `i : I`, `p : ℕ` and `0 < p`, the homology in degree p of the complex obtained
  by applying `preadditiveCoyoneda.obj (op (E i))` to `P.cocomplex` is `IsZero`.
  This additive functor has object Hom(E_i,-) and differential postcomposition,
  so these groups are exactly the resolution-defined Ext in the node.
- The cochain complex of module sheaves is `K : CochainComplex (...) ℤ`.
  `hbounded` says there is `b : ℤ` with `IsZero (K.X n)` for all `b < n`.
  `hacyclic : K.Acyclic` is the recorded exactness-at-every-degree condition,
  equivalent to zero homology sheaves in every degree.
- The term condition `hterms` binds, independently in each degree, `A : Type u`
  and an arbitrary function `i : A → I` with `Nonempty (K.X n ≅ ∐ ...)`.
  Arbitrary `i` allows repetitions; no injectivity, surjectivity, or nonemptiness
  is required. `A : Type u` is precisely a small coproduct in the module universe.
- The conclusion is acyclicity of Mathlib's `CochainComplex.HomComplex K`
  into the single complex F[0]. In degree n its cochains identify additively
  with `K.X (-n) ⟶ F`, by `HomComplex.Cochain.toSingleEquiv`
  applied with `p = -n`, `q = 0` and `-n + n = 0`.
  The source declaration `HomComplex.Cochain.δ_toSingleMk`, with `n' = n+1`
  and `p' = -n-1`, identifies its differential with
  `(n+1).negOnePow • (K.d (-n-1) (-n) ≫ h)`.
  Thus it has exactly the terms and differential specified by the node;
  there is no alternate unsigned Hom convention or sheaf-valued internal Hom.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, whose documentation retains
  Mathlib `GrothendieckTopology` and `Sheaf` for the topology and sheaf components.
- `def-weil-size-convention` is explicitly metatheoretic; `universe u w` and
  the small category/module binders realize it without a new object.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation of `SheafOfModules`; its full source and the
  underlying Mathlib sheaf/module and morphism structures were read.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `CategoryTheory.Injective` and `CategoryTheory.InjectiveResolution`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.Acyclic`, `ExactAt`, `homology`,
  `exactAt_iff_isZero_homology`.

All recorded proof-dependency modules are imported without `public`, including
`RingedSiteModulesGrothendieckOfUniverses.isGrothendieckAbelianOfUniverses`
(the declaration's namespace is `SheafOfModules`), Mathlib's Grothendieck enough
injectives, `InjectiveResolution.isoRightDerivedObj`, degree-zero cycles and
`Functor.rightDerivedZeroIsoSelf` in `Mathlib.CategoryTheory.Abelian.RightDerived`,
`instAB4StarAddCommGrpCat`, `HomologicalComplex₂.firstFiltration` and
`secondFiltration`, `HomologicalComplex₂.exists_spectralSequence`, and
`CategoryTheory.first_quadrant_row_collapse`. The theorem docstring carries all
current eight proof steps and the named inputs; no proof is supplied in stage 2.

Edge cases checked mathematically:

- Empty `I`, and empty termwise coproducts `A`: both are allowed; K has zero
  terms in the former case, and Hom is acyclic. No `Nonempty` index assumption.
- Repetitions: `i : A → I` may be constant or noninjective.
- K=0 and F=0: both remain included, as do the zero coefficient ring and an
  empty site. No nontriviality or nonempty-site binder.
- The two-term identity complex is acyclic with acyclic Hom in all degrees.
- The bound b is any integer, so shifting across degree zero is allowed.
  The Ext condition excludes p=0, but the conclusion includes degree zero and
  all negative degrees. The proof uses the full row-collapse edge isomorphism.
- For the exact complex Z --2--> Z --> Z/2, Hom(-,Z) is not acyclic;
  the Ext hypothesis correctly fails on Z/2. Thus termwise Ext orthogonality
  is not accidentally omitted or replaced by acyclicity alone.
- No claim of sectionwise exactness of K is made: acyclicity is in the abelian
  category of sheaves, and the row proof uses injectivity there.

Searches performed on 2026-10-19:

- `msearch.py ... leanfinder "Hom from a bounded above acyclic complex of
  coproducts of Ext orthogonal sheaf modules into F is acyclic"`: eight hits
  about K-injective/K-projective complexes, injective dimension and existence
  of Ext; none is this bounded-above termwise Ext-orthogonality theorem.
- `msearch.py ... loogle '"Ext", "Acyclic"'`: zero hits.
- `msearch.py ... leansearch "Hom from a bounded above acyclic complex whose
  terms are coproducts of Ext orthogonal objects into F is acyclic"`: eight
  hits on K-injectivity, K-projectivity and definitions of acyclicity; no match.
- `msearch.py ... grep 'Ext.*[Aa]cyclic|[Aa]cyclic.*Ext|[Aa]cyclic.*[Hh]om|[Hh]om.*[Aa]cyclic'
  Algebra/Homology`: 25 hits, mainly derived categories and K-injectivity;
  none gives the theorem.
- `rg` in the pinned upstream `WeilConjectures/` and side `lean/Sheaf/` for
  the item id, acyclic Hom, coproduct acyclicity and HomComplex: no declaration
  for this lemma. `ContinuousCocontinuousDerivedShriek.lean` mentions the node
  only as a proof input. Mathlib's existing HomComplex, `toSingleEquiv` and
  `δ_toSingleMk` provide the exact construction and sign formula needed here.

Source checked directly: `literature/stacks-project/sites-cohomology.tex`,
`example-hom-complex-into-sheaf` at lines 8172 onward (07AA), and the
free-sum Ext vanishing and concluding spectral-sequence argument at lines
9380 onward in `lemma-existence-derived-lower-shriek` (07AC).

No new nodes, dependency repairs, statement correction, or STATEMENT-DISPUTED.
Compilation: prescribed `scompile.py` passed both sandbox and named library
module, with no errors or warnings (2.8 s / 2.9 s). `autoImplicit false` is set.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
