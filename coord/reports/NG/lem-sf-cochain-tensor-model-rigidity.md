## Worker report

The module `Sheaf.Algebra.Homology.CochainTensorModelRigidity` states
`SheafOfModules.cochain_tensor_model_rigidity`. Its sole postponed proof is `sorry`.
The supporting definitions expose the existing homotopy-descent packet, its canonical
quotient on representatives, and the explicit comparison component. There is no new
independent notion, tensor construction, arbitrary comparison-map hypothesis, or
functorial resolution choice. The node statement and dependencies are unchanged.

Hypothesis and clause correspondence:

- The site is `{C : Type u} [Category.{v} C]`, with topology `J` and
  `[EssentiallySmall.{w} C]`; the commutative coefficient sheaf is
  `R : Sheaf J CommRingCat.{w}`. Site object, morphism, and coefficient universes
  remain independent. `[HasDerivedCategory.{d} (SheafOfModules ...)]` chooses
  the morphism-size convention for the existing unbounded derived category.
- The category of module sheaves is Mathlib `SheafOfModules`, definitionally the
  category exposed by `CategoryTheory.ringedSiteModules`. Complexes are
  `CochainComplex ... ℤ`; the functors `DerivedCategory.Q`, `DerivedCategory.Qh`,
  and `HomotopyCategory.quotient` are the recorded localization and quotient.
- `cochainTensorFlatRepresentatives` is the full-subcategory property
  `CochainComplex.IsKFlatIndependentCoefficients ... ∧ ∀ n, IsFlatOnSite ...`.
  It uses exactly the recorded predicates. Its inclusion is `.ι`, and
  `cochainTensorRepresentativeLocalization` is `.ι ⋙ DerivedCategory.Q`.
- `cochainTensorTotal` is `Functor.uncurry.obj ((curriedTensor ...).
  map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))`. This is the signed
  direct-sum total tensor of the existing sheafified sectionwise tensor;
  its differential is d₁⊗1 + (-1)^p 1⊗d₂, with no boundedness restriction.
- `T` is exactly `siteDerivedTensorIndependentCoefficients J R`.
  `cochainTensorHomotopyRepresentatives`, `cochainTensorHomotopyTotal`, and
  the two homotopy comparison isomorphisms project the same existing descent
  packet at auxiliary transformation-test universes 0,0 as this selected T.
  The representative property is uniquely characterized by the membership
  equivalence in that packet. The tensor is characterized together with its
  quotient comparison; no data is fabricated from an uncharacterized existence.
- `cochainTensorRepresentativeQuotient` is the restriction of the actual
  homotopy quotient; its membership proof is the descent packet's exact
  characterization applied to `K.property`.
- The existential `r` has source `ι.prod ι ⋙ cochainTensorTotal ⋙ Q` and
  target `q.prod q ⋙ T`. Its first conjunct states for every representative
  pair X that `r.hom.app X = cochainTensorRepresentativeArrow J R X`.
  That arrow is the four-arrow composite in proof Step 3: the inverse of
  `quotientCompQhIso` at the total tensor, Qh applied to the inverse tensor
  comparison, the given homotopy representative comparison, and T applied
  to `quotientCompQhIso.hom` at both input complexes. Thus r is specified
  from the supplied comparison and the canonical factorization.
- For every bifunctor T' and every specified representative isomorphism r',
  the second conjunct is `∃! e : T ≅ T', r.hom ≫ whiskerLeft (q.prod q)
  e.hom = r'.hom`. Equality of forward natural transformations is equality
  of the corresponding natural isomorphisms, so this is precisely the
  stated normalization and uniqueness.
- The last conjunct quantifies over `(E : Type e) [Category.{z} E]` and every
  pair of functors U,V into E. Bijectivity of `τ ↦ whiskerLeft (q.prod q) τ`
  is full faithfulness on functor categories, including noninvertible
  natural transformations and arbitrary target-category sizes.
- No K-flat resolution functor or functorial-choice hypothesis occurs.

Dependency declarations inspected and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent Mathlib module-sheaf category.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`, and
  `DerivedCategory.quotientCompQhIso` (homotopy-to-cochain direction).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, defined by exactness of
  `siteSheafTensorRight`, with its sheafification instances.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, `cochainModulesPreadditive`, and the tensor
  colimit instances, supplying the recorded sheaf tensor at independent sizes.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  its bifunctorial form is `Functor.map₂HomologicalComplex` from Bifunctor.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`, including their full signatures,
  given comparisons and arbitrary-transformation extension clause.

Sources read: the current blueprint `def-wf-tensor-product.md`, first sentence;
Stacks `sites-cohomology.tex`, K-flat resolution and derived tensor construction
(Tags 06YS, 06YT, 06YU); the quotient/localization declarations for Tag 013H.
The theorem docstring carries all four proof steps and names the dependencies.

Edge cases checked: empty site and zero coefficient ring impose no nonempty or
nonzero assumptions; zero and unbounded complexes are included; no boundedness,
flatness of arbitrary derived objects, or finite generation is imposed. Over a
one-object field site the homotopy quotient still identifies homotopic cochain
maps, so no faithfulness of the cochain quotient is asserted. Arbitrary E needs
no additive, abelian or nonempty structure. A larger independent coefficient
universe is allowed by relative essential smallness; no site-universe equality
is imposed.

Searches performed:

- `msearch.py leanfinder`: "Precomposition with the cochain localization
  restricted to flat K-flat complexes is fully faithful and determines the
  derived tensor model uniquely". Eight hits, including derived-category
  exact-functor lifting and full/faithful restriction along Qh; none concerns
  restriction to flat-term K-flat cochain representatives with normalized
  tensor comparison.
- `msearch.py loogle`: `"Localization", "fullyFaithfulWhiskeringLeft"`.
  Two hits: the generic localization theorem and the Serre-class exact-functor
  version. Neither identifies this representative category or its cochain
  tensor comparison.
- `msearch.py grep`: `KFlat|kFlat|flatRepresentatives|resolvingRepresentatives`
  in Mathlib CategoryTheory: zero hits.
- `rg` in project Sheaf/Algebra/Homology and WeilConjectures for
  `cochain.*[Rr]epresent|[Rr]epresent.*cochain|wfTensorRepresentative|rigidity|flatKFlat|flatTerm`:
  unrelated rigidity, existing representative constructions for other nodes,
  and no statement of this node. Searching the exact node id in
  WeilConjectures returned no hits. Searching all Mathlib, Sheaf, and
  WeilConjectures for the new declaration/helper names returned no clashes.

Validation: `scompile.py NG lem-sf-cochain-tensor-model-rigidity` passed
with no diagnostics for the sandbox (40.5 s) and final library module (31.1 s),
within the unmodified 60-second limits. The draft noncomputable localization
helper was marked `noncomputable`; two helper abbreviations were changed to
definitions to avoid expensive automatic unfolding. All profiling options
were removed. The only postponed proof is the named main theorem.

No statement dispute or node correction.

## Second reading by NG

The dispatcher explicitly prohibits starting another agent; independent delivery
review is assigned to the maintainer by the task brief. No independent worker
review is claimed here. A final self-check matched every hypothesis and clause
above against the node and the Lean file, including the orientation of all four
comparison arrows, uniqueness among isomorphisms, arbitrary transformations,
and the three independent site/coefficient universes.
