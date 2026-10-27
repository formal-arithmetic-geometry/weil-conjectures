## Worker report

The module `Sheaf.CategoryTheory.BoundedHomLocalizationEmbedding` states
`CategoryTheory.boundedHomLocalizationEmbedding`. Its proof is `sorry`.
The public helper `CategoryTheory.RawScalarLocalizationEmbedding` is a fully written
Prop-valued definition packaging the raw-functor clauses of this same node; it constructs
no unspecified data. There are no additional nodes or dependency repairs. The item JSON
changes only `lean`.

Source read: Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 6.8.12 on
printed page 61 and Proposition 6.8.14(2), including its proof, on printed pages 61–62
(local PDF, pdftotext pages 61–63). The proposition explicitly deduces full faithfulness
from Lemma 6.8.12 and treats essential surjectivity separately. The DAG node abstracts
exactly that full-faithfulness implication under the stipulated continuity assumptions.
The Lean does not assert essential surjectivity.

Hypothesis and clause correspondence:

- Small site: `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`. The topology
  is the existing Mathlib representation of the sheaf category. This is the existing
  small-site interface retained publicly by the recorded site/localization dependencies.
- Commutative coefficient ring and scalar: `(A : Type v) [CommRing A]` and `(t : A)`.
  No nonzero, non-zero-divisor, domain or invertibility hypothesis is imposed.
- Sheaf of commutative A-algebras: `(R : Sheaf J CommRingCat.{u})` and the ring map
  `a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)`.
  The latter gives the compatible sectionwise algebra structures, including the
  empty-site case. The ring and site universe can always be enlarged together;
  the external coefficient ring and derived Hom universes remain explicit `v,w`.
- Module sheaves: `ringedSiteModules.{u}` is transparently the existing `SheafOfModules`.
  `DerivedCategory` and the two `HasDerivedCategory.{w}` binders give the actual ordinary
  unbounded derived categories in the chosen Hom universe, without a new category or
  a chosen Abelian instance.
- Sheafified section localization: `ringedLocalizationRing R (a t)` and its canonical
  `ringedLocalizationRingUnit`. These are the retained SmallCategory construction in
  the recorded `RingedSectionLocalizationOfUniverses` module; that module generalizes,
  rather than replaces, this interface.
- Actual scalar localization: `E` is pinned on objects by `hE` to
  `SheafOfModules.changeOfRings (ringedLocalizationRingUnit R (a t))`, and on every
  morphism by `hmap` to its sheafified tensor map. The additive and finite-limit/
  finite-colimit preservation instances spell out the stipulated exactness. These
  are not an arbitrary replacement functor or additional mathematical restrictions:
  the published `scalarLocalization_exact` supplies them for this actual functor.
  `F` in the node is precisely `E.mapDerivedCategory` throughout the conclusion, with
  its canonical `CommShift ℤ` instance from the termwise derived construction.
- Full A-linear subcategory: `P : ObjectProperty (DerivedCategory ...)` defines
  `P.FullSubcategory`, whose morphisms and A-linear structure are inherited from the
  ambient category. `hshift` states closure under every integer shift; `hbounded`
  states `∀ K, P K → ∃ b : ℤ, K.IsGE b`. The lower bound may depend on K.
- Countable common-lower-bound continuity: `hcontinuous` uses the published
  `DerivedCategory.CountableBoundedBelowHomContinuous`. I read its definition:
  it quantifies all ℕ-families, all common bounds, every coproduct cofan with its
  `IsColimit` witness, and every integer q. Its map is exactly the sum of composition
  with the shifted coprojections. Bijectivity of this additive map is equivalent to
  its being an isomorphism of A-modules. An arbitrary small countable index set
  injects into ℕ: reindex the family and put zero objects at unused indices. Coproducts,
  the common bound and the comparison are preserved. Thus this existing ℕ formulation
  includes finite and empty countable families and does not restrict the node.
- All localized shifted Hom isomorphisms: the first conjunct is the existing
  `scalarLocalizationHomComparison A t E.mapDerivedCategory P P`. Its existential
  `e K hK L hL q` is a `scalarLocalizationHomEquiv`, i.e. a genuine
  `LocalizedModule.Away t (K ⟶ L⟦q⟧) ≃ₗ[Localization.Away t]
  (F.obj K ⟶ (F.obj L)⟦q⟧)` with the canonical localized module structure.
- Actual map on every fraction: that predicate's first equation uses
  `LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩` and sends it to
  `(IsLocalization.Away.invSelf t)^n • (F.map f ≫ (F.commShiftIso q).hom.app L)`.
  Thus the target is FL[q] with the stated shift comparison, not F(L[q]) with an
  arbitrary identification.
- Naturality: its next equation simultaneously quantifies integral precomposition
  `f : K' ⟶ K`, postcomposition `g : L ⟶ L'`, an arbitrary numerator and denominator,
  and all q. Taking either arrow to be an identity gives each explicit formula in
  the node. Linearity and the fraction relation extend these to every localized arrow.
- Simultaneous shifts: the last comparison equation uses `shiftFunctorComm` and
  `F.commShiftIso` on both endpoints for all two integers p,q. The explicit hshift
  hypothesis keeps shifted endpoints in P. The identity and graded-composition clauses
  of the same predicate include canonical zero/addition identifications as required.
- Raw localization Q: `ScalarLocalization A P.FullSubcategory t` and its existing
  `ScalarLocalization.localization` retain all objects, use tensor Hom modules and
  perform no idempotent completion. The scalar-first tensor order is canonically
  the node's Hom-first order via `TensorProduct.comm`.
- Degree-zero functor J: `RawScalarLocalizationEmbedding` asserts an actual functor
  `J : ScalarLocalization A P.FullSubcategory t ⥤ D(R_t)`, its additivity,
  `J.Linear (Localization.Away t)`, `J.Full` and `J.Faithful`.
- Objects: `hobj : ∀ K, J.obj ⟨K⟩ = F.obj K.obj` is precisely J(QK)=FK.
  `eqToHom` only transports along these endpoint equalities in the map formulas.
- Functor fractions: the first equation in the raw predicate sends
  `(invSelf t)^n ⊗ₜ[A] f` to `(invSelf t)^n • F.map f.hom`, after the hobj transports.
  It is therefore the degree-zero Hom comparison after the canonical shift-zero
  identification: both are linear and agree on all fractions, so are the same map.
- Coverage of every localized morphism: the next conjunct quantifies an arbitrary
  raw arrow z and gives `∃ f n, z = (invSelf t)^n ⊗ₜ[A] f`. The tensor/fraction
  identification in node proof step 2 proves exactly this coverage. No restriction
  to an integrally generated subset or essential image is made.
- Identity and composition: the last two conjuncts explicitly state transported
  `J(Q.map (𝟙 K)) = 𝟙 (F.obj K.obj)` and the two equalities identifying J of a
  composition of fractions with `invSelf t^(m+n) • F.map (f.hom ≫ g.hom)` and with
  the composition of the two scaled F maps. Lean writes composition left-to-right,
  so its f≫g is the node's gf. The target is the entire ambient derived category.

The canonical scalar structures are installed only in the conclusion by the same
instance-lambda technique as the published comparison theorem:
`scalarLocalizationDerivedLinear A R a` on the source and
`scalarLocalizationDerivedLinear (Localization.Away t) (ringedLocalizationRing R (a t))
(scalarLocalizationCoefficientMap A R a t)` on the target. No arbitrary linear
structure is a hypothesis, and there are no `let` binders in the theorem statement.

Dependency declarations inspected and reused:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`, retaining
  Mathlib `GrothendieckTopology`/`Sheaf` for the site's sheaf categories.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`; and `.TStructure`:
  `DerivedCategory.IsGE`, `isGE_iff` identifies lower bounds with cohomology vanishing.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`, publicly retaining
  `.RingedSectionLocalizationRing`: `ringedLocalizationRing`,
  `ringedLocalizationRingUnit`, their actual sectionwise localization/sheafification.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, retaining
  `.SiteTensorFunctoriality` and the upstream tensor constructions;
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  `SheafOfModules.changeOfRings`, `changeOfRingsHom` (full definitions read).
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`:
  `CategoryTheory.Functor.exactFunctor_derivedFunctor`; the inherited Mathlib
  `Functor.mapDerivedCategory` fixes the termwise derived functor and shift comparison.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`, `.localization`,
  `.category`, `.preadditive`, `.linear` and the tensor composition/identity formulas.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`, its inherited
  full-subcategory instance; `.LinearFunctor`: `Functor.Linear` and additive functors.
- `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`: `scalarLocalization_derivedHom`,
  `scalarLocalization_exact`, `scalarLocalizationHomComparison`, `scalarLocalizationHomEquiv`.
  Its public imports provide `CountableBoundedBelowHomContinuous` from
  `.BoundedBelowCountableHomContinuity`, and `scalarLocalizationDerivedLinear` /
  `scalarLocalizationCoefficientMap` from `.ScalarLocalizationCoefficientActions`.
- Proof-only imports of `Mathlib.LinearAlgebra.TensorProduct.Tower`
  (`LinearMap.baseChange`, tensor extension) and `Mathlib.Algebra.Module.LocalizedModule.Basic`
  (`LocalizedModule.Away`, `mkLinearMap`, `IsLocalizedModule.lift`) retain the other
  two proof dependencies. All statements have the node's full natural-language proof.

Edge cases checked before writing and during the second pass: t=0 or nilpotent
(localized scalar ring and both sides of Hom comparisons are zero), t=1/unit
(localization is unchanged), t a zero-divisor (the full fraction relation is used),
zero coefficient ring, empty site, empty P, zero objects when present, q=0 and arbitrary
negative/positive q,r, n=m=0, finite/empty countable families, different lower bounds
for different members of P. No condition excludes any of them. No essential surjectivity,
Noetherian, constructibility, scheme or idempotent-completeness hypothesis/conclusion
is introduced. There is no statement fault or disputed statement.

Searches actually run with msearch.py Q124 lem-per-bounded-hom-localization-embedding:

- leanfinder: "Scalar localization of a full shift stable subcategory of bounded below
  derived sheaf modules with countable Hom continuity is fully faithful". Eight hits:
  locally constant condensed/light-condensed module functors, fully faithful forgetful
  functors for sheaf modules and schemes, and fully faithful sheaf composition functors.
  None states this conditional raw embedding.
- loogle: "CategoryTheory.Functor.Full, CategoryTheory.Linear". Four hits:
  Functor.linear_of_full_essSurj_comp, Functor.linear_comp_iff_of_full_of_essSurj,
  full_linearCoyoneda, full_linearYoneda. These do not give the ringed-site comparison.
- grep: "scalar.*localization|localization.*fullyFaithful", Mathlib CategoryTheory.
  Two hits in Localization/LocalizerMorphism and Abelian/SerreClass/Localization;
  generic categorical localization results, not the node.
- leansearch: "Raw scalar localization of a bounded below Hom continuous full subcategory
  embeds fully faithfully into the derived category of localized sheaf modules".
  Eight hits including HasDerivedCategory.standard, derived-category localization
  instances and their whiskering functors, Bousfield localization and subcanonical
  Yoneda. No exact match.
- rg of `lean/WeilConjectures` for scalar localization, localization fullyFaithful,
  CountableBoundedBelowHomContinuous and the proposed declaration names; grep -rn
  of the exact item id there. No occurrence of this item or its statement. Existing
  derived rationalization/extension-of-scalars results are for different categories.
- rg of `lean/Sheaf` for the item/declaration names, CountableBoundedBelowHomContinuous
  and scalarLocalizationHomComparison found the existing pairwise comparison,
  its continuity definition and ConstructibleRationalHomComparison. The latter is
  specialized to completed constructible pro-etale coefficients; it does not state
  this arbitrary-ringed-site raw-subcategory theorem. Reused those generic interfaces
  instead of duplicating them.

Validation: the server scompile.py accepted both sandbox and library module modes,
with no errors or warnings (20.3 s and 16.3 s). An initial parser-precedence issue in
power/tensor expressions was corrected by parenthesizing each inverse power before
`⊗ₜ`; it did not change the mathematical statement. The final additional proof-only
imports are checked again by the mandatory delivery preflight and per-file compile.

## Second reading by Q124

Author's second pass, with the node, source and final file open; the maintainer supplies
independent review as specified by the worker brief. No other agent was started.

I matched the small site, A-algebra action, t, section localization and exact E to the
node. hE and hmap fix both object and morphism parts of scalar extension; the conclusion
uses only its canonical mapDerivedCategory shift comparisons. I unfolded the published
comparison predicate: it gives all q, the precise fraction formula, pre/postcomposition,
identity, graded composition and simultaneous shifts, specialized to P in both slots.
I checked that P.FullSubcategory has the inherited ambient Hom, rather than an arbitrary
A-linear category. hbounded uses a separate bound for each object, and hcontinuous's
ℕ indexing includes every countable family by reindexing and zero padding. Empty families
are included. hshift is explicitly quantified over every integer.

I then read the new raw predicate independently of the prose: J has the raw tensor-Hom
source, hobj fixes all objects, the first equation fixes every fraction and agrees with
Φ in degree zero, the next equation covers every raw arrow, and the last two give the
identity/composition formulas with the correct left-to-right Lean order and m+n exponent.
Full, Faithful, Additive and Linear are all asserted of the same J. There is no
idempotent completion or essential-surjectivity clause. The only change found in this
pass was to add direct proof-only imports for the module-base-change and module-localization
proof dependencies; the signatures needed no mathematical correction. All data in the
helper definition are an explicit proposition; the sole theorem remains sorry.
