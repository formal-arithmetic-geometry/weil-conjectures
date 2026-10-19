## Worker report

The module `Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation` states
`CategoryTheory.topos_localization_site_presentation`, with a single `sorry` and
no definitions or helper theorems. The item's natural-language statement and all
other node fields remain unchanged. There are no new nodes or dependency repairs.

Source checked: `literature/stacks-project/sites.tex`, lemma-topos-good-site
(Tag 03CI), clauses (1), (3), (5) and its full-subcategory construction, and
lemma-localize-topos (Tag 04GZ), especially the product inverse image and transport
through sheaves over a representable. The module docstring and theorem docstring
identify these sources; the theorem docstring carries all six DAG proof steps.

Clause-by-clause rendering:

- The category is `(E : Type u) [Category.{v} E]`. The sole mathematical hypothesis
  is `hE : IsGrothendieckTopos.{w, v, u} E`, exactly the recorded small-site topos
  predicate. The object `(A : E)` is completely arbitrary.
- The universe convention is explicit `universe w v u`. The presenting category
  `C : Type w`, `c : SmallCategory C`, and coefficient category `Type w` use the
  same bound `w` as that predicate. Neither `u` nor `v` is identified with `w`.
  The size-convention node is metatheoretic and has no declaration to import.
- A small covering-family site is supplied by existential `C`, `c`,
  `K : @Precoverage C c`, and `hK : @Precoverage.IsSiteForCoverings C c K`.
  Its topology and sheaf category use the recorded convention
  `K.toGrothendieck` and `Sheaf K.toGrothendieck (Type w)`.
- Finite limits are the existential `hC : @HasFiniteLimits C c`.
  Subcanonicity is `hJ : ...Subcanonical ... K.toGrothendieck`, the existing
  Mathlib property equivalent to all representables being sheaves.
- The equivalence is `e : E ≌ Sheaf K.toGrothendieck (Type w)`. An equivalence
  of categories between topoi is an equivalence of topoi: its two adjoint
  equivalence functors preserve finite limits. Thus a second, arbitrary geometric
  equivalence datum would add no content and is not substituted for `e`.
- The existential `U : C` and
  `Nonempty (e.functor.obj A ≅ (...GrothendieckTopology.yoneda ... hJ).obj U)`
  give the precise representability assertion. This is the ordinary Yoneda sheaf,
  with sections `V ⟶ U`; there is no universe lift, chosen unrelated presheaf,
  or assumption that A was already representable.
- `s : Over A ≌ Sheaf (K.toGrothendieck.over U) (Type w)` is the required
  equivalence from the original slice to the localized sheaf category.
  The slice is Mathlib's existing `Over`, not a privately introduced category.
- The localized topology is the recorded `GrothendieckTopology.over`. Its definition
  is `sieves Y := Sieve.overEquiv Y ⁻¹' J Y.left`, hence exactly the dependency's
  stated equivalent sieve criterion: an underlying generated sieve covers in the
  base iff the corresponding sieve covers over U. `Sieve.overEquiv_ofArrows`
  identifies a family's sieve with that of its underlying family. For literal
  covering presieves, the localized precoverage is `K.comap (Over.forget U)`;
  sheaves use its induced topology. No additional covering property is postulated
  as a tautological conjunct.
- `g : GeometricMorphism (Over A) E` supplies the actual adjunction and finite-limit
  preservation of the slice inverse image. It is explicitly identified by
  `Nonempty (g.inverse ≅ @Over.star E _ A hprod)`. The source of `Over.star` says
  its value on H is `A × H ⟶ A`, with first projection and morphism part
  `prod.map (𝟙 A) f`. Symmetry of products identifies this with the node's
  `H × A ⟶ A` and second projection. This is the same canonical functor up to
  natural isomorphism, not a replacement by an unconstrained inverse-image functor.
- `hprod : HasBinaryProducts E` is existential in the conclusion, supplying the
  product structure for `Over.star`; it is not a hypothesis on the input topos.
  Such products are transported from the sheaf presentation in `hE` and do not
  restrict the allowed topoi or objects.
- Finally,
  `Nonempty (g.inverse ⋙ s.functor ≅
    e.functor ⋙ K.toGrothendieck.overPullback (Type w) U)`
  states the entire functorial compatibility. `overPullback` is the dependency's
  restriction by precomposition with `(Over.forget U).op`, with value F(V) at
  V → U, on both objects and morphisms. It is not merely objectwise compatibility.
  The product identification and this commuting square share the same g, e and s.

Recorded statement dependency interfaces read and used:

- `def-weil-pbc-topos`: `Sheaf.CategoryTheory.Sites.GrothendieckTopos`,
  `CategoryTheory.IsGrothendieckTopos` (full definition read).
- `def-weil-size-convention`: its recorded metatheoretic convention, implemented
  by the independent explicit universe parameters described above.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings` (full predicate read).
- `def-pur-localized-ringed-site`: `Mathlib.CategoryTheory.Sites.Over`,
  `CategoryTheory.GrothendieckTopology.over`, `overPullback` and
  `CategoryTheory.Sheaf.over`. The recorded main module
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and its
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, and
  `overFunctorMap` were also read. Only the underlying set-sheaf restriction is
  needed here, so the smaller defining module `Mathlib.CategoryTheory.Sites.Over`
  is imported, using exactly those recorded constructions.
- `def-trf-geometric-morphism`:
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism`, with fields `inverse`, `direct`, `adj`,
  `leftExact` (full declaration and composition/mates read).

The stated proof dependencies are imported without `public`:
`ContinuousCocontinuousToposAdjunctionForCoverings`,
`Sites.LocalizedSheavesOverRepresentable`, `SheafSubcategoryComparison`,
`Mathlib.CategoryTheory.Sites.Limits`, and
`Mathlib.CategoryTheory.Sites.Sheafification`.
The sieve-to-covering-site prerequisite `lem-trf-sieve-sheaves-covering-site` has
no Lean record yet, so there is no existing module to import. It is a proof
prerequisite only; the statement neither assumes its conclusion nor needs a new
notion from it. Its role remains explicitly in the proof docstring and DAG.

Edge cases checked before finalizing the statement:

- A may be initial, terminal, subterminal, or any other object; no inhabitance,
  nonzero, or subterminal assumption is present.
- For initial A, the slice and localized sheaf category can both be degenerate;
  no hypothesis excludes the empty-cover phenomenon that makes this possible.
- All covering-family index sets, including empty ones, remain available in the
  precoverage predicate. There is no nonempty-index restriction.
- An empty category E cannot satisfy `hE`, since a sheaf category has a terminal
  sheaf. No extra nonemptiness hypothesis is therefore needed. The output site
  has a terminal object by hC, exactly as the source requires.
- The original presentation in hE may lack pullbacks or be non-subcanonical;
  neither property is imposed on that input site. Finite limits and subcanonicity
  belong only to the newly produced site.
- Object and Hom universes of E are independent, and all output site objects,
  Hom sets and section sets obey the original w bound. No extra universe equality
  is introduced to use an API.

Searches for an existing theorem or canonical notion:

- `msearch.py`, LeanFinder:
  "Every Grothendieck topos admits a small subcanonical finite limit site
  presentation representing a specified object and its slice". Eight results:
  `GrothendieckTopology.Subcanonical`, its canonical-topology instance,
  `hasLimitsEssentiallySmallSite`, point/finite-limit declarations and coherent
  topology results. None constructs the adapted presentation.
- `msearch.py`, LeanSearch:
  "A Grothendieck topos has a small finite limit subcanonical site presentation
  representing a given object and localization identifies slice sheaves".
  Eight results, consisting of Subcanonical APIs, sheaf limit APIs and the
  Grothendieck-abelian theorem. No exact match.
- `msearch.py`, Loogle: `CategoryTheory.Over.star`. Twelve results give the existing
  canonical product-to-slice functor, its adjunction with forgetful, its object
  and morphism formulas, pullback compatibility and cover preservation. Its full
  source/docstring was read; it is reused without a new definition.
- `msearch.py`, grep:
  `IsGrothendieckTopos|subcanonical|overPullback|def star` in
  `CategoryTheory/Sites`. Results identify Subcanonical, Yoneda, Over and
  overPullback APIs; none is the target theorem.
- `rg` of the upstream `WeilConjectures`, project `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `topos_localization_site_presentation`,
  `IsGrothendieckTopos`, `lemma-topos-good-site`, and the item's exact DAG id.
  No existing target declaration; the topos predicate and some topoi built from
  sites are present, but do not assert this adapted small-site presentation.
- Direct reads of Mathlib's `Sites/Canonical.lean`, `Sites/Over.lean`,
  `Sites/Limits.lean`, and `Comma/Over/Pullback.lean` verify the precise canonical
  definitions used above. No duplicate definition is introduced.

Validation: the final module compiles cleanly using the prescribed `scompile.py`,
including compilation as its final library module. Every theorem proof is `sorry`;
there is exactly one. There are no auxiliary data definitions, no extra axioms,
no auto-bound variables, and no remaining diagnostics. There is no
STATEMENT-DISPUTED issue or statement correction.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
