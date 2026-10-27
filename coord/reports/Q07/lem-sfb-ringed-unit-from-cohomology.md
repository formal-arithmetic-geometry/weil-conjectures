## Worker report

The module `Sheaf.SixFunctors.RingedUnitFromCohomology` states
`CategoryTheory.ringedUnitFromCohomology`, with its sole proof `sorry`. The helper
`CategoryTheory.exactRingedDerivedAdjunction` has real data: it specializes the
existing upstream exact-left/right-derived adjunction and installs K-injective
resolutions from the proved Grothendieck-abelian theorem. It introduces no new
mathematical notion, chosen functor, comparison, or arbitrary map. No node
statement was corrected and no dependency record was repaired.

Source read: `literature/stacks-project/sites-cohomology.tex`, lines 6368–6396,
Tag 0D7T, `lemma-bounded-in-image-downstairs`, full statement and proof.
The node already expresses flatness as exactness of module pullback. Its proof
is reproduced step by step in the theorem docstring. The theorem does not claim
that a finite cohomological dimension or an upper bound is needed.

Hypothesis and clause correspondence:

- Sites and size: `{C D : Type u} [SmallCategory C] [SmallCategory D]` and
  `J`, `K : GrothendieckTopology ...` present sites small in the module universe
  `u`. Enlarging `u` covers the fixed-universe convention. The two derived
  localization universes `wA`, `wB` are independent. `HasDerivedCategory` binds
  the standard localization, not a modified derived category.
- Commutative coefficient rings: `O : Sheaf J CommRingCat.{u}` and
  `R : Sheaf K CommRingCat.{u}`. The displayed `sheafCompose` forgets only
  commutativity to pass these sheaves to the existing ringed-topos/module APIs.
  No independent RingCat sheaf or unspecified coefficient action is supplied.
- The morphism of ringed topoi is `f : RingedToposMorphism ... ...`, the
  recorded declaration. Its inverse image, direct image, structural ring map,
  and induced module direct image are exactly its recorded fields. No functor
  on the presenting sites is imposed.
- Module categories are exactly `ringedSiteModules.{u,u,u,u}`; this is the
  recorded transparent abbreviation for Mathlib's `SheafOfModules`.
- Ordinary module pullback is supplied as `F : Mod(R) ⥤ Mod(O)` together with
  `adj : F ⊣ f.modules`. This is the universal characterization of the module
  pullback, unique as an adjoint up to its canonical adjoint isomorphism. It
  does not replace the induced direct image by an arbitrary additive functor.
  Binding the existing adjunction avoids constructing a second tensor pullback.
- Exactness is `[F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]`, precisely the exact additive functor used in the
  node's first proof step. There is no exactness assumption on `f.modules`.
- The derived pullback is `F.mapDerivedCategory` and direct image is
  `f.modules.rightDerivedFunctor`, from the result type of the helper.
  `SheafOfModules.isGrothendieckAbelian` supplies the existing Grothendieck
  instance locally inside the definition, and
  `Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian` supplies K-injective
  resolutions. Neither is an extra hypothesis of the theorem.
- The unit and counit are the actual fields of
  `adj.mapDerivedCategoryRightDerivedAdjunction`, the canonical construction
  by derived functor factorization, as exposed by the helper. The counit is
  introduced by this adjunction and is not an additional asserted conclusion.
- The complex is `K₀ : DerivedCategory (Mod(R))`. Its bound is `a : ℤ` and
  `hbelow : ∀ q : ℤ, q < a → IsZero ((homologyFunctor ... q).obj K₀)`.
  This matches exactly vanishing below some integer, without excluding
  negative bounds or imposing any upper bound.
- The premise `hcoh` quantifies over every integer `q`. It evaluates the same
  canonical unit at `(DerivedCategory.singleFunctor ... 0).obj
  ((DerivedCategory.homologyFunctor ... q).obj K₀)`, exactly `H^q(K)[0]`.
- The conclusion is `IsIso ((exactRingedDerivedAdjunction O R f F adj).unit.app K₀)`,
  exactly invertibility of the canonical unit on the original complex.

Dependency declarations and modules read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  including its full structural map, scalar-linearity and induced module fields.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: recorded
  `Precoverage.IsSiteForCoverings`; retained as the statement dependency import.
  The theorem itself uses its retained Mathlib `GrothendieckTopology`/`Sheaf`
  components, with no unnecessary choice of a precoverage presentation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and `Qh`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its localization comparison.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors` and their
  triangulated and shift structures.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `Functor.homologyFunctorIso` and `preservesHomologyOfExact` (proof dependency).
- `Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds`:
  `CategoryTheory.exactDerivedAdjunction_isGE` (proof dependency).
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.Plus`, `isGE_iff` (proof dependency).
- `Mathlib.CategoryTheory.Shift.Adjunction`:
  `Adjunction.rightAdjointCommShift`, `commShift_of_leftAdjoint` and
  `CommShift.compatibilityCounit_of_compatibilityUnit` (proof dependency).
- `Mathlib.CategoryTheory.Triangulated.Adjunction`:
  `Adjunction.isTriangulated_rightAdjoint` (proof dependency).
- `Sheaf.CategoryTheory.HeartTestBoundedBelow`:
  `DerivedCategory.Plus.heart_test_bounded_below` (proof dependency).
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`; its full source
  construction was read, including the two absolute derived-functor instances.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  `Functor.rightDerivedFunctor`, `rightDerivedFunctorUnit`, and the K-injective
  comparison instance, read through the preceding canonical adjunction import.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`:
  `SheafOfModules.isGrothendieckAbelian`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

Edge cases checked against the source and signature: the zero object and zero
coefficient ring are permitted; identity morphisms give the usual identity unit;
a sheaf shifted to any positive or negative degree is covered; `a` may be
negative; cohomology above every finite bound is allowed; arbitrary geometric
morphisms need not come from a site functor. Independent derived localization
universes avoid silently equating the two Hom-size bounds. All variables and
universes are bound explicitly, and `autoImplicit` is false.

Searches actually run using the prescribed msearch wrapper:

- LeanFinder: “For an exact pullback of ringed topoi, the canonical derived
  adjunction unit is invertible on a bounded below complex if it is invertible
  on every cohomology sheaf”. Eight hits, including module pullback unit and
  `Adjunction.derived_unit` constructions; no theorem stating the criterion.
- LeanSearch: “A derived adjunction unit is an isomorphism on a bounded below
  complex if it is an isomorphism on its cohomology objects”. Eight hits on
  derived units and adjunctions, no criterion on cohomology objects.
- Loogle: `"Adjunction", "unit", "DerivedCategory"`: zero hits.
- Mathlib grep: `(unit|Unit).*(cohomology|bounded)|bounded.*(unit|Unit)` in
  `Algebra/Homology`: zero hits.
- Project rg: node ID and `ringed.*unit|unit.*cohomology` in `lean/WeilConjectures`
  and `lean/Sheaf`; no existing declaration states this ringed-topos criterion.
  Related unit normalization and projection statements were inspected.
- Targeted project rg found the upstream exact-left/right-derived adjunction,
  which is reused instead of copied. `dag/lean_names_upstream.json` contained
  no occurrence of the item ID.

Compiler validation uses only the prescribed `scompile.py`. Initial probes
exposed public-import visibility and an inconsistent redundant Abelian instance;
the final module relies on the canonical Mathlib instance and public imports.
The statement module compiled in both sandbox and final module modes without
errors or warnings. Dry-run and final delivery results follow below.

## Second reading by Q07

Fresh self-reading of the source, node, and final module; no other agent was
started, as required by the dispatcher brief. Independent maintainer review
remains the final mathematical review.

The first draft allowed an arbitrary RingCat sheaf and explicitly supplied
K-injective and Abelian instances. The final reading removed those mismatches:
coefficients are commutative sheaves, their underlying RingCat sheaves are
literal forgetful images, module abelianness is Mathlib's canonical structure,
and K-injective existence is obtained from the existing Grothendieck theorem
inside the fully defined helper. There are no default-valued coefficient
parameters that could be overridden by unrelated rings. The final two
localization universes are separate.

Compared each clause once more: small sites and commutative rings; geometric
ringed-topos morphism with induced module direct image; an ordinary left
adjoint with exactly additive finite-limit/finite-colimit exactness; its
termwise derived pullback and K-injective right derived direct image; the
canonical derived adjunction; all-integer lower-bound vanishing; all-integer
unit invertibility at cohomology in degree zero; and unit invertibility at K.
All are rendered as listed above. The helper installs only a proved resolution
structure and the existing canonical adjunction. Its data contain no sorry;
exactly one theorem remains postponed, with this node and its complete proof
docstring. No statement change, new definition node, or disputed statement.
