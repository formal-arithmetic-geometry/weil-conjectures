## Worker report

The module `Sheaf.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange` states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_affine_locally_indEtale`.
Its only theorem has proof `sorry`; it defines no new objects. The item changes
only in `lean`. No statement correction, dependency repair, or new node is needed.

Clause-by-clause correspondence:

- A commutative coefficient ring: `(A : Type (u + 1)) [CommRing A]`.
  This is the existing module-sheaf size convention of the recorded derived-category
  and exchange-forgetting-coefficients dependencies. It includes zero rings and
  coefficients without torsion or invertibility conditions.
- Schemes and morphisms: `{X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)`.
  The Lean variable `g` is the node's `u`.
- The morphism f is quasi-compact: `[QuasiCompact f]`.
- The morphism f is quasi-separated: `[QuasiSeparated f]`.
- The base-change morphism is affine: `[IsAffineHom g]`. This does not require
  S or S' themselves to be affine.
- Locally ind-etale: `hlocal` quantifies over every `t : S'`, and supplies opens
  `V : S'.Opens`, `U : S.Opens`, membership `t ∈ V`, affine conditions on both
  `V.toScheme` and `U.toScheme`, and a map `e : V.toScheme ⟶ U.toScheme`.
  The equation `e ≫ U.ι = V.ι ≫ g` says it is precisely the restriction of g.
  `RingHom.IndEtaleAcrossUniverses e.appTop.hom` says that the induced ring map
  Γ(U,O) → Γ(V,O) is a filtered colimit of finitely presented etale algebras.
  This is the recorded ind-etale predicate, with canonical ULift transport;
  neither a separate affine chart predicate nor a different colimit definition
  has been introduced. These pointwise chart witnesses express the stated local
  condition, not global affineness of either scheme.
- The base-changed scheme is `pullback f g`; its v and f' are `pullback.fst f g`
  and `pullback.snd f g`. `IsPullback.of_hasPullback f g` supplies the canonical
  Cartesian square, and `.toCommSq` supplies its commuting square to exchange.
  There are no additional square data or projection hypotheses.
- The arbitrary bounded-below complex is
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  This is exactly the recorded module-valued encoding of modules over the
  constant ring sheaf, also used in `exchange_forget_coefficients`. It is not
  the category of modules over the scheme's structure sheaf.
- The specified arrow is
  `(derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f g).toCommSq).app K`.
  Its source is `u* Rf* K` and its target is `Rf'* v* K`, on the ordinary
  bounded-below derived category. The existing construction is the canonical
  exchange (derived from the underived adjunction mate); its resolution formula
  is the recorded `derivedExchangeTermwise`, and its coefficient compatibility
  is the recorded `exchange_forget_coefficients`. It is not an arbitrary arrow
  or merely an existence of an isomorphism between the endpoint objects.
- `IsIso` of that arrow is exactly the conclusion. No constructibility,
  Noetherian, finite-type, or coefficient-invertibility binders occur.

Statement dependency declarations read and reused:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`:
  sheafification of the constant presheaf.
- `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, with `Scheme.Etale` from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: the small etale site.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the general-site `SheafOfModules` category. The recorded coefficient-comparison
  dependency gives the existing equivalent module-valued encoding used here.
- `def-weil-pbc-scheme-conventions` is a convention record without a declaration;
  the actual conditions use Mathlib's `QuasiCompact`, `QuasiSeparated`,
  `IsAffineHom` and `IsAffine`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `RingHom.IndEtaleAcrossUniverses`: exactly the recorded ind-etale ring-map
  predicate, canonically transported to a common universe. Its underlying
  `Algebra.IndEtale` filtered presentation is in
  `WeilConjectures.RingTheory.ProEtale.IndEtale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`: chosen fibre
  product and projections. `IsPullback.of_hasPullback` gives its square.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, and its public import
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `DerivedCategoryModule` and `DerivedCategory.Plus` give the recorded category
  encoding. No torsion-cohomology condition is used.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`: existing inverse and direct images.
- `WeilConjectures.SixFunctors.BaseChange.Derived`,
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`: the specified arrow.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`,
  `AlgebraicGeometry.Etale.exchange_forget_coefficients`: its signature uses
  these same module coefficients and this same exchange construction.

Every stated proof dependency's module is also imported, privately where it
is not a statement dependency. The four proof dependencies without `lean`
records have usable Mathlib matches, not missing interfaces:
`Functor.isZero_rightDerived_obj_injective_succ` and
`instIsIsoToRightDerivedZero'` in `Mathlib.CategoryTheory.Abelian.RightDerived`,
`DerivedCategory.Plus.exists_injective_nonempty_iso` in
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`, and
`CochainComplex.IsKInjective.Qh_map_bijective` in
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` (with its Plus version
available through the imported Plus framework). The docstring carries all six
steps of the node's proof, including the acyclic-resolution comparison needed
to establish invertibility of the actual exchange for every bounded-below K.

Source check: read Stacks `etale-cohomology.tex` theorem-higher-direct-images
(Tag 03Q9), including its derived-category formula, and remark-stalk-fibre;
`sites-cohomology.tex` remark-base-change (Tag 07A7); and `algebra.tex`
lemma-quasi-finite-strict-henselization (Tag 05WR) and
lemma-base-change-strict-henselization-quasi-finite (Tag 0GIP). The qcqs strict-local
formula applies to arbitrary abelian sheaves and bounded-below complexes. The
ind-etale invariance identifies strict-local pullbacks, with no torsion condition.

Edge cases checked before writing:

- Empty S': the pointwise chart condition is vacuous as intended, and the target
  sheaf category is zero; no nonempty hypothesis is introduced.
- Empty X and the zero complex: both sides and the canonical comparison behave
  as zero objects; the statement covers them.
- Zero coefficient ring and A = Z: allowed by the binders, with no torsion or
  characteristic restrictions. Arbitrary shifts and complexes bounded below
  but unbounded above remain allowed by `DerivedCategory.Plus`.
- Identity base change and affine etale base change satisfy the chart condition;
  there is no requirement that g fail to be an isomorphism or finite presentation.
- S need not be affine, Noetherian or of finite type. Both the affine property
  of g and its pointwise chart condition are substantive; neither follows from
  the bare existence of an arbitrary morphism.
- `u` is declared explicitly, every object and map is bound, and
  `set_option autoImplicit false` forbids accidental auto-bound parameters.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`, query "For a quasi compact quasi separated scheme
  morphism derived direct image of arbitrary bounded below etale module complexes
  commutes with affine locally ind etale base change": eight results, including
  etale stability under base change and structure-sheaf module adjunctions, none
  stating this ordinary small-etale coefficient-sheaf theorem.
- `msearch.py leansearch`, query "Higher direct image of etale module sheaves
  commutes with affine locally ind etale inverse image for bounded below
  complexes": eight results about module-sheaf adjunctions, restriction or
  sheafification, none this theorem.
- `msearch.py loogle`, query `"Sheaf", "baseChange"`: two precoverage results,
  neither an etale derived direct-image theorem.
- `msearch.py grep`, query
  `ind.etale|indEtale|IndEtale|derived.*[Bb]ase[Cc]hange`, Mathlib AlgebraicGeometry:
  zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item's id,
  `indEtale.*baseChange`, `baseChange.*indEtale`, and
  `ind.etale.*direct.image`: only the affine strict-local base-change theorem
  `Scheme.indEtale_affine_strictLocal_baseChange`, which concerns schemes of
  strict localizations and does not state the derived direct-image result.
- Broader ind-etale searches found the existing ring-map predicates, strict-local
  invariance, affine strict-local comparison, and pro-affine-etale framework.
  Those notions are reused; no duplicate notion or statement was found.
- The proposed declaration name was searched in both project source roots;
  there is no pre-existing declaration with that name.

Validation: `scompile.py Q87 lem-per-ind-etale-qcqs-direct-image-base-change`
compiled this file against the live server build, in both sandbox and library
module contexts, cleanly (1.7 seconds each). Only the intended named theorem
has a postponed proof. Maximum Lean line width is 86 characters.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
