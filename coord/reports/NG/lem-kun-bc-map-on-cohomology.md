## Worker report

Module: `Sheaf.Paper.KunBcMapOnCohomology`.
Declaration: `AlgebraicGeometry.derivedBaseChangeMapPlus_cohomology_resolution`.
One theorem, with proof `sorry`; no definitions or helper theorems. The node changes only in
`lean`. The informal statement is retained verbatim. There are no new nodes, dependency
modules, or statement corrections.

The declaration equates the transported degree-q cohomology of derived exchange with the
explicit injective-resolution recipe, and asserts negative-degree vanishing separately.
The usual map is written as the composite of existing functorial constructions, rather than
introduced as a second definition of base change or defined by the desired equality.

Hypothesis and clause correspondence:

- The four schemes and four arrows are the explicitly bound `X' X Y' Y`, `g' f' f g`.
  `sq : IsPullback g' f' f g` records the cartesian square, including its commutativity.
  `sq.toCommSq` supplies the specified square identification to the existing exchange maps.
- Abelian coefficients are exactly `AddCommGrpCat.{u + 1}` throughout. No coefficient ring,
  torsion, finiteness, smoothness, or properness assumption is imposed.
- `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` is the sheaf on the small etale
  site. `(DerivedCategory.Plus.singleFunctor ... 0).obj F` is its degree-zero embedding.
- `q : ℤ` allows every integer, including zero and negative degrees.
- Higher direct images are, as in the dependency node, the degree-q cohomology of
  `lowerStar.rightDerivedFunctorPlus` applied to the degree-zero embedding.
- The first and second sides both start with
  `upperStar.mapDerivedCategoryPlusHomologyFunctorIso q` at `Rf_*F[0]`. Its hom component
  identifies `g⁻¹ H^q(Rf_*F[0])` with `H^q(g⁻¹ Rf_*F[0])`; this is the source identification
  of the node, oriented toward the object on which the derived exchange acts.
- The middle map on the left is `DerivedCategory.Plus.homologyFunctor ... q` applied to
  `Etale.derivedBaseChangeMapPlus ... sq.toCommSq` at `F[0]`.
- Both sides end by applying degree-q cohomology to `Rf'_*` of
  `g'⁻¹.mapDerivedCategoryPlusSingleFunctor 0` at `F`. This identifies the target with
  `H^q(Rf'_*(g'⁻¹F)[0])`, exactly the higher direct image in the displayed conclusion.
- The first conjunct quantifies over bounded-below injective representatives `I`, `J`.
  The two `∀ n : ℤ, Injective (...X n)` conditions describe their injective terms.
  These are resolution data quantified inside the conclusion, not extra hypotheses on
  the square or the sheaf. Existence is supplied by the imported resolution results.
  Bounded-below complexes of injectives are K-injective, so these are valid choices for
  the node's injective-resolution construction, which needs no unbounded representative.
- `s : F[0] ≅ Qh I` is the resolution identification. A quasi-isomorphism from `F[0]` to
  `I` gives this isomorphism after localization. Working in the homotopy category retains
  exactly the homotopy class of each resolution map, which is all its cohomology uses.
- `j : g'⁻¹ I ⟶ J` with `[IsIso (Qh.map j)]` is a quasi-isomorphism comparison into a
  new resolution on `X'`. Localization inverts exactly quasi-isomorphisms. In particular,
  no injectivity condition is imposed on `g'⁻¹ I`.
- The right-side middle composite spells out the resolution map. First invert `g⁻¹` of
  `rightDerivedFunctorPlusUnit.app I ≫ Rf_*.map s.inv` to pass to `Qh(g⁻¹ f_*I)`.
  `mapDerivedCategoryPlusFactorsh.hom.app` implements the termwise inverse-image comparison.
  Then apply `Qh.map` to `NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap ...).app I`:
  this is precisely the underived exchange applied termwise. Next apply `Qh.map` to
  `f'_*.mapHomotopyCategoryPlus.map j`. Finally use the unit at `J` followed by `Rf'_*` of
  the inverse of `g'⁻¹(s.hom) ≫ factors.hom.app I ≫ Qh.map j`. Thus all comparison maps are
  canonical expressions, not unconstrained comparison isomorphisms.
- Applying the homology functor to this composite is the quotient-of-cycles-by-boundaries
  construction in the node. This does not assert that a section of a cohomology sheaf has
  a global cycle representative.
- The second conjunct is `q < 0 → IsZero (...) ∧ IsZero (...)`, for `R^qf_*F` and
  `R^qf'_*(g'⁻¹F)` respectively. The inverse image of the first zero object is zero because
  inverse image is additive; hence the source and target of the base-change map vanish.

Dependencies read and reused:

- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `AlgebraicGeometry.Etale.squareUpperStarIso`, `AlgebraicGeometry.Etale.baseChangeMap`.
  The square isomorphism is used by the recorded exchange constructions, not redefined.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, with the generic
  `CategoryTheory.Functor.rightDerivedFunctorPlus` for its derived functor.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`,
  `mapDerivedCategoryPlusFactorsh`, `mapDerivedCategoryPlusHomologyFunctorIso`, and
  `mapDerivedCategoryPlusSingleFunctor`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `CategoryTheory.Functor.homologyFunctorIso` and `ShortComplex.mapHomologyIso`, the
  cycle-and-boundary comparison underlying the preceding derived homology identification.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`. Its factorization lemma is not the
  statement of this item: that lemma is on arbitrary homotopy complexes before taking
  cohomology; it neither identifies the sheaf-level higher direct image source/target
  nor states negative-degree vanishing.
- Proof imports: `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`
  (`AlgebraicGeometry.derivedExchangeTermwise`),
  `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
  (`AlgebraicGeometry.Etale.upperStar_abelian_exact`),
  `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
  (`CochainComplex.etale_kinjective_resolutions_exist`), and
  `Sheaf.AlgebraicGeometry.KInjectiveResolutions`
  (`CochainComplex.IsKInjectiveResolution`).
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`:
  `DerivedCategory.Plus.exists_injective_nonempty_iso`, the recorded Mathlib match for
  nonnegative injective representatives. The theorem's proof is supplied in the docstring
  as the node's four steps; only `sorry` is written as the Lean proof.

Source reading: the blueprint page at order 1752; local Stacks `sites-cohomology.tex`,
`lemma-base-change-map-flat-case` (Tag 0736), and `remark-base-change` (Tag 07A7).
The blueprint page's old truncation argument is not used: the DAG already replaced that
argument by the valid termwise-resolution proof and the module docstring follows the DAG.

Edge cases checked: `q = 0` uses the same construction; `q < 0` has the explicit two
vanishing conclusions. The zero sheaf, empty schemes, and identity squares are permitted.
There is no characteristic restriction. The scheme universe `u` is arbitrary, with
abelian-group coefficients in `u + 1`, as in the dependency statements. A resolution is
not assumed to have inverse image injective, and no false claim about global representatives
of quotient-sheaf sections is introduced.

Searches performed:

- msearch LeanFinder: “Cohomology of derived base change for etale abelian sheaves is
  computed by termwise exchange on injective resolutions”. Eight hits: sheaf cohomology
  presheaves, `Sheaf.H`, and formally-etale Kaehler results; no matching statement.
- msearch Loogle: `CategoryTheory.Functor.mapDerivedCategoryPlusHomologyFunctorIso`.
  No hits (upstream-only identifier unknown to Loogle). The upstream source was then opened
  and its full signature read; it supplies the canonical comparison used here.
- msearch grep: `baseChange.*homology|homology.*baseChange`: zero Mathlib hits.
- msearch LeanSearch: “Derived etale base change morphism on cohomology equals injective
  resolution base change”: service unavailable, Internal Server Error; no verdict inferred.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for the item ID and
  `baseChange.*homology|homology.*baseChange`. The derived factorization and degree-zero
  smooth-base-change results were inspected. The degree-zero theorem is only `q = 0`;
  other hits concern field extension or module cohomology and do not state this item.
- `rg` over `dag/lean_names_upstream.json`, Mathlib homology, and upstream for the final
  declaration name: no collision. The recorded dependency declarations' signatures and
  docstrings were opened, including the termwise exchange comparison.

Validation: server-only single-file `scompile.py`, nice 19, two threads, default 60-second
limit per file. No local compiler or lake invocation. Dry-run delivery result is recorded
below once complete.

## Second reading by NG

I opened the node statement, its Stacks source place (sites-cohomology.tex, Tags 0736 and
07A7), and the declaration in `lean/Sheaf/Paper/KunBcMapOnCohomology.lean`. The correspondence
is as follows.

- The node's cartesian square of schemes with arrows `g' f' f g` is rendered by
  `{X' X Y' Y : Scheme.{u}}`, the four morphism binders, and
  `sq : IsPullback g' f' f g`; `sq.toCommSq` supplies the specified commutative square to
  the recorded square and exchange declarations. This is the project's recorded
  cartesian-square encoding.
- The abelian sheaf `F` on `X_\Et` is exactly
  `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`. Its degree-zero placement is the
  displayed `DerivedCategory.Plus.singleFunctor ... 0` object. No coefficient,
  finiteness, properness, smoothness, or characteristic hypothesis is added.
- The arbitrary integer degree is `q : ℤ`, and the first conjunct quantifies the
  bounded-below injective resolution terms `I`, `J`, their injectivity hypotheses,
  the resolution isomorphism `s`, and the quasi-isomorphism comparison `j` with
  `[IsIso (DerivedCategory.Plus.Qh.map j)]`. These are the node's resolution data in
  the conclusion, rather than hypotheses on the square or sheaf.
- The left side is the canonical cohomology identification
  `mapDerivedCategoryPlusHomologyFunctorIso q` followed by homology of
  `Etale.derivedBaseChangeMapPlus ... sq.toCommSq`. The right side explicitly applies
  homology to the resolution comparison: inverse the source unit and `s.inv`, apply
  `mapDerivedCategoryPlusFactorsh`, termwise `Etale.baseChangeMap`, `f'_*` applied to
  `j`, then the target unit and inverse of the pulled-back resolution comparison.
  Thus it is the injective-resolution usual higher-direct-image base-change map, with
  every comparison map written canonically.
- The second conjunct is exactly `q < 0` implying `IsZero` of the source and target
  degree-`q` homology objects, which are the two higher direct images represented by
  the same derived direct-image constructions. No negative-degree case is omitted.

No mismatch was found and no Lean or node repair was needed. In particular, the Lean
uses the dependency node's `IsPullback` encoding rather than inventing a second square
notion, and it does not assume inverse images of injectives are injective. The equality
is universal over all admissible resolution comparisons, matching the node's canonical
resolution construction; it does not assert a false global cycle-representative claim.

Edge cases checked: `q = 0` uses the same formula; `q < 0` gives both explicit zero
objects; the zero sheaf, empty schemes, and identity squares are not excluded; the
scheme universe `u` is arbitrary and coefficients are in `AddCommGrpCat.{u + 1}`; no
characteristic assumption or nonempty-index assumption occurs.

Searches were checked against the worker's recorded LeanFinder, Loogle, LeanSearch, and
grep searches, and I independently inspected the upstream declarations
`derivedBaseChangeMapPlus`, `baseChangeMap`, `lowerStar`, and
`mapDerivedCategoryPlus`. No existing declaration states this cohomology/resolution
comparison, and no duplicate definition was introduced. The module compiles with the
required server-only command (`scompile.py`, nice 19, two threads, 60-second limit).
