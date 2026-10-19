## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedOpenRestriction` states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_openImmersion`.
Its sole theorem has proof `sorry`; it introduces no definition.

Hypothesis and conclusion correspondence:

- `T S U V : Scheme.{u}`, `f : T ⟶ S`, `a : U ⟶ S`, `b : V ⟶ T`, and
  `fU : V ⟶ U` render the four schemes and four morphisms in the square.
- `[IsOpenImmersion a]` is exactly the open immersion hypothesis. No properness,
  separation, quasi-compactness, or Noetherian hypothesis is imposed.
- `sq : ChosenCartesianSquare b fU f a` supplies the chosen identification of
  `V` with `T ×_S U` and both projection equations; thus `b` is the base change
  of `a`, hence an open immersion without a further assumption.
- `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` is the finite coefficient ring
  in the commutative coefficient convention of the dependency's derived categories.
  The coefficient universe is the recorded six-functor convention, with no
  equality between small-site object and morphism universes imposed.
- `IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq)` says the
  canonical restriction comparison is a natural isomorphism on the entire
  bounded-below derived category. Its source is
  `lowerStar (ModuleCat Λ) f |>.rightDerivedFunctorPlus`, followed by
  `(upperStar (ModuleCat Λ) a).mapDerivedCategoryPlus`. Its target is
  `(upperStar (ModuleCat Λ) b).mapDerivedCategoryPlus`, followed by
  `(lowerStar (ModuleCat Λ) fU).rightDerivedFunctorPlus`.
  Consequently the component at each `L : DerivedCategory.Plus
  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))` has precisely the
  displayed source and target in the node. Naturality is part of the existing
  natural transformation, and `IsIso` gives its inverse naturally, rather
  than asserting unrelated objectwise isomorphisms.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including `isoPullback`, `hom_fst`,
  `hom_snd`, and inherited `toCommSq`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded vocabulary uses
  `AlgebraicGeometry.Etale.DerivedCategoryModule` in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, and Mathlib's
  `DerivedCategory.Plus` for bounded-below objects.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, with its resolution
  characterization `derivedBaseChangeMapPlus_fac_app`. Added the already recorded
  node `def-weil-pbc-derived-exchange` to `stmt_deps` to cite this canonical map.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and
  `upperStarLowerStarAdjunction`, imported transitively by the derived map.
- `def-weil-pbc-scheme-conventions` has a convention-only record; its relevant
  notions are Mathlib's `Scheme` and `IsOpenImmersion`.
- Proof imports retain
  `AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction` and
  `localizationRestrictionLowerStarAdjunction` from
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
  `AlgebraicGeometry.Scheme.Etale.overEquiv` and the cocontinuity and sheaf
  equivalence interfaces from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`;
  `SheafOfModules.localizedModule_adjunction_exact` from
  `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`; and
  `CochainComplex.etale_kinjective_resolutions_exist` from
  `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`.

Edge cases checked: `a = 𝟙 S` gives identity restriction; the empty open gives
zero sheaves and derived objects on the empty scheme; `L = 0` gives an
isomorphism between zero objects. The zero coefficient ring is allowed.
No condition rules out arbitrary disconnected schemes or unbounded-above
complexes. A chosen Cartesian identification allows any model of the fibre
product, including the literal categorical pullback.

Searches performed (2026-10-15):

- `msearch.py leanfinder`: "derived direct image restricted to an open immersion
  is base change". Eight hits, concerning scheme module restriction and
  open-immersion section isomorphisms; none states etale derived restriction.
- `msearch.py loogle`: "IsOpenImmersion, IsIso". Zero hits; the service reports
  unknown identifier `IsOpenImmersion`.
- `msearch.py grep`: "baseChange|rightDerivedLowerStarPlus" in
  `AlgebraicGeometry`. Twenty-five hits concern stability of geometric
  morphism properties under base change, not derived etale sheaves.
- `rg` of the source six-functor tree found
  `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale` in
  `WeilConjectures.SixFunctors.BaseChange.EtaleDerived`. Read its full signature
  and docstring: it applies to all commutative rings and all etale base changes,
  whereas this node assumes a finite ring and an open immersion. The delivery
  states the node's precise specialization, using the same existing canonical
  comparison map and no second definition. This more general theorem is not
  imported as a new proof dependency: the docstring follows the node's
  prescribed sectionwise/injective-resolution route.
- `rg` in project `lean/Sheaf` for open restriction and base change found
  scheme-module results, extension-by-zero base change, and a reference to
  this item in `ProperConstructibleHigherDirectImages`; none states this theorem.
- Searched the exact node id in the upstream source: no matching declaration.
  Searched the new declaration name in Mathlib, upstream and `lean/Sheaf`:
  no collision.

Validation: `scompile.py NB lem-weil-pbc-derived-open-restriction` compiled the
sandbox probe and library module successfully, with no warnings or errors.
No statement correction, new node, dependency repair, or disputed statement.


## Second reading by NB

Independent review, 2026-10-15. I opened the node, its blueprint source,
Stacks sources, the delivered module, and the dependency declarations.

Object/hypothesis/conclusion checklist (all pass):

1. Schemes T and S and arbitrary morphism f:T→S: `{T S U V : Scheme.{u}}`
   and `(f : T ⟶ S)`. There is no properness, finiteness, separation,
   Noetherian, or base-field hypothesis.
2. Scheme U and open immersion a:U→S: `(a : U ⟶ S) [IsOpenImmersion a]`.
   This is Mathlib's open immersion, as the scheme convention requires.
3. V=T×_S U with projections b and f_U: `(b : V ⟶ T) (fU : V ⟶ U)` and
   `(sq : ChosenCartesianSquare b fU f a)`. I read the structure's
   `isoPullback : V ≅ pullback f a`, `hom_fst`, `hom_snd`, and inherited
   `CommSq`. The projection equations are essential: this is a Cartesian
   square, not merely an isomorphism of its upper-left scheme. No separate
   open-immersion assumption on b is needed; it follows by base change.
4. Finite coefficient ring Λ: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
   Commutativity comes from the cited `def-weil-pbc-derived-categories`,
   which defines its coefficient categories for commutative rings. Thus this
   does not silently replace a node permitting noncommutative coefficients.
   `Finite` asserts finiteness without choosing an enumeration.
5. Every L in D⁺(T_et,Λ): the existing `derivedBaseChangeMapPlus` is a natural
   transformation with domain `DerivedCategory.Plus (Sheaf
   T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. There is consequently no
   explicit L binder: `IsIso` of that transformation quantifies over every
   component, equivalently giving a natural isomorphism on the whole D⁺.
   I checked `DerivedCategoryModule` and the dependency module's D⁺ convention,
   rather than using the similarly named category of O_T-modules.
6. Source a⁻¹ Rf_*L: `derivedBaseChangeMapPlus` has source
   `(lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
   (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus`.
   I read `lowerStar` (pushforward along the small-etale base-change functor)
   and `upperStar` (its sheaf inverse image), and the derived map definition.
7. Target Rf_U,* b⁻¹L: its target is
   `(upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus ⋙
   (lowerStar (ModuleCat.{u + 1} Λ) fU).rightDerivedFunctorPlus`.
   The directions of all four arrows agree with the node.
8. The restriction comparison is natural and invertible:
   `IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq)`.
   This uses the recorded canonical map, not unrelated chosen component
   isomorphisms. Its `derivedBaseChangeMapPlus_fac_app` characterization
   identifies it with the node's sectionwise comparison on resolutions.

Source and proof check: Stacks Tag 03S2 is the extension-by-zero section in
`etale-cohomology.tex` (the DAG proof's file attribution to
`sites-cohomology.tex` is imprecise); it identifies inverse image with
restriction and supplies extension by zero for module sheaves. Tag 03F3 in
`sites-cohomology.tex` proves preservation of injectives using the exact
extension-by-zero adjunction. Tags 05TH and 05TI in `derived.tex` supply
injective acyclicity and bounded-below right derived functors. None imposes
properness or Noetherian hypotheses here. The module docstring reproduces all
three proof steps: sectionwise equality, injective preservation through the
exact adjoint, and degreewise comparison on an injective resolution. I also
opened `upperStarIsoLocalizationRestriction`,
`localizationRestrictionLowerStarAdjunction`, `Scheme.Etale.overEquiv`,
`SheafOfModules.localizedModule_adjunction_exact`, and
`CochainComplex.etale_kinjective_resolutions_exist`; the proof imports are the
recorded interfaces. No new definition node or dependency module is delivered.

Edge cases: the identity open and the empty open are included; an empty T or S
is allowed whenever the square exists. Zero complexes and the zero coefficient
ring are included. No nonzero/nontorsion or invertible-characteristic condition
is present. There is no index set or degree n in the signature; all degrees,
including degree zero and negative lower bounds, occur in D⁺. Complexes need
not be bounded above. The universe u is declared; all variables are bound.
The coefficient universe and module universe are exactly those of the recorded
six-functor category, with no extra equality on site universes. An arbitrary
finite coefficient ring can be represented in this universe, and schemes from
different smaller universes can be viewed in a common one.

Independent searches: `msearch.py leanfinder` with “etale derived pushforward
commutes with restriction to an open subscheme” returned eight hits about
scheme-module restriction and scheme sections, not this etale theorem.
`msearch.py loogle` with `IsIso, ModuleCat` returned no hits (unknown IsIso).
`msearch.py leansearch` with “derived direct image restriction open immersion
sheaves modules” reported Internal Server Error; recorded as unavailable.
I searched Mathlib, upstream WeilConjectures, and project Sheaf with rg for
`derivedBaseChangeMapPlus`, derived/restriction combinations, and the proposed
name. The similar project statements are about scheme/ringed-space modules,
not constant-coefficient etale sheaves. I independently opened the complete
signature and docstring of upstream
`Etale.isIso_derivedBaseChangeMapPlus_of_etale`: it permits arbitrary commutative
rings and etale g, and takes IsPullback rather than the chosen square. It is a
more general theorem, not an identical statement of this node. I retain the
precise finite-ring/open-immersion specialization and reuse its canonical map;
no construction is duplicated.

Mismatch/change verdict: no mathematical signature mismatch found; no Lean or
node change needed. Added this independent reading and clarified the source
file attribution in this report. The recorded lean.statement was checked
verbatim against the theorem signature. The sole theorem remains sorry;
there are no new definitions, proofs, private declarations or local notation.
