## Worker report

The delivery states `AlgebraicGeometry.Etale.etale_locality_baseChange` in
`Sheaf.AlgebraicGeometry.EtaleLocalityBaseChange`. Its proof is `sorry`, as required at
stage 2. The six-step proof docstring gives the node's slice-localization, K-injective,
canonical-arrow compatibility, sheaf gluing, all-degree detection, and single-degree
arguments. The source read was Stacks Project `etale-cohomology.tex`, Tag 0EZR,
`lemma-base-change-local`, statement and proof (lines 16307–16369), together with the
blueprint statement. No statement correction or dispute is needed.

Hypotheses and clauses, in order:

- A base-change square is the recorded `sq : ChosenCartesianSquare h e f g`, with
  `X Y S T : Scheme.{u}` and all four named edges, not just a commutative square.
  This is exactly sbc-def-base-change-square and includes its chosen Cartesian identification.
- The covering is `a : ∀ i, U i ⟶ X`, with `[∀ i, AlgebraicGeometry.Etale (a i)]`
  and `ha : ∀ x : X, ∃ i y, (a i).base y = x`. These are etaleness and joint
  surjectivity, respectively. `ι : Type w` is independent of the scheme universe;
  there is no finite, nonempty, or countable restriction on the cover.
- The factorization is `fi : ∀ i, U i ⟶ V i`, `b : ∀ i, V i ⟶ S`,
  `[∀ i, AlgebraicGeometry.Etale (b i)]`, and
  `wfactor : ∀ i, fi i ≫ b i = a i ≫ f`. No etaleness is imposed on fi or f.
- The associated products are represented by arbitrary chosen models: `T' i`,
  `c i : T' i ⟶ T`, `gi i : T' i ⟶ V i`, and
  `hc : ∀ i, IsPullback (c i) (gi i) g (b i)` express `V_i ×_S T`.
  `localSquare : ∀ i, ChosenCartesianSquare (hi i) (ei i) (fi i) (gi i)`
  expresses `U_i ×_{V_i} T'_i`. The factorization equation and the global square
  identify this with `U_i ×_X Y`, compatibly with projections, by pullback pasting.
  Thus these are exactly the associated Cartesian diagrams, allowing arbitrary isomorphic
  models as the global square does. No morphism to Y or additional hypothesis is needed:
  it is the uniquely induced morphism to the chosen global product.
- Clause (1) quantifies `F : Sheaf T.smallEtaleTopology (Type (u + 1))`.
  `((Scheme.etaleSetPullback (c i)).obj F)` is precisely F_i. Its premise is
  `∀ i, IsIso (setBaseChangeArrow (localSquare i) F_i)` and its conclusion is
  `IsIso (setBaseChangeArrow sq F)`. The source equalities mean that the canonical
  comparison is invertible, as the source proof explicitly states; no objectwise
  arbitrary isomorphism replaces the canonical arrow.
- Clause (2) quantifies every
  `K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  `D(upperStar AddCommGrpCat.{u + 1} (c i)).obj K` is K_i, the exact termwise
  inverse image. The premise and conclusion assert invertibility of the local and global
  `abelianDerivedBaseChangeArrow`. This uses the unbounded derived category, with no
  torsion, coefficient, bounded-below, qcqs, or properness assumption.
- Clause (3) quantifies an abelian sheaf F and `q : ℤ`. The sheaf in degree zero is
  `(DerivedCategory.singleFunctor _ 0).obj F`; the arrow is its canonical derived
  exchange mapped by `DerivedCategory.homologyFunctor _ q`. Locally F is first pulled
  back by `upperStar ... (c i)`, giving F_i. Thus precisely the degree-q comparison is
  assumed locally, and precisely that comparison is concluded globally. It does not
  assume the clause-(2) premise or any other degree. Exactness supplies the usual
  identification of its sides with f-inverse-image of R^q g_* and R^q h_* e-inverse-image.

Dependency declarations used:

- sbc-def-base-change-square:
  `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`,
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso`; its imported
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` supplies the identical square datum.
  The inverse-image comparison is not redefined in the locality module.
- sbc-def-base-change-map: repaired in this delivery as detailed below; the original
  `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`,
  `AlgebraicGeometry.Etale.derivedBaseChangeMap` is retained for module coefficients.
  The added set and abelian arrows give the cases needed here.
- def-weil-pbc-etale-site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- def-weil-pbc-etale-sheaf-of-sets: `Mathlib.CategoryTheory.Sites.Sheaf`,
  `CategoryTheory.Sheaf`, specialized to `Type (u + 1)`.
- def-weil-pbc-derived-categories: `Sheaf.AlgebraicGeometry.DerivedCategories`;
  its documented unbounded abelian-sheaf derived category is used literally.
- def-weil-pbc-direct-image:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.lowerStar`;
  its total derived extension is the existing generic `Functor.rightDerivedFunctor`
  and `Etale.mapDerivedUpperStarLowerStarAdjunction` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.
- def-weil-pbc-sites-and-cohomology:
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, `Sheaf.H'` and its site/sheaf
  vocabulary. This theorem concerns cohomology SHEAVES of the derived exchange, so
  it uses `DerivedCategory.homologyFunctor`, not objectwise site cohomology H'.
- def-weil-abstract-derived-category:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, with the existing
  Grothendieck-abelian category instance, and the existing single/homology functors.
- The set-valued inverse image is the existing `Scheme.etaleSetPullback` from
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` (def-weil-pbc-etale-sheaves), not a private copy.
  This landed node is added to stmt_deps because its construction is now used explicitly.

The recorded, stated proof-dependency modules are imported without `public`: etale slice
site equivalence, slice-site localization, site-morphism composition, exact inverse image
for sets, K-injective resolutions and restriction, total right derived functors, site
restriction exactness, exact abelian inverse image, and etale-cover detection. Mathlib
proof dependencies are already transitively imported; no unavailable theorem has been
postulated. These imports preserve the existing proof route; the helpers introduce no
postponed theorem at all.

Edge cases checked before writing: an empty cover is allowed and forces X empty by ha;
its sheaf equalizer has singleton section sets and its abelian derived category is zero.
Identity covers and identity squares use the usual units, counits, and canonical composition
comparisons. Empty source or target schemes are allowed. q=0 gives the underived abelian
comparison; negative q remains allowed. The zero sheaf and zero complex require no
exception. Unbounded complexes in both directions are included literally. The index
universe is unrestricted. The sites retain their existing object and morphism universes;
no universe equality was added to force an API.

Searches actually run:

- msearch.py / leanfinder: "Etale localization of base change maps for sheaves of sets
  and unbounded derived direct images" — eight hits, including
  `SheafOfModules.bijective_pushforwardSections`, `Functor.sheafPullbackConstruction.sheafPullback`,
  RanIsSheaf lemmas, and the formally-etale Kaehler differential base-change result;
  none states the three-clause locality lemma.
- msearch.py / loogle: "CategoryTheory.Sheaf, CategoryTheory.IsIso" — twelve hits on
  sheafification, localization, and sheaf composition; no exact locality statement.
- msearch.py / grep: "baseChange|localization" in AlgebraicGeometry/Sites — 22 hits on
  topology stability and related site constructions, no matching locality statement.
- msearch.py / leansearch: "Etale covering detects isomorphism of base change maps for
  sheaves of sets and unbounded derived direct image" — UNAVAILABLE, HTTP Internal
  Server Error; not treated as a negative result.
- rg in the upstream WeilConjectures tree for the node id and etale locality found
  `SixFunctors/Etale/SmoothBaseChange/Locality.lean`. Read its full locality signatures:
  the set-named underived result actually quantifies module sheaves; the derived result
  is on `DerivedCategory.Plus`; the degreewise result is for module sheaves. Thus it is
  not the node's full statement. It is not attached as an exact existing declaration.
- rg in lean/Sheaf for locality and set pullback found the existing etale-set inverse-image
  construction and composition/unit APIs, which are reused. No declaration gives this
  three-clause statement or either new arrow name. The upstream names table and source
  grep likewise contain none of the three new helper names or the new theorem name.

Validation: both delivered files compiled separately in dependency order using scompile.py;
all server compiles were clean, with no errors or unexpected warnings. No local Lean
compiler, lake build, upstream edits, or direct repository writes were used.

## Dependency modules

`sbc-def-base-change-map` gets a lean-only interface repair under brief-stage2 §1(B),
module `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`. The recorded
`Etale.derivedBaseChangeMap` needs monoidal coefficient data and therefore cannot be
specialized directly to AddCommGrpCat; it also does not provide the sheaf-of-sets arrow.
The module imports and preserves that existing module-coefficient definition. It adds
`Etale.setUpperLowerAdjunction`, the direct specialization of Mathlib's continuous
sheaf-pullback adjunction to the already existing set inverse image and direct image;
`Etale.setBaseChangeArrow`; and `Etale.abelianDerivedBaseChangeArrow`. Each definition
contains real data, no sorry, arbitrary arrow, Nonempty choice, or existential selection.

Both arrows are exactly the unit for e, the canonical pushforward composition square
comparison, and the counit for f. In the abelian derived case the pushforward comparisons
are `rightDerivedLowerStarComp` (conjugates of the exact termwise inverse-image comparison)
and `rightDerivedLowerStarCongr sq.w.symm`. Thus this is the normalized formula in the
node, not an unspecified isomorphism or a new comparison chosen ad hoc. The helpers are
part of the same base-change-map notion, and their source/blueprint docstrings name
sbc-def-base-change-map. The repaired lean record lists the original module-coefficient
map as well as all added declarations. Every other field of this dependency is unchanged.

The set-pullback source was additionally read from the current server with
`scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleSheaves`, because the older
local source checkout does not contain that upstream module. The helper imports the
recorded upstream module, rather than the retired local Sheaf module.

## Second reading by NM

I independently read the sandbox node, both delivered Lean files, Stacks
`etale-cohomology.tex` at `section-base-change-preliminaries` and the full statement
and proof of `lemma-base-change-local` (Tag 0EZR). The section introduces arbitrary
schemes and small etale sites; it imposes no properness, finiteness, Noetherian,
characteristic, torsion, or boundedness assumption. The source explicitly interprets
the displayed equalities as invertibility of the base-change maps.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Four schemes X,Y,S,T and the named Cartesian square, with h:Y→X, e:Y→T,
   f:X→S, g:T→S: `{X Y S T : Scheme.{u}}` and `sq : ChosenCartesianSquare h e f g`.
   Pass. I opened `ChosenCartesianSquare` and `baseChangeInverseImageIso`: the datum
   extends the correct `CommSq` and specifies a pullback isomorphism respecting both
   projections. It is the recorded square, not a weaker commutative square.
2. An etale covering of X: `a : ∀ i, U i ⟶ X`, the etale instance family, and
   `ha : ∀ x : X, ∃ i y, (a i).base y = x`. Pass: these are exactly etaleness and
   joint surjectivity; Mathlib's `ofArrows_mem_smallEtaleTopology_iff` confirms the
   covering interpretation. `ι : Type w` carries no size, finiteness or nonemptiness
   assumption beyond being an index set.
3. Factor U_i→S through V_i→S etale: `fi`, `b`, the etale instances on `b i`, and
   `wfactor : ∀ i, fi i ≫ b i = a i ≫ f`. Pass. Neither fi nor f is assumed etale.
4. The associated lower products V_i×_S T: `T'`, `c`, `gi`, and
   `hc : ∀ i, IsPullback (c i) (gi i) g (b i)`. Pass, with arbitrary isomorphic
   models of the specified products and the correct projections.
5. The associated upper products U_i×_X Y and their arrows: `Y'`, `hi`, `ei`,
   and `localSquare : ∀ i, ChosenCartesianSquare (hi i) (ei i) (fi i) (gi i)`.
   Pass. Substituting the lower pullback and the factorization identifies this upper
   product with U_i×_S T, and the global Cartesian square identifies U_i×_X Y with
   the same product. Pullback pasting therefore supplies the compatible map to Y;
   omitting an explicit projection to Y does not omit a mathematical hypothesis.
6. Clause (1), arbitrary set sheaf F on T, its restriction F_i, and local-to-global
   invertibility: `∀ F : Sheaf T.smallEtaleTopology (Type (u + 1))`,
   `(Scheme.etaleSetPullback (c i)).obj F`, and the implication between the local and
   global `IsIso (setBaseChangeArrow ...)`. Pass. The premise is for every i with
   this same F, and the conclusion concerns its canonical global arrow.
7. Clause (2), arbitrary K in unbounded D(T_et), restriction K_i, and derived
   local-to-global invertibility: `∀ K : DerivedCategory (Sheaf ... AddCommGrpCat)`,
   `D(upperStar ... (c i)).obj K`, and `IsIso (abelianDerivedBaseChangeArrow ...)`.
   Pass. I read `DerivedCategories`, `upperStar`, `lowerStar`, and
   `mapDerivedUpperStarLowerStarAdjunction`; these are the recorded abelian-sheaf
   category, exact inverse image applied termwise, and total right derived image.
   There is no Plus restriction and no extra typeclass binder on the theorem.
8. Clause (3), abelian F, fixed degree q, and ONLY degree-q local hypotheses:
   `∀ (F : Sheaf ... AddCommGrpCat.{u + 1}) (q : ℤ)`, `singleFunctor _ 0`,
   and `homologyFunctor _ q` applied to the canonical derived arrows, locally after
   pulling back F along c_i. Pass. Exact inverse image identifies these with the
   stated higher-direct-image arrows. The clause does not require the whole local
   derived arrow to be invertible or assume the other clauses' premises.

Dependency module review (H4/H5/H12/H13): no new definition nodes are present.
I read the repaired `sbc-def-base-change-map` node, including its coefficient scope
and unit-e/composition/counit-f formula. The imported original
`derivedBaseChangeMap` has monoidal and flat-resolution coefficient assumptions;
`AddCommGrpCat` cannot directly use that recorded interface. The new abelian arrow
uses `mapDerivedUpperStarLowerStarAdjunction` and `rightDerivedLowerStarComp`, whose
source definition is the conjugate of the exact inverse-image composition comparison;
`rightDerivedLowerStarCongr sq.w.symm` has precisely the e≫g to h≫f orientation.
The counit is for f and the inserted unit is for e, as required. The set arrow uses
the same formula with `lowerStarComp` and the standard continuous sheaf adjunction.
I also read the current server source of `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
using `scompile.py --source`: `etaleSetPullback` is exactly the left Kan extension
and sheafification construction used by `setUpperLowerAdjunction`. No private inverse
image or arbitrary comparison has been introduced. All three added definitions
contain real terms and no sorry; the existing module-coefficient definition remains
imported and listed. The dependency repair therefore preserves its full recorded
scope while supplying the previously unusable abelian and missing set interfaces.

I opened the other recorded statement-dependency signatures in Mathlib and the
project: `smallEtaleTopology`, `Sheaf`, `DerivedCategory`/`HasDerivedCategory`, and
`Sheaf.H'`, as well as the sheaf and derived-functor modules above. `H'` is object
cohomology; correctly, the theorem uses the existing derived homology functor for
cohomology SHEAVES instead. No private replacement of one of these notions occurs.

Independent searches: LeanFinder query "jointly surjective etale family reflects
invertibility of exchange morphisms on unbounded abelian complexes" returned eight
ring-theoretic etale hits, none matching. Loogle query
`CategoryTheory.IsIso, CategoryTheory.Sheaf` returned sheafification and localization
isomorphism tests, not this statement. I ran rg with `exchange`, `locality`,
`local.*[Bb]ase[Cc]hange`, `[Bb]ase[Cc]hange.*local`, and the added arrow names in
Mathlib's site files, the upstream six-functor tree, and the project's `lean/Sheaf`.
I opened the three `isIso_baseChange...of_etale_cover` declarations in upstream
`SmoothBaseChange/Locality`: their sheaves are ModuleCat-valued, and the derived
clause is on DerivedCategory.Plus. I also read the project's
`ProperBaseChangeTargetLocality`: it assumes properness and uses a degree-zero sheaf
in D+, so it is not the present arbitrary-cover/unbounded three-clause statement.
Upstream `baseChangeMap` requires abelian coefficients and the unbounded derived
map requires monoidal coefficients; neither duplicates the added set/abelian arrows.
No exact existing declaration was found.

Edge cases: an empty index set is allowed; ha then forces X empty and the conclusion
is valid in its terminal sheaf/zero abelian derived category. Empty schemes, zero
sheaves and zero complexes are allowed. Identity covers and squares use the standard
adjunction units and counits. q=0 is the ordinary comparison and negative q is allowed;
no bound on K or characteristic is imposed. Scheme universes are shared as in the
recorded small-site convention, coefficient values are in u+1, and the index universe
w is independent. No hidden equality of site universes or unbound variable occurs.

Mismatch/change verdict: no mathematical mismatch was found. I left both Lean files
and node records unchanged, including the verbatim `lean.statement` signatures.
The source/blueprint docstrings and all six proof steps are present; the only theorem
proof is sorry, and there are no local instances, private definitions, or local
notations introduced by either module. This second-reading section is the only edit.

Validation: I independently recompiled BOTH delivered files, in dependency order,
using `scompile.py NM sbc-lem-etale-locality` with the prescribed server-only settings.
Both passed without errors or unexpected warnings. No local compiler, lake build,
upstream modification, repository modification, or repository git command was used.
