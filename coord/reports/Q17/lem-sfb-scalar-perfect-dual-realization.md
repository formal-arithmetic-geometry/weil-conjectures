## Worker report

Item: `lem-sfb-scalar-perfect-dual-realization`, group Q17, stage 2, 2026-10-21.
Module: `Sheaf.Paper.ScalarPerfectDualRealization`.
Namespace: `CategoryTheory.ScalarPerfectDual`.

This delivery states all clauses of the node in one module, with the declarations
listed in `lean.declarations`. Every theorem proof is `sorry`. All definitions have
actual data, and only uniquely specified maps/isomorphisms are extracted from
postponed existence statements. No statement correction, dependency repair, or new
node is needed. The source was read in `literature/stacks-project/sites-cohomology.tex`,
`lemma-Rhom-strictly-perfect` (08JH) and `lemma-dual-perfect-complex` (08JJ), including
the final finite-free/direct-summand evaluation calculation.

Hypotheses and clauses, in order:

* A commutative scalar ring: `(R : Type u) [CommRing R]`.
* An arbitrary site small in the module universe: `{C : Type u} [SmallCategory C]`
  and `(J : GrothendieckTopology C)`. There is no terminal-object, point, scheme,
  nonemptiness, or special-topology hypothesis. `u` is explicit. The independent
  `w` in `[HasDerivedCategory.{w} (Modules J B)]` chooses the derived localization's
  Hom universe, as required by Mathlib and the size-convention dependency.
* A commutative ring sheaf with scalar structure: `(B : Sheaf J CommRingCat.{u})`
  and `α : (constantSheaf J CommRingCat).obj (CommRingCat.of R) ⟶ B`.
* Module sheaves and their unbounded derived category: `Modules` abbreviates
  `ringedSiteModules` over the underlying ring sheaf of B; the derived clause uses
  `DerivedCategory` on precisely this category.
* The specified ordinary realization C_B(M): `realize` applies the existing
  `constantCoefficientModule J R` followed by `SheafOfModules.changeOfRings α`.
  The latter is ordinary sheafification of the sectionwise scalar tensor, with
  B acting on its scalar factor. `realizeMap` uses the existing change-of-rings
  map of the constant-module map. `realization` packages these same objects and
  maps; its functor laws are the named `realizeMap_laws`. Additivity is obtained
  by referencing that theorem, and `complexRealization` is termwise realization.
* A bounded cochain complex of finite projectives with chosen degreewise splittings:
  `F : CochainComplex (ModuleCat.{u} R) ℤ`,
  `P : ModuleCat.StrictPerfectCoefficientPackage F`, and integer bounds with
  `hbounded : ∀ q, q < a ∨ b < q → IsZero (F.X q)`. The package contains actual
  maps to and from `ModuleCat.of R (Fin (P.N q) → R)` with composite identity.
  These data imply finite generation and projectivity, so separate redundant
  hypotheses are unnecessary. No requirement that the splittings be chain maps
  is imposed. The theorem for an individual finite projective V explicitly takes
  `Module.Finite R V` and `Module.Projective R V`.
* F-dual means the existing Hom_R(F,R[0]): `dual` is an abbreviation for
  `CochainComplex.moduleHomComplex F (singleFunctor ... 0).obj (ModuleCat.of R R)`.
  It is not a newly chosen dual complex. `dual_coordinates` identifies its q-th
  term with `Module.Dual R (F.X (-q))`. Its first equation specifies projection at
  the triplet (-q,0,-q+q=0); its second equation gives exactly
  `-q.negOnePow • (F.d (-(q+1)) (-q)).hom.dualMap`. This is the displayed
  differential -(-1)^q φ d_F. `coordinates` extracts that uniquely specified iso.
* Each E^q is a summand of a finite free B-sheaf: the first conjunct of
  `scalarPerfectDualRealization` is `Nonempty (StrictPerfectCoefficientPackage ... E)`.
  Its ranks are natural numbers, including zero; its maps and splitting equation
  are exactly the dependency's package. This asserts existence of the splitting,
  rather than defining an unknown sheaf from existence.
* Internal Hom_B(E^q,-) is exact: the second conjunct quantifies over every degree
  and every `ShortComplex (Modules J B)` with `S.ShortExact`. It asserts that the
  short complex of the actual `homObjMap (𝟙 E^q) S.f` and `... S.g` is short exact.
  This is exactness in the sheaf category, with no global-Hom or sectionwise-exactness
  substitution. The existential `hz` supplies only the proof of zero composition.
* Every K-injective resolution: the last conjunct quantifies over arbitrary,
  possibly unbounded I and every `ι : unitComplex J B ⟶ I`, assuming `QuasiIso ι`
  and `I.IsKInjective`. The resulting `QuasiIso` is for the canonical map induced
  by ι using the recorded `homComplexFunctor`. There is no selected resolution
  restriction or extra boundedness on I.
* The canonical β_V and its generator formula: `evaluation_existsUnique` specifies
  β as a sheaf morphism with the exact value
  `bb' * scalar ... (φ v)` on `b ⊗ φ`, evaluated at `b' ⊗ v` in the slice over U.
  `constantElement` and `tensorElement` are the actual two sheafification-unit
  elements, not arbitrary generator functions. Evaluation at
  `op (Over.mk (𝟙 U.unop))` is the identity object of that slice. `evaluation`
  extracts the unique such morphism. This defines the canonical comparison for
  general modules; `evaluation_natural_isIso` states its contravariant naturality
  and its invertibility under exactly finiteness and projectivity.
* These degree maps form a cochain isomorphism: `comparison_existsUnique` specifies
  `κ : C_B(F-dual) ≅ signedSheafDualComplex E B` with every component fixed by
  `HEq (κ.hom.f q) (realization.map (coordinates ... q).hom ≫ β)`.
  The arrow types are definitionally the same by the term formulas of
  `mapHomologicalComplex` and `signedSheafDualComplex`; HEq expresses the same
  component equality while avoiding expensive eager unfolding of sheafification.
  It introduces no additional type equality hypothesis or arbitrary transport.
  The existing `signedSheafDualComplex` has precisely the surviving degree-q Hom
  factor and the differential -(-1)^q precomposition by d_E. The library's
  `homComplex_to_single_iso` identifies this signed complex with `homComplex E B[0]`
  by the canonical surviving-factor projection and degree-zero single-complex iso.
  `ordinary_comparison` states the resulting isomorphism to the recorded product
  Hom complex. No data are chosen from this bare existence statement. The source
  and target retain their existing signed differentials; chain-map compatibility
  is part of κ. `comparison` extracts the uniquely normalized signed cochain iso.
* Naturality in cochain maps: `comparison_natural` constructs scalar precomposition
  `g : dual G ⟶ dual F`, fixes each component through `coordinates` and the actual
  `dualMap (f.f (-q))`, and states the square with the recorded Hom-complex
  precomposition map. No arbitrary dual action is used.
* Derived internal Hom representation and naturality: `derived_comparison_natural`
  gives a family of isomorphisms from `Q(C_B(F-dual))` to the object of the existing
  `derivedInternalHomOfUniverses` at `(op (Q E), Q B[0])`. Its equation quantifies
  over all scalar cochain maps and their coordinate-characterized duals and uses
  the bifunctor's actual map `(Q(C_B f)).op, 𝟙`. In particular the family is natural
  in F; the identity case also makes it independent of splitting and bound witnesses.
  Combined with the every-resolution quasi-isomorphism and the normalized κ, this
  states precisely that the ordinary Hom complex represents this derived Hom.
* Reversed degree bounds: `dual_bounds` gives both `IsZero (C_B(F-dual).X q)` and
  `IsZero ((homComplex E B[0]).X q)` whenever `q < -b ∨ -a < q`.
* No flatness: neither a ring-flatness assumption on α nor an exactness assumption
  on scalar extension is present. Only additivity and preservation of finite
  splittings are used.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  the Grothendieck topology is the sheaf-theoretic site presentation.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  and the underlying Mathlib `SheafOfModules` category.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, Q.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  ordinary sheaf tensor; its imports retain the exact existing
  `SheafOfModules.changeOfRings`, `changeOfRingsHom`, `changeOfRingsPresheaf` used here.
* `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`: the recorded general
  interfaces and its public original module's
  `ModuleCat.StrictPerfectCoefficientPackage`,
  `SheafOfModules.StrictPerfectCoefficientPackage`, `strictPerfectConstantPresheaf`.
* `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`; `...HomComplexToSingle`: `signedSheafDualComplex`,
  `homComplex_to_single_iso` (canonical projection identification).
* `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`, with the localized-site interpretation read
  from `...Presheaf.InternalHom`.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses`, its representative/comparison interface.
* `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`:
  `CategoryTheory.quasiIso_homComplex_map_of_bounded_exact_terms`, proof-plan import.
* Three already-landed definition nodes were added to stmt_deps, under the rule allowing
  landed notions: `def-weil-pbc-constant-coefficient-scalar-extension` supplies
  `Sheaf.CategoryTheory.ConstantCoefficientScalarExtension` and its recorded
  `constantCoefficientModule`, `constantCoefficientUnit`;
  `def-sc-module-total-hom-complex` supplies
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`,
  `CochainComplex.moduleHomComplex`. Their complete source signatures and docstrings
  were read; neither node is changed or copied in this delivery. The third is
  `def-sc-signed-sheaf-dual-complex`, whose recorded
  `WeilConjectures.Algebra.Homology.HomComplexToSingle` supplies the existing
  `CategoryTheory.signedSheafDualComplex` used to normalize the cochain iso directly.
* The proof dependency `lem-sfb-ringed-site-finite-retract-dual-exact` has no recorded
  Lean module yet, so there is no module to import. It is a proof dependency only:
  the exactness clause is stated here and its eventual proof uses that lemma.
  All statement dependencies have usable declarations, so no prerequisite node needs
  to be supplied. Module sheafification uses Mathlib's existing
  `PresheafOfModules.sheafificationAdjunction` and its actual units.

Edge cases checked before and during writing: V=0 and rank N=0; the zero ring and
zero B; zero complex; a>b (the hypotheses force the entire complex to vanish);
endpoints q=-b,-a are retained by strict outside inequalities; arbitrary odd and
even negative degrees in `Int.negOnePow`; a non-free finite projective summand;
non-flat scalar morphism Z→Z/2; arbitrary unbounded K-injective targets; identity
and arbitrary cochain maps; empty sites and sites without terminal objects.
There is no mathematical dispute or node fault to report.

Searches (the wrapper's exact results are also in searches.jsonl):

* msearch leanfinder: "Constant sheaf scalar extension of a finite projective complex
  dual computes derived internal sheaf Hom". Eight hits: Ext, Sheaf.H, specialized
  condensed monoidal/internal-projective results and ProjectiveResolution.isoExt;
  none gives the arbitrary-ringed-site comparison.
* msearch loogle: "Module.Dual, TensorProduct". Twelve hits including dualDistrib,
  contractions and dualTensorHomEquiv. These concern ordinary modules, not the
  constant-sheaf/change-of-rings comparison and its signed derived realization.
* msearch grep: "scalar.*[Dd]ual|[Dd]ual.*scalar" in Algebra/Category/ModuleCat.
  Zero hits.
* msearch leansearch: "Scalar realization by constant sheaf and extension of scalars
  commutes with finite projective duals and computes derived sheaf Hom". Eight hits,
  primarily ordinary extension/restriction adjunctions, Module.dual_projective and
  sheafification scalar machinery; no exact match.
* rg in lean/WeilConjectures and lean/Sheaf for scalar/dual realization and the
  item id found no declaration of the item. Searching for the underlying Hom and
  constant-sheaf notions found the modules reused above. The specialized downstream
  `AlgebraicGeometry.ProEtale.InternalHomDualModels.scalarDual` has module universe
  u+1; instead the already-recorded, arbitrary-universe module total Hom is used,
  with explicit coordinates. No second signed-dual construction is introduced.

Validation: scompile.py was used for every compilation. The complete final file
compiled with no errors or warnings: sandbox 19.5 seconds, named module 18.1 seconds,
with the unchanged 60-second limit. The only final elaboration adjustment was HEq
in the degreewise component formula; the ordinary homogeneous equality forced deep
unfolding of the scalar tensor/sheafification implementation. Diagnostic options and
check commands were removed. The prescribed delivery dry run follows.

## Second reading by Q17

Final rereading by the same dispatcher-started worker; no independent agent was
started, as the brief expressly prohibits it. The maintainer supplies the independent
review. The rereading checked the node's clauses against the declaration list above,
the exact β formula including both scalar factors and slice identity object, the
negative-degree sign, the all-resolutions quantifier, and both reversed-bound terms.
It also checked that each extracted map is fixed by its formula, that the scalar
Hom object is reused rather than replaced by an arbitrary complex, and that no
flatness, terminal object, or chain splitting is assumed. Compiler repairs made
universe arguments of ordinary change of rings explicit, supplied the stored
section-module action to the pure-tensor constructor, and used the actual implicit
binders of the additive-functor field. The explicit product-projection helper was
replaced by the existing signedSheafDualComplex normal form and the library's
canonical Hom-into-a-single identification, to avoid repeated expensive elaboration. No mathematical statement changed.

Delivery validation: `deliver2.py Q17 lem-sfb-scalar-perfect-dual-realization --no-push`
returned `OK (dry run): commit 91bd0f73d47 passes the preflight and compiles; nothing pushed`.
The first dry run caught an incorrectly truncated `lean.statement` record: extraction
had stopped at a named argument `(R := B)`. The record was repaired to contain the
entire theorem signature up to its final `:= by`, and the second dry run passed.
