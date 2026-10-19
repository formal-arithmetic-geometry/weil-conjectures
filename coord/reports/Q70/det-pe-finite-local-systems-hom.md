## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantHom` states all three clauses of
`det-pe-finite-local-systems-hom`. Its three theorem proofs are `sorry`:
`AlgebraicGeometry.ProEtale.finiteConstantHom_presentation`,
`AlgebraicGeometry.ProEtale.finiteConstantHom_constant`, and
`AlgebraicGeometry.ProEtale.finiteConstantHom_automorphisms`.
Every helper has real data, and every declaration is recorded in `lean.declarations`.
No statement correction, disputed statement, new definition node, or dependency repair is needed.

Hypotheses and objects:

- The scheme is `(X : Scheme.{u})`; the original small site is `X.ProEt` with
  `Scheme.ProEt.topology X`. The etale site is `X.Etale` with `X.smallEtaleTopology`.
  Site objects remain in `u+1` and arrows in `u`; they are never identified.
- A discrete commutative ring is `(Λ : Type (u+1)) [CommRing Λ]`. There is no topology
  or finite-cardinality hypothesis. Values of modules, sets, and groups are in the
  common larger universe `u+1`; all universes and variables are explicitly bound.
  This is the usual common-universe convention: any given scheme and discrete ring
  may be placed in such universes (with the canonical lift of a smaller coefficient
  ring if necessary). No mathematical ring or module is excluded by finiteness or
  a relation between the site's object and morphism universes.
- `finiteConstantHomRing` is the existing `constantSheaf` in `CommRingCat`.
  `FiniteConstantHomModules` abbreviates the recorded `ringedSiteModules` over its
  underlying `RingCat` sheaf. Thus `N` is an arbitrary intrinsic Lambda_X-module
  sheaf, not a finite, classical, constant, or fixed-scalar-valued target.
- `finiteConstantHomFunctor` abbreviates the existing `constantModuleHomFunctor`.
  This is the real constant module presheaf, module sheafification, and canonical
  `constantModuleHomRingIso` coefficient transport required by the recorded internal
  Hom. It is the constant module denoted nu_X^* M_Et in the source. The identification
  follows from their common universal property: both module functors are left
  adjoint to module global sections, since the site inclusion preserves the terminal
  object. Their scalar-ring comparison is the constant-ring sheafification comparison.
  No alternative module action or arbitrary comparison map is assumed.

Clause (1):

- `m n : ℕ`, `a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)`, and
  `b : (Fin n → Λ) →ₗ[Λ] M` give the displayed two finite free modules and quotient.
  `Function.Exact a b` and `Function.Surjective b` say exactly that
  Λ^m -> Λ^n -> M -> 0 is exact; no injectivity of a or projectivity of M is imposed.
- The source of the equivalence is the sections of the recorded
  `SheafOfModules.homObj ((finiteConstantHomFunctor X Λ).obj M) N`.
- `finiteConstantHomScalar` is the actual constant-ring sheafification unit.
  `finiteConstantHomTranspose` sends a tuple x to the tuple whose k-th component is
  sum_i eta(a(e_k)_i) • x_i, with eta that unit. The target of each `e N U` is
  `LinearMap.ker` of precisely that linear map. A linear equivalence at every U,
  natural under restriction, is the sectionwise description of an isomorphism of
  module sheaves with the kernel sheaf; kernels and finite products are sectionwise.
- The first equation says its i-th coordinate is phi(b(e_i)), evaluating the actual
  slice morphism at the terminal slice object. This fixes the canonical comparison.
  The second equation gives restriction naturality along every `f : U ⟶ V`.
  The third equation gives naturality for every target map `g : N ⟶ N'` through
  the recorded `SheafOfModules.homObjMap`.

Clause (2):

- `σ` compares the underlying set sheaf of each existing constant module with the
  ordinary constant set sheaf, and its first equation fixes it on every constant
  section through the two sheafification units. Thus these are canonical comparisons,
  not unconstrained bijections or an invented realization functor.
- `c P Q` is a morphism of intrinsic module sheaves from the constant module on
  `P →ₗ[Λ] Q` to the recorded `homObj`. Its formula sends every constant linear map
  f to the restriction of the actual constant-module map C(f). Naturality on the
  site is part of being a sheaf morphism. Local generation by constant sections
  determines this comparison uniquely.
- `IsIso (c P Q)` is asserted with exactly the two
  `[Module.FinitePresentation Λ P]` and `[Module.FinitePresentation Λ Q]`
  hypotheses of the clause. Its inverse is the isomorphism in the node's direction.
  Defining the canonical comparison for arbitrary modules does not assert it is
  invertible there.
- The composition equation applies to *arbitrary sections* f and g on every U,
  not just globally constant maps. `finiteConstantSetComposition` is constructed
  from the inverse finite-product comparison for `constantSheaf` followed by the
  image of ordinary composition. `finiteConstantHomPair` uses the canonical
  evaluation-product comparison; it never assumes that a chosen categorical product
  is definitionally a pair. `finiteConstantModuleComposition` transports this map
  by the unit-normalized σ. The equation states that c takes it to actual composition
  of the local linear sheaf maps. The last equation includes preservation of identity.

Clause (3):

- The existential `A : Sheaf (ProEt.topology X) GrpCat` and multiplicative equivalences
  `e U` characterize its sections as `Aut` of the actual restricted constant-module
  presheaf on `Over U`. Forgetting sheaf structure on the slice is fully faithful,
  so these are exactly module-sheaf automorphisms. The restriction equation specifies
  their hom components on every further slice object W. Inverses restrict along the
  same maps, and multiplicative equivalences preserve the complete group law.
- The first isomorphism identifies A with the genuine `constantSheaf` in `GrpCat`
  on `Aut M`. Its normalization sends a constant automorphism to the restricted
  image under the existing constant-module functor, including the actual inverse.
- The next isomorphism is in the category of group sheaves and has target the actual
  `Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) GrpCat` applied
  to the constant *etale* group sheaf on `Aut M`. This is exactly nu_X^* Aut(M)_Et,
  not just a set-valued bijection or a commutative-group specialization.
- `IsClassical` of its underlying set sheaf is the recorded bijectivity of every
  affine-presentation continuity map, including all cofiltered presentation categories.
  There is no finiteness or commutativity assumption on the automorphism group.

The group-valued functors needed four support instances. They assemble existing
`GrpCat.FilteredColimits.colimitCocone` and `colimitCoconeIsColimit`, Mathlib's
`hasFilteredColimitsOfSize_of_univLE`, the `structuredArrowOpEquivalence` for the
existing flat inclusion, and the pointwise Kan extension instance. These are explicit
uses of existing constructions, without any new theorem proof or postponed data.
The definitional finite-limit instance inside `finiteConstantSetComposition` is
inferred for the actual constant-presheaf/sheafification composite; it introduces
no assumption into any statement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale` and `Scheme.smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the original `Scheme.ProEt`
  site and the constant-ring intrinsic coefficient convention used by
  `Scheme.proEtaleDerivedCategory`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf` and
  its defining constant-presheaf/sheafification construction.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  the current recorded original-site `Scheme.proEtaleSiteComparison`.
  The original `Scheme.toProEt` inclusion and
  `Functor.sheafPullbackConstruction.sheafPullback` are used on the original sites,
  as required by this item's statement.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj` and `SheafOfModules.homObjMap`; its presheaf source supplies
  `PresheafOfModules.restrictOver`, the exact local linear Hom category.
- `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`: `AlgebraicGeometry.ProEtale.IsClassical`.
  During the task the classical-definition node's existing record was published;
  the final delivery uses it and needs no duplicate definition or dependency repair.
- Added landed dependencies `def-sf-site-constant-module-functor` and
  `lem-pur-site-constant-module-hom`: their recorded modules are
  `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral` and
  `Sheaf.CategoryTheory.SiteConstantModuleHom`. The declarations used are
  `siteConstantModuleFunctorGeneral`, `constantModuleHomRingIso`,
  `constantModuleHomFunctor`, and `constantModuleHomUnit`; the recorded theorem
  `siteConstantModule_hom` is available for the eventual clause-(2) proof.
- The already-stated proof dependencies
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  (`CategoryTheory.moduleSheaves_colimits_forgetful`) and
  `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`
  (`CategoryTheory.siteRestriction_exact`) are non-public proof imports.
  The now-landed `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules` and
  `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage` are also non-public proof
  imports. Remaining proof nodes with no Lean binding are cited in the proof
  docstrings; no nonexistent module or invented replacement theorem is imported.

Edge cases checked before the statement was written: X empty; Lambda the zero ring;
m=0; n=0; M=0; a noninjective presentation matrix; noetherianity not assumed;
N arbitrary, including zero, nonclassical and nonconstant targets; disconnected X
and sections that are only locally constant; infinite and nonabelian Aut(M).
In rank zero the tuple is empty, its kernel is the zero module, and exactness forces
the corresponding zero quotient as it should. With m=0 the transpose has zero target
and the kernel is the full finite product. All formulas retain the empty cases.
No exactness of the section functor or constancy of its global sections is used.

Searches for an existing statement, made with the prescribed msearch wrapper:

- leanfinder: "Internal Hom from a finitely presented constant module sheaf is the
  kernel of the transpose presentation and automorphism sheaf is constant".
  Eight hits, including `LightCondensed.ihomPoints`, `PresheafOfModules.freeHomEquiv`,
  `SheafOfModules.Presentation.mapGenerators`, and `SheafOfModules.unitHomEquiv`;
  no theorem with the three pro-etale clauses.
- loogle: `"constantSheaf", "hom"`: zero hits.
- grep: `constantSheaf.*(Hom|hom|[Aa]ut)|[Hh]om.*constantSheaf|[Aa]ut.*constantSheaf`:
  six hits, all in generic GlobalSections and SheafCohomology/Basic; no match.
- leansearch: "Internal Hom of finitely presented constant module sheaves and their
  automorphism group sheaves on the pro etale site": eight generic Hom and sheaf Hom
  hits, no match.
- Direct source and side-library rg searches for the item id, `homObj` with constant
  sheaves, `constantModule`, and automorphism/classical interfaces found the existing
  generic constant-module and Hom modules listed above. These are reused. The
  generic `siteConstantModule_isomSheaf` is only a set-valued isomorphism-sheaf theorem
  on a small-category precoverage; it supplies neither clause (1), the arbitrary
  local composition equation of (2), nor the group-valued comparison/classicality
  of (3). No declaration gives this entire item's statement. Searches for all newly
  chosen declaration names in upstream and `lean/Sheaf` returned no collisions.

Validation: `scompile.py Q70 det-pe-finite-local-systems-hom` compiled the complete
module as a sandbox file and at its library module path, cleanly (4.8 s and 5.7 s).
All three theorem proofs are the expected stage-2 sorries. An initial dry run
completed the compilation and server preflight; this report now records the
independent second reading below.

## Second reading by Q70

I opened the node, its blueprint proof, every recorded statement dependency, and
`Sheaf/AlgebraicGeometry/ProEtaleFiniteConstantHom.lean` independently. The
item-by-item match is as follows.

- The ambient objects are `X : Scheme.{u}`, `Λ : Type (u + 1)` with
  `[CommRing Λ]`, `M : ModuleCat.{u + 1} Λ`, and a finite presentation represented
  by `m n : ℕ`, `a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)`, and
  `b : (Fin n → Λ) →ₗ[Λ] M`, with `Function.Exact a b` and
  `Function.Surjective b`. This is exactly the node's arbitrary scheme, discrete
  commutative ring, module, and finite presentation; no finiteness, Noetherian,
  characteristic, or injectivity hypothesis is added.
- `finiteConstantHomRing`, `FiniteConstantHomModules`, and
  `finiteConstantHomFunctor` render the constant ring, intrinsic module-sheaf
  category, and constant module sheaf. The latter is the canonical sheafification
  construction from the added `def-sf-site-constant-module-functor` dependency,
  while the comparison-pullback construction in clause (3) is the recorded
  `ν_X^*` construction. Thus no private or arbitrary coefficient map is used.
- Clause (1) is `finiteConstantHom_presentation`: its `e N U` is the sectionwise
  linear equivalence from `SheafOfModules.homObj` to the kernel of the displayed
  transpose. The three following conjuncts are respectively the basis-value
  formula, restriction naturality for every `f : U ⟶ V`, and naturality for every
  target morphism `g : N ⟶ N'`. `finiteConstantHomTranspose` uses the actual
  constant-ring unit and the coefficients `a (Pi.single k 1) i`, so it is the
  stated transpose, including `m = 0` and `n = 0`.
- Clause (2) is `finiteConstantHom_constant`: `σ` records the canonical
  underlying-set comparison, and `c P Q` is the canonical map from the constant
  sheaf of `P →ₗ[Λ] Q` to the internal Hom. `IsIso (c P Q)` is required exactly
  under `[Module.FinitePresentation Λ P]` and
  `[Module.FinitePresentation Λ Q]`. The next conjunct gives composition on
  arbitrary local sections and the final conjunct gives identity, so it is the
  node's compatibility with composition rather than only a global-sections claim.
- Clause (3) is `finiteConstantHom_automorphisms`: `A` is a sheaf of groups,
  `e U` identifies every local section with the automorphism group of the actual
  restricted constant module, and the first equation gives restriction on every
  slice object. The `α` normalization identifies these groups with `Aut M`; the
  `Nonempty` group-sheaf isomorphism is precisely the pullback of the constant
  etale group sheaf along `Scheme.toProEt X`; and `IsClassical` is imposed on its
  underlying set sheaf. No commutativity or finiteness of `Aut M` is assumed.

I checked the edge cases `X` empty, the zero ring, `M = 0`, `m = 0`, `n = 0`, a
noninjective presentation map, disconnected schemes, and nonconstant or zero
targets `N`. The displayed finite products and kernels retain their empty and
zero interpretations. The universe choice keeps site objects in `u + 1` and
arrows in `u`, with coefficient values in `u + 1`; it does not identify those
universes or exclude a smaller ring by a mathematical finiteness condition.

For the independent notion search I ran LeanFinder on “Internal Hom from a
finitely presented constant module sheaf is the kernel of the transpose
presentation and automorphism sheaf is constant” (generic Hom/free/presentation
hits only), Loogle on `constantSheaf hom kernel` (no hits), and grep for
`constantSheaf.*(Hom|hom|Aut|aut)|homObj.*constant|constant.*homObj` in Mathlib,
the slopmaster2 source, and `lean/Sheaf` (only generic constant-sheaf and
section lemmas). No declaration gives this three-clause statement. The two
additional dependency records in the sandbox node are landed canonical
constant-module functor/Hom interfaces and are used by the module; neither is a
duplicate definition.

No mismatch was found. I changed no Lean declaration or node statement. I only
added this second-reading record and refreshed the search log. The module was
recompiled with `scompile.py`; it compiled both as the sandbox file and at its
library module path with only the three intended `sorry` proofs.

Resumed second-reading validation, 2026-10-17:

I retained the review above and reopened the complete module, the current item and
all eleven statement-dependency records and their relevant source declarations.
The blueprint statement and proof at the node's exact source path agree with the
eight-step expanded DAG proof. I also read Stacks `sites-modules.tex`, Tags 03CY,
03DA, 03DB, 093T and 0E8H: these assume a site and the stated ring/module data,
without a finite ring, points, Noetherian scheme, or characteristic restriction.
The finite-presentation Hom assertion and slice restriction are exactly the
interfaces used here. No source-based statement correction is required, and
there are no new nodes or dependency modules in this delivery.

The only new mismatch was the import list becoming stale: the current comparison
node records `ProEtaleSiteComparison` directly, and the two proof dependencies
`det-pe-classical-sheaves-modules` and `det-pe-classical-sheaves-image` now have
landed modules. I replaced the small-model comparison import with that recorded
original-site module and added the two non-public proof imports. Their import
closures do not reach this item, so these additions create no import cycle.
No definition, theorem signature, node statement, or dependency record was changed.
The earlier paragraph reporting no mismatch describes the interrupted review;
this paragraph records the current-source repair.

Independent searches were refreshed using LeanFinder for “Sheaf of automorphisms
of a finitely presented locally constant module is the constant group sheaf”
(eight generic condensed constant-module hits), Loogle for `"constantSheaf", "Aut"`
(zero hits), and LeanSearch for “Finite presentation computes sheaf Hom as the
kernel of a finite matrix transpose” (generic finite-presentation hits). Direct
`rg` over Mathlib, upstream `WeilConjectures` and the project's `lean/Sheaf` for
constant sheaf Hom/automorphism combinations and the proposed theorem names
found the already-reused generic constant-module Hom interface, with no existing
three-clause statement or declaration-name collision.

All edge-case verdicts above still hold. In particular, there is no nonempty-rank
hypothesis, and group sheaves are valued in `GrpCat`, allowing infinite nonabelian
automorphism groups. The original site keeps independent object/arrow sizes.
The node's `lean.statement` is verbatim the first theorem signature; all variables
are bound under `autoImplicit false`, no line exceeds 100 characters, and the
only three `sorry`s are the whole proofs of the three named theorems.

After the import repair, the prescribed `scompile.py` compiled both sandbox and
library placements cleanly (4.1 s and 5.0 s).
The resumed `deliver2.py --no-push` passed server preflight and compilation,
reporting `OK (dry run)` at commit `cf397aab64`.
