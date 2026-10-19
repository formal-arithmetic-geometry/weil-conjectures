## Worker report

Item: lem-trf-derived-sections-finite-pushforward-modules. Group Q48, stage 2.
Module: `Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules`.
Main declaration: `AlgebraicGeometry.Etale.derivedSectionsFinitePushforwardModules`.

The module states the entire node, using the existing natural finite-pushforward
Leray isomorphism rather than constructing or existentially choosing another one.
Its only postponed proof is this item's theorem. Two real-data helper definitions
make the exact derived counit mate and the resolution comparison readable. Their
source/blueprint docstrings identify this node. Neither helper chooses a map from
an existence assertion or contains a postponed proof.

The source read was Stacks `etale-cohomology.tex`,
`proposition-finite-higher-direct-image-zero` (03QP), together with
`derived.tex`, `lemma-compose-derived-functors` (015M), and the pullback/adjunction
construction in `sites.tex`, `section-pullback`. The module proof docstring follows
all six steps of the DAG proof, including the module-linear section calculation
and the module restriction-resolution lemma; it does not replace that calculation
by abelian-derived base change.

Hypotheses and objects, clause by clause:

* The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`, with no nontriviality,
  characteristic, torsion, or invertibility restriction.
* The schemes are `{Z Y : Scheme.{u}}`, and `(p : Z ⟶ Y) [IsFinite p]` is exactly
  the finite scheme morphism. No properness, separation, Noetherian, or surjectivity
  hypothesis is added.
* `M : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ` is the
  complex of actual module-valued sheaves on the recorded small étale site.
  `(a : ℤ) [M.IsStrictlyGE a]` supplies an arbitrary lower bound. In particular
  there is no upper bound. `DerivedCategory.Q.obj M` is its derived object.
* This is the project's specified constant-coefficient `Sheaf … (ModuleCat Λ)`
  encoding (standing brief §2), not a new definition of module sheaves. It has
  sectionwise scalar-linear morphisms. The recorded general ringed-site category
  `CategoryTheory.ringedSiteModules` is the transparent Mathlib `SheafOfModules`
  abbreviation; constant-ring modules have the equivalent module-valued sheaf
  encoding. The existing `Scheme.etaleConstantModuleFunctor_isEquivalence` construction in
  `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence` verifies this
  equivalence. We do not change the recorded dependency or invent another module
  category. Coefficients and values use `u+1`, as required by the existing étale
  derived-functor API. This accommodates arbitrary coefficient rings; no equality
  between different object/morphism universes of a pro-étale site is imposed.

Conclusions, clause by clause:

1. The first two conjuncts are `PreservesFiniteLimits (lowerStar … p)` and
   `PreservesFiniteColimits (lowerStar … p)`. For this additive functor of abelian
   module-sheaf categories these express exactness. The third conjunct is
   `(lowerStar … p).PreservesInjectiveObjects`.
2. The canonical natural isomorphism is the existing
   `mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p`.
   Its source is `p_*.mapDerivedCategory ⋙ RΓ(Y,-)` and its target is `RΓ(Z,-)`.
   Its component at `Q.obj M` is precisely the node's `λ_{p,M}`. The published
   declaration is an actual natural isomorphism, so naturality and invertibility
   are supplied by its type, rather than replaced by an arbitrary chosen arrow
   or an existential nonempty isomorphism. Its definition uses the canonical
   exact/right-derived identification followed by the canonical Leray comparison.
3. The fourth conjunct quantifies over EVERY `L`, EVERY lower bound `b`, EVERY
   termwise-injectivity instance `[∀ n : ℤ, Injective (L.X n)]`, and EVERY
   quasi-isomorphism `(i : M ⟶ L) [QuasiIso i]`. Its conclusions assert that
   termwise `p_*i` is a quasi-isomorphism, that `p_*L` has lower bound `b`, and
   that each `p_*(L.X n)` is injective. Thus it really asserts that the given
   pushed-forward resolution is a bounded-below injective resolution.
4. `finitePushforwardSectionsUnit Λ X L` is the canonical arrow
   `Q(Γ(X,L)) ⟶ RΓ(X,Q L)`, obtained from the existing right-derived-functor unit
   and the canonical quotient-to-homotopy-derived comparison. It has real data
   without an injectivity assumption. The normalization conjunct explicitly says
   that this arrow is invertible for BOTH `L` and `p_*L` above.
5. The normalization EQUATION starts at `Q Γ(Y,p_*L)` and ends at `RΓ(Z,Q L)`.
   Its left side passes through that resolution comparison, the inverse of the
   exact functor's canonical `mapDerivedCategoryFactors` comparison, `p_*(Q i)⁻¹`,
   `λ_{p,M}`, and `RΓ(Z,Q i)`. Its right side is the localization of the TERMWISE
   identification `Γ(Y,p_*L) ≅ Γ(Z,L)` followed by the resolution comparison on Z.
   This is exactly the assertion that `λ_{p,M}` is induced by that identification
   on the specified injective resolution. The inverse of `Q i` exists because i
   is a quasi-isomorphism; no inverse of an unproved comparison is assumed.
6. The last conjunct quantifies over arbitrary `(Y' : Scheme.{u}) (h : Y' ⟶ Y)`.
   The pullback scheme is Mathlib's `pullback h p`, with
   `g = pullback.snd h p` and `p' = pullback.fst h p`. Finiteness of p' is inferred
   by finite base change, not added as a new hypothesis.
7. `finitePushforwardDerivedMate` constructs β using `mateEquiv` for the exact
   localized adjunctions. Its comparison is the exact localization of the
   existing `squareUpperStarIso`, transported through
   `Functor.mapDerivedCategoryCompIso`. Thus its transpose is the pullback of
   the p-counit through the canonical inverse-image composition comparison,
   exactly as in the node. It does not take β or an isomorphism property as input.
   The underlying ordinary mate already exists as `baseChangeMap`; this helper
   gives its exact unbounded derived interface. The upstream derived base-change
   interface is bounded-below, while this square lives in the recorded unbounded
   derived categories. The exact-localization mate uses the same canonical
   adjunctions and comparisons, rather than a different base-change construction.
8. Each restriction arrow is written out as `RΓ.map (adjunction.unit.app _)`
   followed by `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`.
   The restriction adjunction is the existing
   `mapDerivedUpperStarLowerStarAdjunction`; there is no arbitrary restriction
   map parameter. The final equation says `λ_p ≫ res_g = res_h ≫ RΓ(β) ≫ λ_p'`,
   including the component of β and the bottom λ at the pulled-back complex.
   Both sides have the same source and target in `DerivedCategory (ModuleCat Λ)`.
   There is no hypothesis asserting that β is invertible.

Recorded statement dependencies used/imported:

* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (the general ringed-site encoding; the constant-coefficient encoding is
  explained above).
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
* `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`. This recorded theorem's
  inverse image is the module-linear transport of the canonical sheaf adjunction.
  The statement uses those canonical module-valued `upperStar` functors directly.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`,
  `upperStarLowerStarAdjunction`, and `upperStarComp`.

Other canonical APIs used are imported publicly from
`WeilConjectures.SixFunctors.Finite.GlobalSections` (the natural λ),
`WeilConjectures.SixFunctors.BaseChange.Square` (`squareUpperStarIso`),
`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`
(`Adjunction.mapDerivedCategoryAdjunction`), and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
(the existing comparison API whose unit is transported by the helper).

The recorded, already stated proof dependencies are imported without `public`:
`WeilConjectures.SixFunctors.Finite.Exact`
(`preservesFiniteColimits_lowerStar_of_isFinite`),
`Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
(`existsUnique_constantModuleDirectImage_leftExact`),
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
(`CategoryTheory.moduleSheaves_colimits_forgetful`),
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`
(`Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`),
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
(`Scheme.etaleModule_enoughInjectives`),
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
(`DerivedCategory.Plus.exists_injective_nonempty_iso`),
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`
(`CochainComplex.IsKInjective.Qh_map_bijective`),
`Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
(`Functor.rightDerivedFunctorPlus` and its unit),
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective` (the second clause of
finite-radicial-basechange), and `Mathlib.CategoryTheory.Sites.ConstantSheaf`
(`CategoryTheory.constantSheaf`). The remaining already imported recorded proof
modules are also public statement dependencies. The proof-only node
`lem-trf-module-derived-restriction-resolution` had no Lean record or Mathlib
match in the returned delivery. This repair supplies and imports
`Sheaf.TraceFormula.ModuleDerivedRestrictionResolution`; see Dependency modules below.
Its canonical unit, restrictions and comparisons use the existing derived functor API.

Edge cases checked before finalizing: the zero coefficient ring is allowed;
the zero complex and negative or arbitrary lower bounds are allowed; `b` need
not equal `a`; no resolution is preferred and i need not be the identity; empty
schemes are allowed; h may be an identity, empty-source map, or any nonfinite
map; p need not be surjective. Exactness of inverse image and finiteness of p'
are consequences of the existing APIs in these cases. No clause becomes a
free choice of maps or an assumption of the desired compatibility.

Searches for prior declarations:

* `msearch.py leansearch`, query “Derived sections of finite pushforward of module
  sheaf complexes normalized by injective resolutions commute with pullback”:
  eight hits, ordinary module pushforward/sections/pullback APIs, no complete match.
* `msearch.py leanfinder`, query “For finite morphisms of schemes derived global
  sections of pushforward of module sheaf complexes commute with restriction and
  the adjunction base change mate”: eight hits, ordinary scheme-module adjunctions
  and pushforward sections, no complete match.
* `msearch.py loogle`, query `"mapDerivedCategory"`: twelve generic exact-derived
  functor hits. The search service includes APIs newer than the pinned library;
  the actual pinned source was read before using any declaration.
* `msearch.py grep`, query
  `rightDerivedFunctorObjQIso|finitePushforwardDerivedMate|derivedSectionsFinitePushforwardModules`
  in `CategoryTheory`: zero Mathlib hits.
* Direct `rg` of Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf` for
  derived finite sections, base change, and exact localization found the published
  finite natural λ, generic derived-functor units/comparisons, the ordinary
  `baseChangeMap`, and the bounded-below derived base-change interface. None states
  this item's injective normalization AND arbitrary-restriction square.
* A direct upstream search for the item ID and searches of all three source trees
  for the three proposed declaration names gave no existing declaration with
  those names. The helper definitions supply only the canonical transports needed
  to state this node; no independent mathematical notion or theorem was added.

The repair supplies one existing DAG prerequisite as a dependency module. There
are no new DAG nodes or statement changes. Both copied nodes change only in `lean`.
There is no disputed statement: the source supports the stated compatibility.

Validation: `scompile.py Q48 lem-trf-derived-sections-finite-pushforward-modules`
compiled the sandbox and library-shaped file cleanly, with no diagnostics. The
final delivery dry run also rechecks the final docstrings and signature. All
variables and the universe are explicit; `autoImplicit` is disabled. Definitions
have real data, and each of the two theorems has proof `by sorry`.

## Second reading by Q48

The dispatcher worker reread the original node beside the final source and checked
each clause above. This is a second reading by the same worker, not a claim that
another agent reviewed it: the dispatcher brief expressly forbids starting other
agents and assigns the independent delivery review to the maintainer.

During this rereading the draft was repaired to include the full normalization
for every resolution, including its quasi-isomorphism, bound and injective terms,
and the exact unit/counit square with canonical arrows. The final equation for
normalization uses the forward resolution units so their invertibility is a
conclusion, not an additional typeclass hypothesis. The final statement has no
`True` placeholder, unspecified mate, weakened compatibility, local notation,
statement `let`, hidden auto-bound variable, or new mathematical assumption.
The natural λ is reused, not chosen. The node statement and all dependency lists
are unchanged. The maintainer's independent review remains the next review step.

## Dependency modules

`lem-trf-module-derived-restriction-resolution` was a genuine DAG prerequisite named by
proof step 6 but had no Lean record or Mathlib match in the returned packet. I supplied
its existing statement as `Sheaf.TraceFormula.ModuleDerivedRestrictionResolution`, with
real helper abbreviations and the postponed theorem
`AlgebraicGeometry.Etale.moduleDerivedRestrictionResolution`. The theorem gives exactly
the module-valued K-injective restriction/Leray identity used twice in step 6; its
copied node has a `lean.note` explaining this repair. Its statement and proof dependency
lists remain unchanged. The parent imports this module without `public`, since it is
used in proof step 6. The parent node's `stmt_deps` now explicitly includes
`lem-trf-module-derived-restriction-resolution`, so the supplied dependency module has a
complete DAG record and is available to the delivery preflight.


The prerequisite's hypotheses and clauses are rendered as follows:

* `{T T' : Scheme.{u}} (u : T' ⟶ T)` and arbitrary
  `(Λ : Type (u + 1)) [CommRing Λ]` express the schemes, morphism and coefficient ring.
* `moduleInjectiveComplex` abbreviates the existing module-valued sheaf-complex category.
  `I : moduleInjectiveComplexPlus T Λ` and the analogous J use
  `CochainComplex.Plus (InjectiveObject ...)`: these encode exactly arbitrary
  bounded-below complexes all of whose terms are injective. The underlying-complex
  abbreviation is the termwise injective inclusion, with real data and no choices.
* `a` is any chain map from termwise `upperStar ... u` applied to I to J.
  It has no `QuasiIso` assumption. The functor is the canonical exact constant-module
  inverse image used in the parent statement.
* `w` and `hw` specify the section chain map componentwise as
  `globalSectionsUpperStarMap ... u (I.X i) ≫ Γ.map (a.f i)`. This is precisely
  degreewise unit followed by the ordinary direct-image/sections identification,
  then sections of a. Naturality constructs this chain map, and componentwise equality
  makes it unique; this encoding adds no mathematical hypothesis.
* `rightDerivedFunctorObjQIso I` has orientation `RΓ(Q I) ≅ Q Γ(I)`. Its `hom`
  is therefore `alpha_I` inverse and the corresponding `inv` for J is `alpha_J`.
  These are canonical comparisons on K-injectives, rather than arbitrary isomorphisms.
* The right side is `RΓ.map` of the derived adjunction unit, followed by
  `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`, and `RΓ.map` of Q(a).
  `mapDerivedCategoryFactors.hom.app I` identifies exact inverse image of Q(I)
  with Q of termwise inverse image, with the required orientation.
  The equation has the node's two sides exchanged, which preserves its meaning.

The prerequisite's statement-dependency modules are publicly imported:
`Mathlib.AlgebraicGeometry.Scheme` (Scheme),
`Mathlib.AlgebraicGeometry.Sites.Etale` (smallEtaleTopology),
`Mathlib.CategoryTheory.Sites.ConstantSheaf` (constantSheaf),
`Sheaf.CategoryTheory.RingedSiteModules` (ringedSiteModules),
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
(etaleInverseImageModulesExact),
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (upperStar, lowerStar and adjunction),
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` (rightDerivedGlobalSections),
`Mathlib.Algebra.Homology.DerivedCategory.Basic` (Q), and
`Mathlib.CategoryTheory.Preadditive.Injective.Basic` (Injective).
The additional GlobalSections, Coherence and KInjective imports provide the explicit
canonical section map, Leray comparison and resolution comparisons appearing in the type.

The supplied prerequisite also imports its recorded proof dependencies without `public`:
EtaleModuleEnoughInjectives, the upstream Injective.Preserves and HomotopyCategory.Adjunction
modules, Mathlib DerivabilityStructureInjectives, RightDerivedFunctorPlus, ExactFunctor,
KInjective and Adjunction.Basic, and the side KInjectiveDerivedMapComputation and
KInjectiveResolutionsExist modules. The theorem docstring gives all five proof steps
with the dependency ids, including the derived transpose and Leray normalization.

The prerequisite edge cases checked are identity morphisms, empty source or target
where a morphism exists, zero coefficients, zero complexes, distinct arbitrary lower
bounds, arbitrary non-quasi-isomorphic a, and the zero chain map. The parameter w is
fixed by hw, including in these cases. Neither finiteness nor injective preservation
of inverse image is assumed.

The existing prerequisite node's ten recorded LeanSearch, LeanFinder, Loogle and Mathlib
grep searches find no exact complete module-valued formula; their results are retained
verbatim in its node. The read-only upstream and side-source searches for
`moduleDerivedRestrictionResolution`, right-derived comparisons and section restriction
found the existing canonical APIs and abelian-valued analogues, but no landed declaration
for the exact prerequisite. I retained the previously compiled NU statement interface,
added its full proof docstring and recorded proof imports, and listed all real helper
abbreviations in `lean.declarations`.

## Second reading of the repair by Q48

I reread both node statements and both Lean modules without delegation, as required by
the dispatcher. The parent theorem's signature is unchanged. The repair supplies the
missing genuine prerequisite and imports it for step 6. The prerequisite's injective
wrapper imposes exactly boundedness and termwise injectivity; its `w` parameter is
uniquely specified by hw. The resolution isomorphism orientations give exactly the
node's alpha_J followed after Q(section map) and alpha_I inverse. No quasi-isomorphism
condition on a or finite-morphism hypothesis was introduced. Helper docstrings now name
the source and blueprint, and the postponed proof records all five DAG steps.
Both node copies retain every non-lean field of the current shared DAG.
