## Worker report

The module `Sheaf.Algebra.Homology.RhomGlobalSections` states
`CategoryTheory.rhom_global_sections`, with its proof `sorry`. It gives the canonical
identification as a natural family of additive equivalences, using the existing
`CategoryTheory.derivedInternalHom`. No existing notion has been copied. The companion
module defines the missing general ringed-site zeroth hypercohomology by composing existing
functors, with full data and no `sorry`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A site with small underlying category: `{C : Type u₁} [SmallCategory C]` and
  `(J : GrothendieckTopology C)`. Objects and morphisms live in the same universe.
- A sheaf of commutative rings: `(R : Sheaf J CommRingCat.{u₁})`.
- The abelian category of O-modules: `SheafOfModules.{u₁}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)`. This is the general-site
  `mathlib_match` of `def-weil-sheaf-of-modules-category`, explicitly allowed by its
  `lean.note`; the recorded `Scheme.Modules` specialization does not apply to this site.
  The existing small-site sheafification instances supply its abelian structure.
- Its derived category: `DerivedCategory` with `[HasDerivedCategory.{w₁} ...]`.
  The latter chooses the localization and its morphism universe, as specified in the
  size convention of `def-weil-abstract-derived-category`; it is no additional
  geometric or cohomological hypothesis.
- Global sections equal Hom from the unit O-module: the companion definition uses
  `preadditiveCoyoneda.obj (op (SheafOfModules.unit ...))`. By `unitHomEquiv` this is
  the additive group of compatible global sections, including when C has no terminal object.
- H⁰(C,K) computed on a K-injective representative: `ringedSiteZerothHypercohomology J R`
  is this sections functor's `rightDerivedFunctor` followed by
  `DerivedCategory.homologyFunctor AddCommGrpCat 0`. The existing
  `Functor.rightDerivedFunctorObjQIso` computes it on any K-injective complex by termwise
  sections; `homologyFunctorFactors` computes H⁰. Thus it also supplies canonical
  independence of representatives. The Grothendieck structure is obtained from
  `grothendieckAbelian_and_functorial_kInjective_resolutions`, and the upstream
  Grothendieck K-injective resolution instance is used, with no added instance hypothesis.
- Arbitrary L,M in D(O): each `P` ranges over `D(O)ᵒᵖ × D(O)`, so L is `P.1.unop`
  and M is `P.2`.
- Derived internal Hom: `(derivedInternalHom J R).obj P`, precisely the dependency's
  recorded declaration, with no alternative derived Hom construction.
- The canonical isomorphism: `e P : H⁰(C,RHom(P)) ≃+ (P.1.unop ⟶ P.2)`.
  Additive equivalences express the asserted isomorphism of abelian groups even when
  the chosen localization has morphisms in a different universe.
- Canonical/natural dependence: for every `f : P ⟶ P'` and every cohomology class x,
  `e P' (H⁰.map (RHom.map f) x) = f.1.unop ≫ e P x ≫ f.2`.
  This is the natural-isomorphism equation for the Hom bifunctor, contravariant in L
  and covariant in M, not just unrelated equivalences of sets. Choice-independence
  is built into H⁰ and RHom, both already functors on the localization.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `SheafOfModules.unit`,
  `SheafOfModules.unitHomEquiv`, `SheafOfModules.unitHomEquiv_comp_apply`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
  It occurs through the existing right-derived-functor construction and comparison API;
  no second K-injectivity definition is introduced.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`;
  its comparison declarations were also read.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
  (and its imported `Defs`): `Functor.rightDerivedFunctor`,
  `Functor.rightDerivedFunctorObjQIso`.
- `Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`: `preadditiveCoyoneda`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `DerivedCategory.homologyFunctorFactors`.

Edge cases checked mathematically before writing: empty site, zero ring sheaf, and zero
L or M give zero groups on both sides. No terminal object of C is required: global sections
are Hom from O rather than evaluation at a chosen object. The category need not be a scheme,
a topological space, or an étale site. No boundedness, flatness, degreewise injectivity,
nonempty-site, or characteristic hypothesis was added. All cochain indices are integers,
including negative degrees. Morphism universe w₁ is independent of u₁; the additive
equivalence permits different universes without excluding the chosen derived category.

Searches made (msearch.py invoked with group H1 and this item):

- LeanFinder, `global sections of derived internal Hom are morphisms in the derived category`:
  eight Ext-related results; none is the sheaf-valued RHom global-sections statement.
- Loogle, `CochainComplex.IsKInjective, DerivedCategory`: two generic localization
  bijectivity results, including `CochainComplex.IsKInjective.Qh_map_bijective`.
- Mathlib grep, `derivedGlobal|globalSections|RHom`, subdirectory `Algebra/Homology`:
  reported 25 hits from generic bifunctor/monoidal files; no exact statement.
- LeanSearch, `global sections derived internal Hom`: unavailable, Internal Server Error.
- `rg` of `globalSections|derivedGlobal|RHom|lem-pur-rhom-global-sections` in the source
  CategoryTheory and Mathlib extensions: generic derived Hom/monoidal material, no exact
  ringed-site theorem. Search for the item id in all `WeilConjectures` returned no match.
- `rg` of global-sections/derived-global/rhom in project homology and category modules:
  the landed local K-injective comparison and derived internal Hom, but no global theorem.
- Full proposed declaration names searched in Mathlib, source, project and
  `dag/lean_names_upstream.json`: no collision.

The Stacks TeX file is absent on this machine. The source was opened directly at
https://stacks.math.columbia.edu/tag/08JA, Lemma 21.35.1: its global assertion is exactly
H⁰(C,RHom(L,M)) = Hom_D(O)(L,M); its proof uses a K-flat L and K-injective I and the
K-injectivity of their sheaf Hom complex. The theorem docstring carries all three node
proof steps and their dependencies. No statement correction or dispute was needed.

## New nodes

`def-pur-ringed-site-zeroth-hypercohomology` defines H⁰(C,-) on the unbounded derived
category of an arbitrary small commutative ringed site. Its source is Stacks Section 07A5
and the H⁰(C,-) appearing in Tag 08JA. Its own module is
`Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology`, declaration
`CategoryTheory.ringedSiteZerothHypercohomology`. This is the sections right derived functor
followed by H⁰; its data contains no sorry and no extra proof was introduced. It is needed
because no general ringed-site zeroth hypercohomology functor has a declaration or DAG node.

Before adding it, `blueprint_refs.py search hypercohomology` found eight spectral-sequence
nodes but no such definition; `rg -l` for global sections and K-injectivity in DAG nodes
found the item, scheme global RHom, and étale/cohomological comparison nodes. Reading
`def-pc-global-derived-rhom` confirmed that its base is a scheme and its target D(Γ(X,O_X));
`def-kun-rgamma-unbounded` is restricted to étale sheaves. Neither defines this notion.
LeanFinder queried `zeroth hypercohomology of sheaves of modules on a ringed site by K
injective global sections`: ordinary `Sheaf.H` and cohomology-presheaf results, no match.
Loogle queried `CategoryTheory.Functor.rightDerivedFunctor`: unknown identifier; the source
checkout does provide this generic functor and it is reused. Mathlib grep queried
`hypercohomology|derivedGlobalSections`: zero hits. The same patterns in the source Sites
and project returned only special-site/cohomology and spectral-sequence material.
LeanSearch was unavailable as recorded above. These searches are recorded in the new node.

The item's statement is unchanged; its stmt_deps only gains this definition node. There
are no dependency modules or corrections. The second reader must supply the independent
reading and deliver; this worker only runs `deliver2.py --no-push`.

## Second reading by H1

Independent second reader: I opened the item and new definition node, both delivered
modules, all five original statement dependencies and their recorded declarations, and
the generic right-derived-functor implementation and K-injective computation API. I read
Stacks Tag 08JA and Section 07A5 online, and fetched the source TeX into the sandbox
scratchpad. In sites-cohomology.tex I read section-unbounded and section-internal-hom,
including lemma-section-RHom-over-U and its proof. There are no standing Noetherian,
boundedness, characteristic, terminal-object, or geometric hypotheses at those places.

The node's object/hypothesis/conclusion list and its Lean correspondence follows.
Every entry passes.

1. A site with small underlying category: `{C : Type u₁} [SmallCategory C]` and
   `J : GrothendieckTopology C`. This is an arbitrary small site, without a selected
   terminal object or nonemptiness assumption.
2. A sheaf O of commutative rings: `R : Sheaf J CommRingCat.{u₁}`. The expression
   `((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)` forgets commutativity only
   when constructing its module category; it preserves O and all its restrictions.
3. The abelian category Mod(O): `SheafOfModules.{u₁}` of that ring sheaf. I read the
   Mathlib structure: it consists of a presheaf of modules with its underlying
   abelian presheaf a sheaf. This is the general-site declaration in
   def-weil-sheaf-of-modules-category's mathlib_match and expressly permitted lean.note;
   the recorded `Scheme.Modules` is only its scheme specialization. Small-site
   sheafification supplies the abelian structure, without another hypothesis.
4. Its unbounded derived category: `DerivedCategory (SheafOfModules ...)` and
   `[HasDerivedCategory.{w₁} (SheafOfModules ...)]`. I read DerivedCategory.Basic:
   this is localization of integer-indexed cochain complexes at quasi-isomorphisms.
   HasDerivedCategory specifies a localization in the chosen morphism universe,
   exactly the size convention in def-weil-abstract-derived-category; it imposes
   no cohomological condition on O or the site.
5. Global sections as Hom from O: the new definition uses
   `preadditiveCoyoneda.obj (op (SheafOfModules.unit ...))`. I read `unit`,
   `unitHomEquiv`, and `unitHomEquiv_comp_apply`: unit is O as a rank-one module,
   and evaluating a module map on 1 gives a compatible global family of sections.
   Addition is pointwise in this identification. Thus the target is the required
   additive group of sections even without a terminal object of C.
6. H⁰(C,K) computed using a K-injective representative, independently of choices:
   `ringedSiteZerothHypercohomology J R` composes the sections functor's
   `rightDerivedFunctor` with `DerivedCategory.homologyFunctor AddCommGrpCat 0`.
   Its local Grothendieck instance is obtained from the recorded
   `grothendieckAbelian_and_functorial_kInjective_resolutions J R`. The existing
   upstream `hasKInjectiveResolutions_of_isGrothendieckAbelian` then supplies the
   right-derived-functor requirement. I read `rightDerivedFunctorObjQIso` and
   `homologyFunctorFactors`: on any K-injective complex I this composite gives
   H⁰ of sections of I. Functoriality on the localization supplies independence
   of representatives. The only local instance choices are inside a definition
   body, not hidden hypotheses or file-local instances.
7. Arbitrary L and M in D(O): `P : D(O)ᵒᵖ × D(O)` represents L by `P.1.unop`
   and M by `P.2`. There is no boundedness restriction.
8. Derived internal Hom: `(derivedInternalHom J R).obj P`. I read its landed
   definition, `derivedInternalHom_comparison` and `derivedInternalHom_obj_iso`:
   it localizes the sheaf Hom complex with functorial K-injective replacement
   in the second variable, precisely def-pur-derived-internal-hom.
9. The canonical group identification:
   `e P : (ringedSiteZerothHypercohomology J R).obj
     ((derivedInternalHom J R).obj P) ≃+ (P.1.unop ⟶ P.2)`.
   This states an isomorphism of additive groups, not merely equal cardinalities
   or a map. An additive equivalence accommodates the independent morphism
   universe w₁ of the chosen localization.
10. Canonicity/naturality: one family e is quantified before every P, P', f and x;
    the equation is `e P' (H⁰.map (RHom.map f) x) = f.1.unop ≫ e P x ≫ f.2`.
    Here f.1.unop goes from L' to L and f.2 from M to M', so all composition
    directions and quantifier dependencies are correct. This is the naturality
    asserted by the node's final proof step. The statement docstring specifies
    the canonical localization construction and all three proof steps.

Edge cases: empty C is permitted, with compatible sections the trivial group and
Mod(O) the zero category. A zero ring sheaf, L = 0 or M = 0 likewise gives trivial
additive groups on both sides. Empty schemes are included through their small sites;
no scheme assumption is imposed. Degree zero is explicitly the integer 0, and negative
cochain degrees are retained. There is no n > 0 or characteristic restriction.
The universe u₁ can be enlarged to contain objects, arrows, ring sections and modules;
SmallCategory does not impose a mathematical cardinality bound on a small site.
The independent w₁ handles derived morphism sizes, and no test-object quantifier
becomes vacuous. All universes and variables are explicitly bound.

Independent searches (msearch.py, H1 and this item): LeanFinder query
`hypercohomology degree zero internal hom sheaves derived morphisms` returned ordinary
Sheaf.H/cohomologyPresheaf and generic HomComplex cocycle/cohomology declarations,
not this theorem or a ringed-site hypercohomology functor. Loogle query
`SheafOfModules.unit` returned unit, unitHomEquiv and its naturality, which I opened;
these are reused. Mathlib grep query
`hypercohomology|derivedGlobalSections|rhom_global_sections` found no exact match.
I also ran rg with those terms and `global.*internal.?hom|internal.?hom.*global`
over Mathlib homology/sites, source WeilConjectures and project lean/Sheaf. The source
Modules.HomObjSections result concerns underived modules on schemes; the source étale
derivedGlobalSections constructions are special-site versions. Neither gives the
arbitrary ringed-site theorem. DAG search `zeroth hypercohomology` found no existing
node. I separately opened def-pc-global-derived-rhom (schemes),
def-kun-rgamma-unbounded (étale sheaves), and def-sc-ringed-space-module-cohomology
(ordinary module sheaves on ringed spaces): none carries this notion in its generality.
The worker's LeanSearch service failure remains recorded; no match was assumed from it.

New-node audit: def-pur-ringed-site-zeroth-hypercohomology has a self-contained
statement and exactly its four cited dependencies, all read above. Section 07A5
constructs RΓ by K-injectives and defines its cohomology; forgetting scalar action
to abelian groups agrees with the item's explicit Hom_O(O,-) convention. The module
constructs this data by existing functors, with no sorry or hollow object. The node's
kind/status, empty proof fields, null mathlib_match, search records, created record,
ancestor/via, chapter/unit, lean_audit and lean record follow §5. No dependency module
or statement correction is needed. I corrected its source-place title from
`Section 07A5 (Derived categories)` to `Section 07A5 (Cohomology of unbounded complexes;
sites-cohomology-section-unbounded)`. The tag and mathematical content were already right.

No H3 mismatch or Lean change was needed. Both modules' docstrings name their source
and blueprint node, and the theorem docstring carries the node's K-flat/K-injective,
Hom-complex H⁰, and localization/naturality proof steps. The sole theorem is sorry;
the definition has complete data. There is no private copy, file-local notation,
file-local instance, unbound variable, or additional proved statement. Recorded
lean.statement signatures are unchanged. Both delivered modules compiled together
with scompile.py in dependency order, exit 0, without warnings (17 seconds).
