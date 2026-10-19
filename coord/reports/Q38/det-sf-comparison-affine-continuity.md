## Worker report

Item: `det-sf-comparison-affine-continuity`. Module:
`Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity`. Main declaration:
`AlgebraicGeometry.ProEtale.proEtaleAffineContinuity`.

The node is unchanged outside `lean`. This uses the current reviewed NU split, not the
superseded finite-coefficient attempt mentioned in the dispatcher history. There were no
Lean files or node copies in the assigned sandbox when this worker started. No statement
correction, new node, or dependency replacement was necessary.

The module defines the strict section-complex diagram and its two canonical cocones, then
states the theorem with `sorry`. All helper definitions have actual data, and their law
fields are checked directly. The named additive evaluation instance is a structure whose
map-addition field is reflexivity. The only postponed theorem is the item's own theorem;
its docstring gives all six steps of the current DAG proof.

### Hypotheses and objects

| Node text | Lean |
| --- | --- |
| Any scheme X | `(X : Scheme.{u})`; no quasi-compactness, separatedness, or affineness condition on X. |
| Any unital ring Λ; left modules | `(Λ : Type (u + 1)) [Ring Λ]`, using `ModuleCat.{u + 1} Λ`. There is no `Finite Λ` or `CommRing Λ`. |
| K in bounded-below derived etale module sheaves | `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. |
| Small nonempty cofiltered presentation index | `{I : Type u} [SmallCategory I] [IsCofiltered I]`; the last class includes nonemptiness. The colimit diagram is indexed by `Iᵒᵖ`. |
| Each U_i is etale over X | `D : I ⥤ X.Etale`; its structure maps and compatibility over X are the site's existing objects and morphisms. |
| Each U_i is an affine scheme, not merely affine over X | `[∀ i : I, IsAffine (D.obj i).left]`. |
| Affine transition morphisms | `[∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]`. |
| U and the projections are pro-etale site objects and arrows | `c : Cone (D ⋙ Scheme.toProEt X)`; U is `c.pt.left`, its map to X is `c.pt.hom`, and its projections are `(c.π.app i).left`. |
| U is the indicated inverse limit over X | `hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c)`. This forgets to the actual scheme diagram. For a nonempty cofiltered diagram, the underlying limit and its compatible structure map to X are equivalently the limit in schemes over X. |
| Any bounded-below injective representative mentioned in the node's last paragraph | `L`, `a : ℤ`, `[L.IsStrictlyGE a]`, `[∀ n : ℤ, Injective (L.X n)]`, and `e : DerivedCategory.Q.obj L ≅ K.obj`. These quantify over every such representative, rather than adding an assumption about K: every K in D-plus admits one by the recorded injective-representative theorem. The bound can be any integer. |

The fixed-coefficient category `Sheaf J (ModuleCat Λ)` is the existing encoding used by
`Scheme.proEtaleSiteComparisonModules` in the recorded comparison module. It is the category
of sheaves of left modules over the sheafification of the constant ring presheaf: the
constant Λ-action extends uniquely to the locally constant scalar sheaf, by sheaf gluing;
restriction along constant sections recovers it. This observation includes noncommutative
rings and empty objects. No new category or private sheaf definition is introduced.
Although that recorded convenience adjunction has a finite-ring binder, its publicly
imported `ProEtale.comparisonUpperStar` and `comparisonAdjunction` already work for every
Grothendieck abelian coefficient category. Specializing those existing declarations to
`ModuleCat Λ` retains the precise canonical inverse image for arbitrary rings. A repair of
the dependency is therefore unnecessary.

### Conclusions and canonical maps

`affineContinuitySectionComplex L` applies `sheafToPresheaf`, the existing functor on
complexes, and `HomologicalComplex.asFunctor`. `affineContinuityDiagram D L` restricts it
along `D.op`. Its objects are literally the complexes `L(U_i)` and its arrows are literally
the sheaf restrictions in every degree. `colimit` in the category of cochain complexes is
the degreewise colimit. Exactness of filtered module colimits makes this the node's
filtered derived colimit as well: it preserves objectwise quasi-isomorphisms, and its
cohomology is the filtered colimit of cohomology. These are properties of the specified
existing colimit, not additional choices or hypotheses in the theorem.

The first conjunct is `IsIso (affineContinuityEtaleMap D c K.obj L e)`. Its source is the
localization of the degreewise colimit of the strict section diagram. Its target is
right-derived evaluation at the terminal etale object of U of the exact inverse image
of K along `c.pt.hom`: precisely `RΓ(U_et, K_U)`. The cocone is built from the ordinary
etale inverse-image adjunction unit and the pullback of each projection. The induced map
uses `colimit.desc`, followed by the right-derived evaluation unit and the exact-functor
factorization identifying the representative with the inverse image of K.

The second conjunct is `IsIso (affineContinuityProEtaleMap D c K.obj L e)`. It has the same
strict-colimit source. Its target is right-derived evaluation at `c.pt` of the existing
comparison inverse image of K. Evaluation at an object is sections at the terminal object
of the localized site, so this is exactly
`RΓ(U_proet, (ν_X^* K)|_U)`. Its cocone legs are the actual comparison adjunction unit
followed by restriction along `c.π`, and it uses the same derived evaluation unit and the
same representative e. Thus it is the composite of the two displayed canonical maps.
Together the two conjuncts say exactly that both displayed arrows are invertible: the
second arrow is uniquely specified by its composite with the first, namely
`affineContinuityProEtaleMap`. There is no existentially supplied comparison arrow.

The final universal conjunct states that, for each i, the actual canonical map from
`Q(L(U_i))` to `RΓ((U_i)_et, K_i)` is an isomorphism. The map is
`Q.map (affineContinuityStageRestriction (D.obj i) L)` followed by
`affineContinuityTargetComparison` for `(D.obj i).hom`. The restriction uses the inverse-image
unit evaluated on U_i and restriction along the diagonal into `U_i ×_X U_i`. This explicitly
renders the node's clause that each stage complex computes its derived sections. Since
all these maps use the same L and its restrictions, this is the stipulated strict diagram,
not unrelated derived representatives at the stages.

All three conclusions live in the derived category of left Λ-modules. Isomorphisms there
induce isomorphisms under `DerivedCategory.homologyFunctor` for every `n : ℤ`. Applying
this to the two common-source arrows, with the canonical filtered-colimit/cohomology
identification, gives exactly the two displayed H^n arrows. Conversely the all-integer
cohomology isomorphisms imply invertibility of these derived maps. Thus the use of derived
`IsIso` retains every integer degree and states the node's equivalent derived formulation.

### Dependency interfaces read and used

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and its morphisms.
- `sk-def-pe-morphisms`: `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`,
  `AlgebraicGeometry.proAffineEtale`. Its small cofiltered absolutely affine etale
  presentation is supplied explicitly by D, c, hc and the affine instances.
- `sk-def-pe-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`,
  `ProEt.forget`; these are the recorded weakly-etale site, with its fpqc topology.
- `def-weil-pbc-category-colimit`: Mathlib `CategoryTheory.Limits.colimit`,
  `colimit.desc`, `Cone`, `IsLimit`, `Cocone`, `IsCofiltered`/`IsFiltered`.
- `def-weil-abstract-derived-category`: Mathlib `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q`. The general helper interfaces bind the available localization
  and K-injective-resolution instances explicitly; the theorem itself obtains them from
  the existing Grothendieck sheaf-category instances.
- `def-weil-pbc-bounded-derived-subcategories`: Mathlib `DerivedCategory.Plus`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, the recorded ringed-site notion. The fixed-coefficient
  sheaf encoding is the same one already used by the recorded comparison declaration,
  as explained above; it is not a new copy of the module category.
- `def-weil-pbc-constant-sheaf`: Mathlib `CategoryTheory.constantSheaf`, the sheafification
  of the constant presheaf; this fixes the coefficient convention underlying that encoding.
- `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `Scheme.proEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`, and their publicly imported unrestricted
  `ProEtale.comparisonUpperStar`, `comparisonAdjunction` and exactness instances.
- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms` and
  Mathlib's sheaf categories. Its right-derived-evaluation cohomology convention is
  rendered by `Functor.rightDerivedFunctor` on `sheafSections`.
- `def-weil-size-convention`: explicit `universe u`, schemes and the small presentation
  in u, site objects and coefficient modules in u+1; derived localizations and filtered
  colimits in that common larger bound. This is the recorded metatheoretic convention.
- `def-sp-injective-resolutions`: Mathlib `CategoryTheory.Injective` (extension along
  every mono) and the injective-resolution convention. Its bounded-below complex form
  is L with termwise injectivity and the representation isomorphism e.

The stated proof-dependency modules are imported without `public`, including unrestricted
abelian comparison, sections comparison, derived etale continuity, module/abelian evaluation,
localization, restriction exactness and exact filtered colimits. The proof dependency
`det-pe-classical-definition-continuity-map` has no Lean record and is not imported; the
primary theorem already supplies its geometric presentation data explicitly. No wait on
this proof dependency or downstream theorem is needed to state this item.

### Edge cases

An empty index category is excluded by the source and by `IsCofiltered`; a singleton
presentation and identity projections are included without a special case. Empty schemes,
empty affine stages, the zero ring and zero complexes are included. The bound a can be
negative and the derived-category assertion includes all negative as well as nonnegative
cohomological degrees. No torsion, finite, commutative, characteristic, qcqs-base or
separated-base hypothesis appears. General cofiltered categories, rather than just
preorders, are retained. There is no arbitrary cofinal replacement of the supplied index.
The u/u+1 site object/morphism distinction is retained; no equality of those universes is
imposed. No statement dispute or mathematical node fault was found.

### Searches

- `msearch.py leanfinder`: “Continuity of bounded below derived etale cohomology for affine
  inverse limits and comparison with pro-etale cohomology with arbitrary ring coefficients”.
  Eight hits, including `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` and affine
  structure-sheaf continuity, but no matching theorem for derived etale/pro-etale sections.
- `msearch.py loogle`: `AlgebraicGeometry.Scheme.toProEt, CategoryTheory.SheafOfModules,
  CategoryTheory.constantSheaf`. Zero hits; the service does not know the project inclusion.
- `msearch.py leansearch`: “canonical isomorphism between cohomology of a filtered colimit
  of section complexes on the etale site and proetale cohomology of inverse image”. Eight
  hits, including `CategoryTheory.Limits.colimitLimitIso` and condensed Kan-extension
  continuity; none states the present arbitrary-scheme, arbitrary-ring theorem.
- `msearch.py grep`: `comparisonUpperStar|cohomology.*[Ll]imit|[Pp]roetale.*[Cc]ohomology`
  in Mathlib AlgebraicGeometry. Zero matching declarations of the item.
- `rg` on the upstream WeilConjectures tree and `lean/Sheaf` found the general comparison
  functors, `DerivedEtaleCohomologyLimit`, `AbelianEtaleProEtaleCohomologyComparison`,
  `ProEtaleComparisonPullbackSections` and specialized continuity material. Their complete
  signatures were checked: the upstream general comparison works for ModuleCat of an
  arbitrary ring, while the recorded derived continuity theorem is for abelian sheaves.
  None states this whole two-arrow, strict-section-diagram theorem.
- `rg` for the item id in upstream WeilConjectures found no declaration.
- `rg` for the new helper and theorem names in `dag/lean_names_upstream.json`, upstream
  WeilConjectures and `lean/Sheaf` found no existing names before delivery.
- `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` confirmed the current
  published declaration, including the finite convenience wrapper and the unrestricted
  publicly imported API. The blueprint main-20261015 statement and the current node's
  complete proof and reviewed split were read directly.

Validation: the module passed `scompile.py Q38 det-sf-comparison-affine-continuity` with no
errors or warnings; the sandbox and module checks took 3.6 and 4.1 seconds respectively,
within the required per-file 60-second limit. The required delivery dry run is the next
check. No push or independent second-reading claim is made by this worker.

## Second reading by Q38

I independently read the current node and its complete six-step proof, the main-20261015
blueprint statement, Stacks `etale-cohomology.tex` lines 7463–7480 (03Q6),
7851–7879 (0GIT), and `proetale.tex` lines 3985–4012 (099W). Tag 03Q6 is an affine
base-change special case; it does not impose a qcqs assumption on the arbitrary base X
in this node. The broader continuity input 0GIT and comparison 099W supply the precise
hypotheses. I also read the stage-2 brief, delivery errors H1–H13, framework note, and
statement-dependency records and their source declarations. No repair note exists for
this item. There are no new nodes, dependency modules, or statement corrections.

My object/hypothesis/conclusion checklist follows. Each row passes.

| Node object, hypothesis, or clause | Exact Lean rendering and verdict |
| --- | --- |
| Arbitrary scheme X | `(X : Scheme.{u})`, the recorded Mathlib Scheme; no base finiteness, affineness or separation hypothesis. |
| Arbitrary unital ring and left modules | `(Λ : Type (u + 1)) [Ring Λ]`, `ModuleCat.{u + 1} Λ`; noncommutative rings are included. |
| Constant-ring-sheaf coefficients | Existing `Sheaf J (ModuleCat Λ)` convention of `proEtaleSiteComparisonModules`; a sheafwise Λ action extends uniquely over locally constant scalars by gluing. It is equivalent to the recorded `ringedSiteModules`/`SheafOfModules` notion, including empty objects. |
| K is bounded below | `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat Λ))`; Mathlib Plus is the full subcategory with cohomology zero sufficiently far below. |
| Small nonempty cofiltered I | `{I : Type u} [SmallCategory I] [IsCofiltered I]`; I read the class's `nonempty` field in Mathlib Filtered/Basic. This is a general category, not just a preorder. |
| Absolutely affine etale stages over X | `D : I ⥤ X.Etale` and `[∀ i, IsAffine (D.obj i).left]`. This is exactly the absolute-affine presentation in the recorded `proAffineEtale`, not merely an affine structure morphism. |
| Affine transitions over X | `[∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]`; the site's arrows supply the over-X compatibility. |
| U and projections | `c : Cone (D ⋙ Scheme.toProEt X)`; U is `c.pt.left`, u is `c.pt.hom`, and the projections are `(c.π.app i).left`. Mathlib ProEt uses weakly etale objects with all over-X arrows. |
| Inverse-limit universal property | `hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c)`; for this nonempty connected category the underlying scheme limit is equivalently the over-X limit. No auxiliary limit choice is substituted. |
| Any bounded-below injective representative | `L`, `(a : ℤ)`, `[L.IsStrictlyGE a]`, `[∀ n : ℤ, Injective (L.X n)]`, and `(e : DerivedCategory.Q.obj L ≅ K.obj)`; these quantify universally over the representatives specified by the node. Mathlib's `DerivedCategory.Plus.exists_injective_nonempty_iso` supplies one, so this does not add a restriction on K. |
| Strict stage diagram and its arrows | `affineContinuityDiagram D L` is D.op followed by Mathlib `mapHomologicalComplex`/`asFunctor` on `sheafToPresheaf`; its maps are literally the sheaf restrictions, with one common bound a. |
| Each stage computes its derived sections | The final `∀ i : I, IsIso (...)` uses `affineContinuityStageRestriction (D.obj i) L`, then `affineContinuityTargetComparison` for `(D.obj i).hom`. The restriction is the inverse-image unit followed by the diagonal into the pullback. This clause is expressly present in the node's final paragraph. I initially questioned this conjunct, rechecked that paragraph, and retained it without change. |
| Filtered derived colimit | Both arrows have source Q of `colimit (affineContinuityDiagram D L)`. Complex colimits are degreewise. Exact filtered module colimits commute with cohomology and preserve objectwise quasi-isomorphisms, so this is exactly the specified left-derived colimit; it is bounded below. |
| First displayed arrow | `IsIso (affineContinuityEtaleMap D c K.obj L e)`: `colimit.desc` of the etale pullback-unit/restriction cocone, followed by the right-derived evaluation unit. Its target is RΓ(U_et,u* K). |
| Second displayed arrow and composite | `IsIso (affineContinuityProEtaleMap D c K.obj L e)` asserts invertibility of the canonical composite to pro-etale derived evaluation at c.pt. Its cocone uses the actual comparison adjunction unit and restrictions along c.π. Naturality of these units and the over-X projection equations identify it with the first arrow followed by the etale/pro-etale comparison. Since the first is invertible, asserting invertibility of the composite is equivalent to asserting invertibility of that second displayed arrow. There is no arbitrary map parameter or existential replacement. |
| Pro-etale target on U | Right-derived evaluation at c.pt computes sections on the localized site. The recorded weakly-etale localization identifies it with U_proet, and hence with RΓ(U_proet,(ν_X* K)|U). The comparison functor is the existing unrestricted `comparisonUpperStar`, not the finite-ring convenience wrapper. |
| Every integer degree | Isomorphisms in the derived category induce the two cohomology isomorphisms for every n : ℤ. Exact filtered colimits identify the source with colim H^n of the stage complexes. Thus zero and negative degrees are included; there is no replacement by only natural degrees. |

I opened the recorded comparison module and upstream Comparison/Defs: its general
`comparisonUpperStar` and `comparisonAdjunction` take Grothendieck abelian coefficients,
without a finite-ring assumption. Its public imports provide the exact functor used here.
I checked Mathlib `ProEt`, `ProEt.forget`, `IsCofiltered`, `DerivedCategory.Plus`,
`Injective`, `InjectiveResolution`, `sheafSections`, and the recorded ringed-site category.
The derived-continuity proof dependency has arbitrary abelian coefficients and exactly
small cofiltered, qcqs-stage, affine-transition hypotheses; absolute affine stages supply
qcqs here. The proof-dependency imports remain available for the later proof.

Edge cases checked: the empty index is excluded by both source and IsCofiltered;
singletons and identity projections are included. Empty X, U and affine stages, the zero
ring, zero complexes, and arbitrary characteristic are included. The bound a may be any
integer. No torsion, finite ring, commutativity, or Noetherian condition was added.
I remains in u; sites have objects in u+1 and morphisms in u; modules are in u+1.
All names and universe variables are bound, with `autoImplicit false`. The general
right-derived helpers bind their sheafification/localization/resolution instances, while
the theorem gets those from the existing site and Grothendieck-category instances.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: `derived sections continuity for cofiltered affine etale presentations and
  arbitrary left module coefficients`: eight affine approximation/section hits; none
  states this theorem.
- Loogle: `"proetale", "cohomology"`: zero hits.
- Grep: `rightDerivedFunctor.*[Cc]olimit|[Cc]ontinuity|[Pp]ro[Ee]tale` in Mathlib
  AlgebraicGeometry/Sites: Proetale and ElladicCohomology definitions, no such statement.
- I additionally searched upstream WeilConjectures and the project's lean/Sheaf with rg
  for continuity, derived sections, comparison, and section-complex names. I opened
  `BoundedBelowProEtaleComparison`: `affineBoundedBelowComparison` asserts the pro-etale
  composite and its homology colimit for a second resolved complex J. It does not assert
  the intermediate etale comparison or stage-computation clause, so is not an exact
  existing match for this item.

One actual H4 repair: the worker's `affineContinuitySectionComplex` duplicated
`comparisonSectionComplexes` already in that downstream unit module. Importing the unit
would reverse the dependency and create a cycle. I removed the wrapper and use Mathlib's
`sheafToPresheaf`, `mapHomologicalComplex` and `HomologicalComplex.asFunctor` directly at
its former call sites. These are definitionally the same expressions; the theorem
signature is unchanged. I removed the deleted helper from `lean.declarations`, retained
the worker report above as history, and wrapped the resulting expressions to 100 columns.
The other helpers construct the item's canonical diagram and maps from actual data;
none has a sorry field, arbitrary comparison choice, or theorem proof. The only sorry
is `proEtaleAffineContinuity`, whose docstring follows all six node proof steps.

Validation: scompile.py compiled the entire delivered module independently in sandbox
and library contexts, with no errors or warnings (4.0 s and 4.2 s). I checked that
`lean.statement` equals the declaration signature verbatim. No natural-language statement,
statement dependency, proof dependency, target, or unit statement changed.
