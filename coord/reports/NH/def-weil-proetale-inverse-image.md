## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` gives the actual inverse- and
direct-image constructions of `def-weil-proetale-inverse-image`. Its definitions have real
data, with no `sorry`, axioms, theorem placeholders, additional geometric assumptions, or
statement correction. The node copy changes only `lean`.

The primary declaration is `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`; all helpers
are recorded in `lean.declarations`. They belong to the construction of this node, rather
than introducing independent notions. All definitions use the existing Mathlib and upstream
constructions, not copies of their implementations.

Clause-by-clause correspondence (names below are in `AlgebraicGeometry.Scheme`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary schemes and scheme morphism, without a weakly etale/flat hypothesis on f | `{X Y : Scheme.{u}} (f : X ⟶ Y)` throughout |
| Small pro-etale objects, morphisms and topology | `X.ProEt`, `Y.ProEt`, `ProEt.topology X`, `ProEt.topology Y`, exactly the site underlying the recorded `proEtaleDerivedCategory` |
| Compatible universes and small indexing categories | Explicit `universe u v`; schemes and coefficient rings in u, coefficient values in u+1. Comma categories have objects in u+1 and Homs in u, hence are essentially u+1-small. The upstream Kan-extension instance constructs their colimits without imposing `Small.{u} X.ProEt`. |
| Base-change functor and its maps on arrows | `proEtaleBaseChange f` is the existing `MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`; its chosen product is `V ×[Y] X` with second projection. This is the same chosen fibre-product universal property as `X ×[Y] V`, with the two projections interchanged. Arrows are the induced pullback maps with identity on X. |
| Weakly etale and fpqc base change; covering preservation | The existing pullback functor uses the weakly etale base-change instance; `proEtaleBaseChangeCoverPreserving` reuses `ProEt.coverPreserving_overPullback`. The latter applies `Precoverage.mem_coverings_of_isPullback` to `proetalePrecoverage`. |
| Final object and fibre products preserved; morphism of sites | `proEtaleBaseChange_preservesFiniteLimits` and `proEtaleBaseChange_isContinuous`, both existing upstream/Mathlib evidence specialized to this base change. These are the finite-limit-preserving continuous functor of Tag 00X6. |
| Direct image on sections and restrictions | `proEtaleSheafDirectImage f D` is an abbreviation for the existing `AlgebraicGeometry.ProEtale.lowerStar D f`, itself `u_f.sheafPushforwardContinuous D`; its underlying presheaf is precomposition with `u_f.op`. |
| Category I_U with its specified arrows | `proEtaleInverseImageIndex f U := StructuredArrow U (proEtaleBaseChange f)`; a morphism has `a : V ⟶ V'` and exactly `φ ≫ u_f.map a = φ'`. |
| Presheaf inverse image, opposite index, restriction maps | `proEtaleSheafInverseImage` unfolds to `sheafToPresheaf ⋙ u_f.op.lan ⋙ presheafToSheaf`. Mathlib's pointwise Kan-extension diagram is `CostructuredArrow u_f.op (op U)`, canonically I_U opposite. Its evaluation is the colimit of F(V). The Kan-extension functor restricts a coprojection indexed by φ along b to the one indexed by b ≫ φ. |
| Sheafification and induced maps on sheaves | The last functor is the recorded `presheafToSheaf`; the maps are the inherited functor maps throughout the composite. |
| Set and abelian adjunctions, with unit and counit | `proEtaleSheafAdjunction f D`, at `D = Type (u+1)` and `D = AddCommGrpCat.{u+1}`; its `.unit` and `.counit` are η_f and ε_f. Its abelian specialization uses the identical constructed expression as upstream `ProEtale.upperStar` and its adjunction. |
| Ring colimits and sheafification, also without commutativity | The same two definitions and adjunction specialize to `RingCat.{u+1}` and `CommRingCat.{u+1}`. The Kan extension and sheafification take place in those value categories. Consequently their objects carry actual ring operations and all ring identities, including both distributivities in RingCat. No arbitrary ring structure is chosen. |
| Ring morphisms and restricted adjunction | The ring-valued `proEtaleSheafAdjunction` uses ring homomorphisms and its own unit/counit. This is the ring-colimit version explicitly allowed by the node, equivalent to lifting the finite-product-preserving set inverse image. |
| Constant coefficient sheaves A_Y, A_X | `proEtaleConstantRing X A` is `constantSheaf (ProEt.topology X) CommRingCat` at `CommRingCat.of (ULift A)`. Forgetting commutativity gives exactly the ring sheaf used by the recorded `proEtaleDerivedCategory`, not a separate constant-sheaf presentation. |
| ρ_A^f, unique extension of a ↦ the constant section a | `proEtaleConstantDirectImageMap` transposes `whiskerLeft u_f.op (toSheafify J_X (const A))` under `sheafificationAdjunction J_Y`; `proEtaleCoefficientDirectImageMap` specializes it to the coefficient ring. Thus it uses the sheafification unit on each constant section, with the stipulated normalization and universal uniqueness. |
| c_A^f and the precise counit formula | `proEtaleConstantInverseImageMap` is literally `L.map ρ ≫ adj.counit.app _`; `proEtaleCoefficientInverseImageMap` specializes it to A. |
| Inverse image of a module over f inverse A_Y, with transported action | `proEtaleModuleInverseImage f R` is module pullback along the actual ring adjunction unit `R ⟶ f_* f⁻¹ R`, using `SheafOfModules.pullback`, transported to and from a small equivalent model. Its target ring is the actual ring inverse image, after forgetting commutativity. This standard module inverse image has the transported action: on local colimit representatives the ring and module representatives are put over a common index and multiplied there; finite-limit preservation makes the index filtered. The corresponding universal property is precisely module pullback along the adjunction unit. |
| Module pullback tensor f inverse F over f inverse A_Y with A_X | `proEtaleConstantModulePullback f A M` is exactly the recorded `SheafOfModules.changeOfRings (proEtaleCoefficientInverseImageMap f A)` applied to `proEtaleModuleInverseImage` of M. That dependency sheafifies the sectionwise scalar-extension tensor. |
| Direct-image A_Y action through ρ on sections | `proEtaleConstantModuleDirectImage` is `SheafOfModules.pushforward` along u_f and the actual map ρ after forgetting commutativity. Its underlying abelian sheaf is precomposition and its action is restriction of scalars through ρ_V, as specified. |
| Induced linear maps in both constructions | Inverse image and direct image use their functor `.map`; `proEtaleConstantModulePullbackMap` applies the recorded `changeOfRingsHom` to the inverse-image map. |

The only API transport is internal to the module inverse-image construction. The original
site remains `Type (u+1)` with `Category.{u}`. `proEtaleSiteModel X = AsSmall.{u+1} X.ProEt`
keeps all objects and lifts the Homs; `proEtaleModelTopology` is the induced topology under
the canonical equivalence. `proEtaleModelBaseChange` is down, original base change, up.
Its continuity is composition of the existing continuous functors. `proEtaleModuleToModel`
and `proEtaleModuleFromModel` are precomposition under these equivalences with identity ring
maps. `proEtaleModelRingUnit` is the original ring adjunction unit, whiskered and with
commutativity forgotten. The middle `SheafOfModules.pullback` now has exactly Mathlib's
small-category universe shape. The output is transported back to the original site and
original ring inverse image. Thus this supplies the canonical transport required by the
brief without equating the original object and morphism universes, changing coefficient
modules to module objects, or assuming a new adjunction. Mathlib's chosen adjoint is
specified by its adjunction and hence unique up to its canonical isomorphism; it is not
chosen from a bare `Nonempty` assertion.

Dependency declarations read and used:

| Dependency | Declaration and module |
| --- | --- |
| `def-weil-scheme-morphism-properties` | Convention record: scheme objects and category morphisms; no independent declaration required. Only the existing `WeaklyEtale` property is used here. |
| `def-weil-pbc-proetale-site` | `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`; its actual underlying `ProEt.topology` and forgotten constant CommRingCat ring presentation are retained. |
| `def-weil-size-convention` | Metatheoretic convention record, implemented by explicit universes, essentially small comma categories, and canonical small-model transport. |
| `def-pc-fibre-product` | `CategoryTheory.Limits.pullback` and projections, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, used by the existing base-change functor. |
| `lem-weil-pbc-weakly-etale-composition-base-change` | `MorphismProperty.comp_mem`, `MorphismProperty.pullback_fst`, in Mathlib MorphismProperty Composition/Limits, with `WeaklyEtale` instances. |
| `lem-galois-fpqc-covering-base-change` | `Precoverage.mem_coverings_of_isPullback`, `Mathlib.CategoryTheory.Sites.Precoverage`, applied by the reused upstream cover-preservation result. |
| `lem-weil-pbc-left-exact-site-inverse-image-tensor` | `CategoryTheory.siteInverseImage_tensor`, `Sheaf.CategoryTheory.SiteInverseImageTensor`, imported for the source's general site theorem. The specialized base-change finite-limit/continuity evidence is reused directly from upstream. |
| `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction` | Mathlib match `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, `Mathlib.CategoryTheory.Sites.Pullback`, used verbatim. |
| `def-weil-pbc-sheafification` | `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`, `Mathlib.CategoryTheory.Sites.Sheafification`. |
| `lem-weil-pbc-adjunction-lifts-group-ring-objects` | `CategoryTheory.Adjunction.liftsGroupRingObjects`, `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`, imported for the finite-product-lifting interpretation. The actual definition uses the equivalent ring-valued Kan extension explicitly authorized in the node. |
| `def-weil-pbc-constant-sheaf` | `constantSheaf`, `Mathlib.CategoryTheory.Sites.ConstantSheaf`. |
| `def-weil-sheaf-of-modules-category` | `CategoryTheory.ringedSiteModules`, `Sheaf.CategoryTheory.RingedSiteModules`; its transparent underlying Mathlib `SheafOfModules` category and actual linear maps are used throughout. |
| `def-pur-sheaf-tensor-product` | `SheafOfModules.changeOfRings`, `SheafOfModules.changeOfRingsHom`, `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`; source also read using `scompile.py --source` to verify current universes. |

The exact 51-module framework checkout and `coord/pefw-upstream-framework.md` were read.
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` supplies the
actual abelian Kan-extension construction and imports its canonical existence and
continuity evidence. The module-object upper/lower-star definitions were also inspected;
they concern internal modules over condensed coefficients and do not replace this node's
constant-ring `SheafOfModules` constructions.

Edge cases checked: f is arbitrary, including nonflat maps; X or Y may be empty; identity
maps use exactly the same Kan-extension/sheafification definition; the zero coefficient
ring is allowed; no nonempty-index assumption occurs; the terminal/empty covering cases
remain covered by continuity. There is no assumption `Small.{u} X.ProEt` or equality of
original site object and morphism universes. RingCat retains noncommutative rings. The
coefficient and module values have the same u+1 size as the recorded pro-etale derived
category. Compiler probes verified set, RingCat and CommRingCat specializations of the
inverse image and constant comparison; the probes were removed. All delivered definitions,
including transport and tensor maps, compile together on the server.

Searches (performed with msearch.py, and direct read-only rg of the prescribed checkouts):

- LeanFinder: `Inverse image and direct image of sheaves of sets rings and constant ring
  modules on small pro-etale sites along a scheme morphism`. Eight hits, primarily Zariski
  scheme module restriction functors and pseudofunctors; none states all clauses here.
- Loogle: `Functor.sheafPullback, SheafOfModules.pullback`. No hits, unknown identifier
  `Functor.sheafPullback` in that service. The actual declaration was read in Mathlib.
- Mathlib grep: `sheafPullback|sheafPushforwardContinuous|pullback` in
  `Algebra/Category/ModuleCat/Sheaf`. Twenty hits, including the genuine generic
  `SheafOfModules.pullback`/`pushforward` APIs, which this file reuses.
- LeanSearch: `Inverse image and direct image of sheaves of rings and modules on the small
  pro-etale site`. Service unavailable, Internal Server Error; no verdict inferred.
- Project rg: `def-weil-proetale-inverse-image` in upstream WeilConjectures: no hit.
  `proEtaleSheafInverseImage|proEtaleModuleInverseImage|proEtaleConstantModulePullback` in
  upstream WeilConjectures, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collisions.
- Broader source search found `ProEtale.lowerStar`, `ProEtale.upperStar` and their
  adjunction in the upstream finite-coefficient definitions. The direct image is already fully general and is reused by abbreviation; the inverse
  image and adjunction give the abelian part exactly but have Grothendieck abelian
  coefficient assumptions and do not define the set,
  ring, constant-ring comparison and tensor module constructions together. The general
  Mathlib construction is reused, rather than copying those abelian implementations.
- Existing `TopCat.Sheaf.inverseImageModule`/`inverseImageModuleFunctor` were inspected;
  they are for topological spaces and do not apply to the small pro-etale site.

No new nodes, dependency-record repairs, statement disputes or corrections are needed.
Validation: server-only `scompile.py`, nice 19, two threads, 60 seconds per file. No local
compiler, Lake build, or live-library write was used. The independent second reader supplies
its own reading; this report does not claim to be that reading.


## Second reading by NH

I independently opened the item node and the complete delivered module, the recorded
statement dependencies and their signatures, and the source passages. Stacks proetale.tex
section-morphism (09A5) starts with an arbitrary morphism of schemes. The subsequent
quasi-compact/quasi-separated hypothesis belongs to the comparison lemma, not to this
construction. Sites proposition-get-morphism (00X6) assumes continuity and preservation
of a final object and fibre products. Sites section-functoriality-PSh (00VC),
lemma-adjoints-u (00VE), lemma-adjoint-sheaves (00WX), example-constant-sheaf (0H7J),
and sites-modules lemma-pushforward-module/lemma-pullback-module (03D1/03D2) supply
the remaining constructions, without geometric finiteness hypotheses.

Here is my object/hypothesis/clause inventory and comparison. All declaration names
in the table are in AlgebraicGeometry.Scheme unless explicitly qualified.

| Node item | Lean rendering and verdict |
| --- | --- |
| Schemes X, Y and arbitrary f:X to Y | `{X Y : Scheme.{u}} (f : X ⟶ Y)`; exact, no property instance on f. |
| Small pro-etale sites with the specified size bound | `X.ProEt`, `Y.ProEt`, `ProEt.topology`; these are exactly the sites in the recorded `proEtaleDerivedCategory`. Objects have size u+1 and Homs size u. Exact. |
| Chosen base change V maps to X times_Y V, with induced arrows | `proEtaleBaseChange` abbreviates `MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`. I read its implementation: object is `pullback V.hom f` with second projection; arrow is the unique pullback lift of the variable arrow and identity on X. Swapping factors is the canonical projection-preserving isomorphism, not a different object. Exact. |
| Weakly etale stability, covering preservation | The base-change functor uses the existing weakly-etale base-change instance; `proEtaleBaseChangeCoverPreserving` reuses `ProEt.coverPreserving_overPullback`. Its source uses `Precoverage.mem_coverings_of_isPullback` on the actual pro-etale precoverage. Exact. |
| Final object and fibre products preserved, hence morphism of sites | `proEtaleBaseChange_preservesFiniteLimits` and `proEtaleBaseChange_isContinuous` reuse the existing finite-limit and continuity evidence. This is the continuous finite-limit-preserving site functor of 00X6; no extra flatness assumption. Exact. |
| Direct-image values, restrictions, maps | `proEtaleSheafDirectImage` reuses `ProEtale.lowerStar`, whose definition is `sheafPushforwardContinuous`: precomposition by base change opposite. Exact. |
| I_U objects and its morphism equation | `proEtaleInverseImageIndex := StructuredArrow U (proEtaleBaseChange f)` has object `(V, φ)` and arrow a with `φ ≫ u_f.map a = φ′`. Exact order. |
| Colimit over I_U opposite using F restrictions | `proEtaleSheafInverseImage` is the existing `sheafPullbackConstruction.sheafPullback`, namely inclusion, `u_f.op.lan`, sheafification. Its pointwise comma category is `CostructuredArrow u_f.op (op U)`, canonically I_U opposite. Exact. |
| Restriction along b sends the φ insertion to the φb insertion | The pointwise left Kan extension uses composition with b on the comma index; this is the stated restriction. It is not precomposition in the wrong direction. Exact. |
| All indexing categories small in the larger universe | `HasColimitsOfSize.{u+1,u+1}` and the imported pointwise Kan-extension instance cover the essentially u+1-small comma categories. No `Small.{u} X.ProEt` assumption. Exact. |
| Set and abelian sheaf adjunction, η and ε | `proEtaleSheafAdjunction`, specialized to `Type (u+1)` and `AddCommGrpCat.{u+1}`, is the prescribed composite Kan-extension/sheafification adjunction; `.unit` and `.counit` are the requested maps. Exact. |
| Ring inverse image, operations, identities and ring adjunction | The same definitions specialize to `RingCat.{u+1}` and `CommRingCat.{u+1}`. Colimits and sheafification occur in rings, the explicitly permitted version of the node. Actual ring-category objects retain every ring identity, including both distributive laws without commutativity. Direct image is sectionwise. Exact. |
| Commutative coefficient ring A and A_X, A_Y | `proEtaleConstantRing X A` is `constantSheaf` of `CommRingCat.of (ULift A)`. Forgetting commutativity gives definitionally the coefficient presentation in `proEtaleDerivedCategory`; no competing coefficient sheaf. Exact. |
| ρ_A extends the map sending a to the same constant section on base change | `proEtaleConstantDirectImageMap` uses the inverse sheafification Hom equivalence on the whiskered sheafification unit of the constant presheaf. `proEtaleCoefficientDirectImageMap` specializes it to A. This gives the unique extension with the specified normalization. Exact. |
| c_A is adjoint to ρ_A by the stated counit formula | `proEtaleConstantInverseImageMap` is literally `L.map ρ ≫ counit.app _`; `proEtaleCoefficientInverseImageMap` specializes it. Exact. |
| Underlying abelian inverse image with transported module action over f inverse A_Y | `proEtaleModuleInverseImage f R` transports to `AsSmall`, pulls back along the transported actual ring adjunction unit, and transports back. I read Mathlib `SheafOfModules.pullback`, its `pullbackIso` and the presheaf pullback existence construction. It is the canonical adjoint to restriction of scalars along that unit, not an arbitrary map or module structure. Since I_U opposite is filtered, its abelian colimit carries the action obtained by taking a common index for ring/module representatives; this has precisely that adjunction. Thus the construction is canonically the node's action inverse image. Exact. |
| Tensor extension along c_A | `proEtaleConstantModulePullback` applies the recorded `SheafOfModules.changeOfRings` to that module inverse image and the exact `proEtaleCoefficientInverseImageMap`. The dependency sheafifies sectionwise extension-of-scalars tensors. Exact. |
| Direct-image A_Y action through ρ on each V | `proEtaleConstantModuleDirectImage` uses `SheafOfModules.pushforward` along the same base change and ρ after forgetting commutativity. Its values and scalar action are exactly the stated precomposition and restriction of scalars. Exact. |
| Induced maps in every construction | Functor `.map` supplies sheaf/module inverse and direct image maps; `proEtaleConstantModulePullbackMap` uses the recorded `changeOfRingsHom` after the inverse-image map, hence the induced tensor map. Exact. |

The universe transport warrants a separate check. `proEtaleSiteModel X` is
`AsSmall.{u+1} X.ProEt`, retaining all objects and lifting Homs, with topology induced
by `AsSmall.down`. The model base change is down/base-change/up. The to/from-model
module transports are actual precompositions with identity ring maps. In
`proEtaleModelRingUnit`, whiskering the original commutative-ring adjunction unit
by down and forgetting commutativity gives exactly the ring map needed by the
model pullback. Down/up composites recover the original section functors. This
satisfies Mathlib's equal model object/Hom universe API without equating the
original universes or changing the bound on schemes. Its chosen adjoint is
characterized by an adjunction to the specified pushforward; no choice from a
mere existence proposition with undetermined data occurs.

Dependency reading: I checked the convention records for scheme properties and
size; the signatures of `proEtaleDerivedCategory`, `ringedSiteModules`,
`siteInverseImage_tensor`, `Adjunction.liftsGroupRingObjects`, the general Mathlib
sheaf adjunction, `constantSheaf`, `presheafToSheaf`, `toSheafify`, and
`sheafificationAdjunction`; the pullback functor implementation and the composition,
base-change and covering lemmas named by the node; and the existing tensor
`changeOfRings`/`changeOfRingsHom` implementations. The general site tensor theorem
has a smaller-site assumption, so it is imported as a proof dependency, not
misapplied to the original pro-etale category. The construction uses the applicable
upstream continuity/finite-limit evidence directly. There are no new nodes or
unpublished dependency modules in this delivery, and no statement correction or
citer audit is required.

Edge cases: empty schemes and empty covering families are allowed; no nonemptiness
of the indexing category is assumed by the definition (in this particular site it
has the terminal-base index). Identity and nonflat morphisms use the same
construction. Zero rings and zero modules are allowed; constant sections are not
assumed distinct. There is no characteristic restriction, nonzero-rank assumption,
or n parameter. Noncommutative rings are covered by RingCat, while the tensor
coefficient specialization correctly asks for commutativity. Universes are explicit
and every variable is bound; coefficients/modules use the recorded u+1 presentation.

Independent searches, using different queries from the worker:

- LeanFinder: `Proetale inverse image constant sheaf ring comparison module action pullback`:
  eight hits, generic module pullback/free-object and composition declarations. I read
  `SheafOfModules.pullback` and its construction; these are reused, not reimplemented.
- Loogle: `"constantSheaf", "sheafPushforwardContinuous"`: zero hits.
- LeanSearch: `Sheaf inverse image commutes with constant ring sheaves on a proetale site`:
  service unavailable (Internal Server Error); no mathematical verdict from that failure.
- msearch grep: `sheafPullbackConstruction|pullbackPushforwardAdjunction|constantSheaf`
  in Mathlib CategoryTheory/Sites: existing generic sheaf pullback, constant sheaf and
  adjunction APIs, reused here.
- Direct rg of Mathlib, source WeilConjectures, project lean/Sheaf and the upstream
  name table for inverse-module and constant-comparison terms found the topological
  space inverse-image API and existing generic/etale constructions, not this complete
  pro-etale construction. The declared new names have no collision.
- I opened the exact group-clone finite-coefficient upper/lower-star source and
  module-object upper/lower-star definitions, and read pefw-upstream-framework.md.
  The abelian inverse image and direct image are reused expressions; the condensed
  internal-module framework uses a different coefficient presentation and does not
  replace these constant-ring SheafOfModules constructions.

Mismatch found and repaired: several docstrings attributed the colimit inverse-image
construction to Tag 06UM, which is actually Sites section-pullback, "Pullback maps".
I changed those citations to Tags 00VC/00WX, adding 00VE in the module source list.
The node's source metadata already lists 09A5 and the natural statement is correct;
its auxiliary description of 06UM is a bibliographic issue, not a statement change.
No Lean term or signature needed repair. The main lean.statement remains verbatim
the primary abbreviation signature. No definition contains sorry; no theorem was
proved or added. The instances only reuse existing evidence. All declarations have
source/blueprint docstrings, and all lines remain within 100 characters.

Validation: the delivered module passed server-only scompile.py with nice 19, two
threads and the hard 60-second per-file limit, without warnings. A final server
compile and delivery preflight are run after the citation edit.
