## Worker report

The module `Sheaf.CategoryTheory.InjectiveTowerRoosShifts` states
`CategoryTheory.injectiveTowerRoosShifts`, with its sole theorem proof `sorry`.
Four real helper constructions package existing product and cone maps; none chooses
objects from an existence theorem or postpones definition data. The node's natural-language
statement, proof and proof dependencies are unchanged. Its statement dependencies gain
the already landed `def-weil-strict-roos-model` and the new definition node
`def-pur-tower-product-functor`. The returned dependency on
`lem-weil-product-comm-shift` is removed; that theorem's module is unchanged.

Hypotheses and objects, read against every clause of the node:

| Node | Lean |
| --- | --- |
| Site small in the module universe | `C : Type uC`, `Category.{vC} C`, `EssentiallySmall.{r} C`, `J : GrothendieckTopology C`. The site universes stay independent of r. |
| Commutative ring sheaf A | `R : Sheaf J RingCat.{r}` and `_hcomm` on every ring of sections. This is the recorded strict-tower dependency's interface to commutative ring sheaves. |
| Abelian module sheaves in that universe | `ringedSiteModules.{r,r} R`, the recorded abbreviation for `SheafOfModules.{r} R`; `HasSheafify` and `WEqualsLocallyBijective` expose the usual small-site sheafification infrastructure. |
| Strict positive-indexed towers, levelwise exactness | `ℕᵒᵖ ⥤ ringedSiteModules R`. Level n denotes n+1 in the paper, with transition `map (homOfLE (Nat.le_succ n)).op`. Mathlib's abelian functor-category instance gives the stated exact structure. |
| Unbounded cochains and chosen derived morphism universe | `CochainComplex ... ℤ`, `HasDerivedCategory.{w}` for modules and towers. No lower bound or original-transition condition occurs. |
| N represented by X, resolution X→I with K-injectivity and injective terms | The final universal block binds `X I`, `q : X ⟶ I`, `QuasiIso q`, `I.IsKInjective`, and `∀ i, Injective (I.X i)`. The computational assertion applies to every such I, hence to every chosen representative. `N` is `DerivedCategory.Q.obj X`; no extra restriction on N is imposed since Q is essentially surjective. |
| L means the total right derived limit computed termwise | The final block binds a right-derived pair `(RF,η)` for `roosLimitFunctor ⋙ Q`, with its computation on K-injectives. It produces `d : Q(lim I) ≅ RF(QX)` with `d.hom ≫ RF.map (Q.map q) = η.app I`, and the transported distinguished triangle on that actual first vertex. The termwise limit-of-complexes and termwise-complex-of-limits presentations are canonically isomorphic; the recorded dependency gives the latter. |

Conclusions and normalizations:

| Node clause | Lean rendering |
| --- | --- |
| All injective-term transitions split | `∀ i n, IsSplitEpi ((I.X i).map ... )`. This is concluded from injectivity, never assumed. |
| Every evaluated complex is K-injective | `∀ n, CochainComplex.IsKInjective (I.asFunctor.obj (op n))`. |
| Termwise product represents the derived product | `(roosP I).IsKInjective` and `Nonempty (IsLimit (Q.mapCone (limit.cone (Discrete.functor ...))))`. The latter retains precisely the localized actual product projections, rather than arbitrary arrows to isomorphic objects. |
| h=1-s with actual transitions | Existing `roosU I`, defined by `towerTransitionEndomorphism` on the actual evaluated transition maps. |
| C=Cone(h)[-1], coordinates and differential | Existing `roosF.obj I` and `roosχ I p`. The owning definition node specifies exactly degree p+1 as P^p⊕P^(p+1) and differential (-dy-hx,dx). No second cone model is defined. |
| η=(0,(z_n)) with actual limit components, and quasi-isomorphism | Existing `roosι I` is the map in the conclusion `QuasiIso (roosι I)`; its definition uses `Pi.lift (fun n ↦ limit.π ... (op n))`. Existing `roosι_χ` gives exactly its zero-first-coordinate formula. The isomorphism ε is required to have `ε.hom = Q.map (roosι I)`. |
| Normalized Roos triangle on the computed L | `Triangle.mk (projection I) (Q.map (roosU I)) (δ I) ∈ distTriang ...`. `projection` is literally Q of the product of limit-cone projections. The product fan above makes this a Roos triangle as defined by `IsDerivedLimitTriangle`, expressed using its specified product model rather than replacing that model by the chosen categorical product. The final d clause transports it to RF(QX). |
| Boundary is the localized actual rotated-cone boundary | `boundary I` is literally `(mappingCone.triangle (roosU I)).invRotate.mor₃`. The equality `δ I ≫ ε.hom⟦1⟧' = Q.map (boundary I) ≫ (Q.commShiftIso 1).hom.app ...` fixes δ uniquely on the specified representatives. |
| Canonical product and limit shift comparisons | The first two universal blocks specify `csP` and `csL` component by component, after every product or limit projection, with the actual termwise `shiftFunctorObjXIso`. These are σ and π of the node after applying `localizedShift`. |
| χ(y,x)=((-1)^m y,x) | The forward `roosχ` block states precisely the diagonal `biprod.map` with `m.negOnePow` on the degree p product summand, and no scalar on degree p+1. Reindexings are explicit. |
| Inverse has the same formula | The following block gives the inverse comparison with the same `m.negOnePow`, composed with the inverse product and degree reindexings. |
| Natural coherent comparisons, zero and addition | `csP`, `csL` and `csC` are `Functor.CommShift ℤ` structures: each comparison is a natural isomorphism, and its zero/addition laws are fields of that structure. Thus these are more than unrelated isomorphisms for individual shifts. |
| χ η_shift = η[shift] σ | The block beginning `roosι (I⟦m⟧) ≫ ...` states exactly this identity with the termwise limit comparison inserted. |
| π p_shift = p[shift] σ | In Lean's left-to-right composition order: `projection (I⟦m⟧) ≫ localizedShift productFunctor csP I m = localizedShift roosLimitFunctor csL I m ≫ (projection I)⟦m⟧'`. |
| σ[1] δ_shift = (-1)^m δ[shift] π | The next equation has `δ (I⟦m⟧) ≫ (localizedShift ... csL ...)⟦1⟧'` on the left and `m.negOnePow • (localizedShift ... csP ... ≫ (δ I)⟦m⟧' ≫ shiftFunctorComm ... )` on the right. `shiftFunctorComm` is explicitly the canonical [1][m]→[m][1] identification, not an extra sign. |
| Naturality after localization and change of chosen representative | The next block asserts naturality of δ for every map between K-injective injective-term representatives, with the actual product and limit maps. The ε comparison is Q of the already natural `roosι`; all three shift comparisons are natural isomorphisms. The K-injective Hom bijection and tower-homotopy compatibility descend this to derived morphisms; the final normalized d identifies the result with the chosen total derived functor. |

The family δ is indexed uniformly by all tower complexes to make shifted indexing
literal; its normalization, distinguished-triangle and naturality assertions are only
made on the K-injective representatives with injective terms of the node. No definition
selects this family from the existential theorem.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`: `Abelian.functorCategoryAbelian`;
  evaluation preservation from `Limits.FunctorCategory.Basic`, and componentwise
  mono/epi criteria from `Limits.FunctorCategory.EpiMono`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, its shift structure and distinguished triangles.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`. Its complete public theorem
  was read; the helper-private proofs were not treated as public interfaces.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `IsDerivedLimitTriangle`, whose definition is distinguished membership with 1-s.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective` (and the
  associated resolution record in `Injective.Resolution`).
- `WeilConjectures.CategoryTheory.KInjectiveBridge`:
  `CochainComplex.KInjectiveResolutionChoice`; K-injectivity itself is Mathlib's
  `CochainComplex.IsKInjective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `Pi.π`, `Pi.lift`, `Pi.map`,
  `Fan`, `IsLimit`; `Limits.Shapes.Countable`: `HasCountableProducts`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, `.Functor`:
  `Pretriangulated`, `IsTriangulated`, `Functor.IsTriangulated`.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosP`, `roosU`, `roosχ`,
  `roosι`, `roosLimitFunctor`, `roosPmap` and their naturality/coordinate declarations.
- `Sheaf.CategoryTheory.TowerProductFunctor`: `InjectiveTowerRoos.productFunctor`,
  whose object and map fields are exactly `roosP` and `roosPmap`. Its laws reuse
  `roosPmap_id` and `roosPmap_comp` from `Sheaf.CategoryTheory.StrictRoosModel`.
  No conclusion of the product-shift theorem is used or imported by this module.
- Proof imports: `CochainComplex.termwise_product_isKInjective_and_isLimit`,
  `CategoryTheory.tower_evaluation_isKInjective`,
  `CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `CategoryTheory.roosF_homotopy_functor`, and the coordinate, inverse, coherence and
  augmentation statements in `Sheaf.Algebra.Homology.EndomorphismFibreCoordinateCalculus`.
  The last two source modules were read from the live server with `scompile.py --source`,
  since the shared read clone did not yet contain them. All stated proof dependencies
  have imports; no new prerequisite statement is needed.

Edge cases checked mathematically before writing and again on rereading:
zero module sheaf and zero coefficient ring; zero complexes; constant towers;
identity resolutions q; non-surjective original transitions (never constrained);
negative, zero and positive cochain degrees; shifts m=0,1,-1,2; successive shifts
1+(-1)=0 and 1+1=2; characteristic two where negOnePow acts trivially. The forward
and inverse diagonal both square to the identity because ((-1)^m)^2=1. The boundary
receives exactly the sign on the first cone coordinate; the first arrow receives none.
There is no empty-tower case, since the node fixes positive natural-number levels;
there is no empty-site exclusion. No AB4* or exact-product binder is present.

Searches made (all via the prescribed wrapper unless noted):

- leanfinder: `Injective tower inverse limit comparison shifted Roos cone signed shift
  isomorphism`: eight hits, including `CochainComplex.mappingCone.shiftIso` and
  `shiftTriangleIso`; none states the injective-tower result with the total-limit
  normalization and no exactness assumption.
- loogle: `CochainComplex.mappingCone, IsKInjective`: no hits; the search service
  reported unknown identifier `IsKInjective`.
- grep Mathlib CategoryTheory: `Roos|roos|injective_tower`: no hits.
- leansearch: `inverse limit K-injective tower shifted mapping cone product signed
  shift comparison`: eight hits on mapping-cone shifts and preservation of
  K-injectivity under shifts, no complete statement match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, patterns for Roos, injective towers,
  signed shifts, and the exact item ID. Existing Roos comparison nodes assume exact
  products; the generic signed cone/product constructions are reusable, but none
  supplies this item as an existing declaration. The exact item ID and the proposed
  full declaration name had no existing source occurrence.
- Read the complete item and every statement dependency's record and source signature;
  read Stacks sites-cohomology.tex Tag 0941 at lines 5066 onward and the blueprint
  coefficient-comparison paragraph named by the node.

No statement dispute or source correction was found. All compilation uses scompile.py.
The repaired delivery contains two modules, the item node and one new definition node,
plus this report.

## Second reading by Q11

A second pass was made with the complete node and module open. Per the dispatcher's
explicit instruction no other agent was started; this section records the worker's
rereading, while the maintainer supplies the independent delivery review.

The pass checked each row above against the actual binders and conclusion, rather
than only declaration names. The cone and kernel inclusion are the existing model,
the product statement keeps its actual localized projections, and the final d equation
ties the chosen q to RF(QX). Forward and inverse signs are on y only. The canonical
[1][m] commutation is present in the boundary formula. All integer and site universes
are explicitly bound, and the site universes are not forced equal to the module
universe. Compiler-detected field-resolution issues on evaluated/limit complexes were
repaired using qualified CochainComplex names; the total-derived natural transformation
also now specifies both localization source categories explicitly. No mathematical
hypothesis or conclusion changed in those elaboration repairs.


## New nodes

`def-pur-tower-product-functor`, module `Sheaf.CategoryTheory.TowerProductFunctor`,
defines `CategoryTheory.InjectiveTowerRoos.productFunctor`. It packages the existing
strict-Roos product, rather than defining a new product model. The category and its
independent object/morphism universes are `{A : Type a} [Category.{b} A]`; abelianness
and countable products are `[Abelian A] [HasCountableProducts A]`. Strict natural-number
towers and unbounded integer cochain complexes are the domain
`CochainComplex (ℕᵒᵖ ⥤ A) ℤ`; the codomain is `CochainComplex A ℤ`. The object clause
is `obj := roosP`, the map clause is `map := roosPmap`, and the functor laws are
`map_id := roosPmap_id` and `map_comp := roosPmap_comp`. All four reuse the existing
interface of `def-weil-strict-roos-model`. Products use exactly the Mathlib
`Pi.map` and categorical products recorded by `def-weil-category-product`.
There is no shift structure, exactness assumption or transition condition in this
definition, and no postponed proof or data choice. The item now uses this functor
for its existential `csP` and every product shift comparison.

New-node searches (recorded with results in `mathlib_searches`):

- LeanSearch, `termwise product functor from cochain complexes of inverse towers to
  cochain complexes`: 8 hits for generic products of functors, bifunctors and complexes;
  no strict-tower product functor.
- LeanFinder, `termwise product functor on cochain complexes of inverse towers`:
  8 hits on bifunctors, their shifts and mapping cones; no exact specialization.
- Wrapper grep, `roosPmap|towerProductFunctor|productFunctor`, Mathlib CategoryTheory:
  2 hits for `binaryProductFunctor` on types.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, `dag/nodes` and
  `dag/lean_names_upstream.json`: no node with this definition; `StrictRoosModel`
  has the exact data/laws to package. `ProductShift.productFunctor` is generic, and
  `RoosCommShift.productFunctor` has a different source category. This delivery
  follows the explicit return instruction to own the tower specialization in a
  definition node. `tools/blueprint_refs.py search 'tower product'` returned
  `0 blueprint nodes match 'tower product'`; `ancestor` returned
  `thm-pur-rational-and-qbar-purity`, used in the new node's blueprint provenance.

Edge cases of the definition: the zero category/complex and zero coefficient ring
remain allowed; arbitrary tower transitions are allowed; there is no boundedness
restriction and site/module universes remain independent. Identity and composition
are the existing proved `roosPmap` laws, including on the zero complex.

## Repair of return L

Return L on immutable head `4919a5f9d8e2` requested one repair: the theorem
`lem-weil-product-comm-shift` was cited only to obtain its helper functor. Added
`def-pur-tower-product-functor` with its own module, citing the strict Roos model
and categorical products; moved the product-functor declaration to that module
and gave it the explicit existing data and laws. The item imports that definition
module, uses it for `csP`, cites its node and drops `lem-weil-product-comm-shift`
from `stmt_deps`. No F3 module is edited, no replacement theorem is cited, and the
node's mathematical statement and theorem signature are unchanged. The helper's
name is retained so every previously reviewed formula still uses the same product
objects and maps. Only the owning module and the packaging of its laws changed.

The saved packet was first dry-run as instructed and passed at `4e25251f70f`;
that mechanical pass did not discharge return L, so the explicit requested repair
was made before delivery. Compared the saved node with the current shared node:
all non-Lean fields except the authorized statement-dependency additions agree.
The delivery wrapper refreshes/rebases its isolated worktree on the current server
branch; no git command or edit is performed in the read-only shared repository.

Required self-check after repair: reread both modules and both nodes. The functor
has actual `roosP`/`roosPmap` data, reuses the existing laws and has no `sorry`.
The main theorem's only postponed proof remains its own `sorry`. Its complete
hypothesis/clause matching and edge-case audit above remain applicable: `csP` is
still tied to every explicit product projection, and all cone, inverse, coherence,
normalization, boundary sign and total-derived-limit clauses are unchanged.

Server validation: `scompile.py` compiled both delivered modules cleanly (the
product definition in 1.6 s and the main theorem in 8.8 s). The repaired packet's
first dry run found one provenance mismatch: the live server has an additional
`lem-pur-adic-purity-scalar-naturality` at the end of the item's blueprint via.
Updated the new node's via to the complete server chain printed in that diagnostic.
No Lean statement or definition changed in this metadata repair.
