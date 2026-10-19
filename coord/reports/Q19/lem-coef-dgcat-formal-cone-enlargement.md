## Worker report

Item: `lem-coef-dgcat-formal-cone-enlargement`, Q19 stage 2.
Module: `Sheaf.CategoryTheory.DgCategoryFormalConeEnlargement`.
Main statement: `CategoryTheory.Dg.formalConeEnlargement : Nonempty (FormalConeCalculus R)`.

The module states the entire construction through characterized witnesses. It does not
choose any object from an unproved existence theorem. All definitions have actual data.
The three preliminary theorems and the main theorem have exactly `by sorry` proofs.
All four belong to this item's statement and its five proof steps:
`representableAction_laws`, `map_closed`, `postcomposition_closed`, and
`formalConeEnlargement`. Each has a source and natural-language proof in its docstring.
The first, second and third justify respectively the representable action, the image
closed-arrow label, and the actual postcomposition chain map used in the mapping cone.

The full statement dependency was read, including all twelve proof steps, its `lean`
record and the complete recorded source module. The dependency is
`lem-coef-dgcat-free-cell-calculus`, module
`Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`; the declarations used are
`CategoryTheory.Dg.Cat`, `hom`, `comp`, `mul`, `unit`, its strict category instance,
and the dg functor maps. The dependency theorem `freeCellCalculus` is available for
stage 3 and its module is already publicly imported for the statement. No unstated
DAG prerequisite is needed. The auxiliary definitions here are the objects explicitly
introduced by this item, rather than independent statements of other DAG nodes.

Source read: Tabuada, arXiv:0710.4303, Chapter 1, Definitions 1.3--1.4 on printed
p. 26, Proposition 1.7 on printed p. 27, and the Yoneda/full cone subcategory and
extension in Lemma 1.10 on printed p. 29. These are PDF page indices 25, 26, 28.
The node's marked agent calculations supply the arbitrary-degree, simultaneous-label
and matrix-functor formulation; the module follows those calculations.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
|---|---|
| Commutative ring R, arbitrary small R-linear cochain dg category with signed Leibniz | `(R : Type u) [CommRing R]`, and `C : Cat R`, using exactly the recorded enriched-category/cochain-tensor convention. There are no field, characteristic, nonzero, flatness or distinct-object hypotheses. |
| Right modules are families of complexes M(z) | `RightModule.obj : C → CochainComplex (ModuleCat R) ℤ`. The universe is the small-module universe of the dependency's size convention. The category of all these modules has object universe `u+1`, not an incorrectly small object set. |
| Bilinear actions M(y) tensor A(z,y) to M(z) | `RightModule.action`, a curried pair of R-linear maps in every pair of integer degrees. This is the tensor-product bilinear universal property without introducing a second tensor product. |
| Unitality and associativity | `RightModule.laws`, with `IsRightAction.unit` and `.assoc`, using the recorded `unit` and `mul`. |
| d(ma)=d(m)a+(-1)^degree(m) m d(a) | `IsRightAction.leibniz`, with the exact sign `j.negOnePow` and explicit arithmetic degree transports. |
| Homogeneous maps of degree n commute with the unchanged right graded actions | `ModuleMap.cochain`, the existing Mathlib `HomComplex.Cochain` of degree n, and `ModuleMap.action_comm`. No sign is inserted into action compatibility. |
| dgMod(A) has exactly all homogeneous module maps | `ModuleSystem.category`, `.object` and `.coordinates`: objects are in bijection with all right modules and each homogeneous Hom degree is in bijection with all `ModuleMap`s. `.add` and `.smul` make these coordinates linear. |
| Differential partial q=d_N q-(-1)^n q d_M | `ModuleSystem.differential`, explicitly Mathlib `HomComplex.δ n (n+1)` on each objectwise cochain. The existing enriched-category structure supplies square-zero and dg Leibniz. |
| Composition is composition of graded maps; units | `ModuleSystem.composition`, using `Cochain.comp`, and `.identity`, using `Cochain.ofHom (𝟙 _)`. `enrichedMultiply` uses exactly the dependency's reverse tensor order and Koszul interchange, generalized only to the larger object universe of dgMod. |
| h_x(z)=A(z,x), composition action | `representable.obj` is literally `hom R C z x`; its action is literally `compositionLinear`, the tensor curry of the recorded `comp`, with its laws supplied by the named auxiliary theorem. |
| Evaluation at 1_x is an isomorphism of complexes for every M | `ModuleSystem.Yoneda`: the isomorphism is a cochain-complex isomorphism, not just a degreewise bijection. Its first equation fixes its forward map to evaluation at `unit R C x`. |
| Inverse sends m to a ↦ ma | The second equation of `ModuleSystem.Yoneda` fixes every degree and every component of the inverse to `M.action z x n j m a`. |
| Small labelled objects all h_x and all C_u for closed degree-zero u | `ClosedArrow` has endpoints, a degree-zero element and its actual closedness proof; `ConeLabel` is the disjoint inductive sum of `.rep x` and `.cone a`. `ConeSystem.label` is a bijection onto its `Cat R`, so there are exactly those labels. |
| C_u is h_y direct sum h_x[1], shift degree j+1 | `ConeSystem.coneCoordinates` is an R-linear equivalence in each degree with `A(z,y)^n × A(z,x)^(n+1)`. |
| Unchanged right graded action on the shift | `ConeSystem.cone_action` fixes both coordinate actions to recorded ordinary composition, with no extra sign. |
| Differential D_u=(d_y,u;0,-d_x) | `ConeSystem.cone_differential` fixes the coordinates to `(da+ub,-db)`, including the exact sign and cross term. |
| Morphism complexes all homogeneous module maps, with the same differential | `ConeSystem.comparison` is a complex isomorphism with the corresponding `moduleHom`. `.comparison_comp` and `.comparison_unit` identify composition and units with dgMod, making this the full dg subcategory on its specified modules. |
| Embedding x ↦ h_x identifies original Hom complexes and preserves units/composition | `ConeSystem.embedding` is an actual dg functor, `.embedding_obj` identifies its object labels, `.embedding_full` makes each actual Hom map an isomorphism. `.embedding_formula` fixes its underlying module maps to `representableCochain`, i.e. postcomposition by the original arrow. Unit and composition preservation are properties of this dg functor. |
| Hom(h_z,C_u) is the specified ordinary cone of u ∘ - | `postcomposition` is the actual closed-arrow chain map, defined with Mathlib `Cocycle.homOf`; `ConeSystem.homConeIso` is an isomorphism to Mathlib `mappingCone`. `HomConeNormalization` fixes its two components to the matrix entries using the actual mapping-cone projections, so it is not an unspecified comparison. |
| Four coordinate maps have degrees 0,0,-1,1 | `ConeCoordinates.inY`, `.outY`, `.inX`, `.outX`. Their module normalization fields identify them with the four actual coordinate maps under `coneCoordinates`; their matrix fields are the corresponding elementary unit matrices. |
| Two identity compositions, two zero compositions, and sum identity | `ConeCoordinates.outY_inY`, `.outX_inX`, `.outY_inX`, `.outX_inY`, and `.partition`, respectively. Closedness is not assumed. |
| Degree-n cone-to-cone maps have all four displayed entries | `ConeSystem.matrix` is a linear equivalence onto `ConeMatrix`. Its degree formula is `n + targetShift - sourceShift`; with shifts `(0,1)` this gives exactly `(n,n-1;n+1,n)`. `coneEntry00/01/10/11` just normalize arithmetic degrees. |
| Composition is ordinary matrix multiplication | `ConeSystem.matrix_comp` equates composition to the explicit finite sum `coneMatrixMultiply`, with no extra Koszul sign in entry multiplication. `.matrix_embedding` fixes the original 1-by-1 matrix. Together with the elementary coordinate matrices, this also fixes every matrix entry by projection/composition/inclusion, rather than allowing an arbitrary coordinate equivalence. |
| Matrix differential is D_v M-(-1)^n M D_u | `ConeSystem.MatrixDifferential` gives all four equations: top left `da+vc`, top right `db+vd-(-1)^n au`, bottom left `-dc`, bottom right `-dd-(-1)^n cu`. Here each d is the original Hom-complex differential in that entry's degree. Thus the equation includes the shifted diagonal signs, not just the off-diagonal terms. The module differential additionally fixes it on every rectangular Hom. |
| Every dg functor extends, with the stated labels | `FormalConeCalculus.extend` is an actual dg functor between the small cone categories. `.extend_obj` uses the concrete `mapConeLabel` and `mapClosedArrow`; `.extend_embedding` identifies its restriction to the original dg category. |
| Applies F to every matrix entry | `FormalConeCalculus.extend_matrix`, for every source/target label, degree and row/column, identifies the entry with the actual original chain map `F.map` applied to that entry. Heterogeneous equality only transports the specified object and arithmetic degree equalities. |
| Extensions preserve identities and composition of dg functors | `FormalConeCalculus.extend_id` and `.extend_comp` are strict equalities of dg functors, not merely natural isomorphisms. |

All variables and universes are explicitly bound; `set_option autoImplicit false` is
in the module. The theorem introduces witnesses; there is no `Classical.choose` of a
bare existence statement and no definition whose data is `sorry`. The only postponed
proofs are the four named theorems listed above. Existing Mathlib cochains, complex
isomorphisms, tensor products, enriched functors, cocycles and mapping cones are reused.

Edge cases checked before the finished statement:

* Empty dg category: there are no cone labels; modules still form the correct family
  over an empty object type. The small category can be empty and every object-indexed
  equation is correctly vacuous, while the module category still has its zero family.
* Zero ring and characteristic two: no nonzero or invertibility hypothesis; signs use
  integer scalar multiplication, so the negative signs specialize correctly.
* Zero attaching arrow, coincident endpoints, zero Hom complexes, and repeated or equal
  modules: cone and representable labels remain disjoint, and no unwanted object
  injectivity for the original-to-cone inclusion is asserted as a bijection onto all cones.
* Every positive, zero and negative integer degree: the shift convention gives top right
  degree `n-1`, bottom left `n+1`, inclusions degree `-1`, projection degree `1`.
* Graded split maps need not be closed: none of the four coordinate maps is required to
  be a cocycle. For nonzero u, the projection to h_y generally fails to commute with d.
* A nonfaithful dg functor, including one identifying objects or arrows, is allowed.
  The label image and entrywise extension require neither injectivity nor equivalence.
* The matrix differential was expanded independently at general n, and at n=0 and n=-1:
  the upper-right sign is `-(-1)^n au` and the lower row's internal differential is negative.

Searches for existing declarations:

1. `msearch.py ... leanfinder` query: “Strict dg Yoneda evaluation homogeneous right dg
   module maps and functorial labelled mapping cone category”. Eight hits, including
   `ChainComplex.linearYonedaObj`, `HomologicalComplex.evalCompCoyonedaCorepresentableBySingle`,
   `CochainComplex.ofHom` and mapping-cone functors; none defines this arbitrary-R
   dg-module category or formal cone enlargement.
2. `msearch.py ... loogle` query: `EnrichedCategory, HomComplex, mappingCone`.
   Zero hits (the service reported unknown identifier `EnrichedCategory`). The actual
   Mathlib enriched-category, HomComplex and mapping-cone sources were read directly.
3. `msearch.py ... grep` query: `DGModule|DgModule|dgYoneda|RightModule|FormalCone`.
   Only one unrelated two-sided-ideal `rightModule` instance.
4. `msearch.py ... leansearch` query: “Differential graded module Yoneda isomorphism
   and full cone enlargement”. Eight hits concerning ordinary Yoneda/limits and
   `ChainComplex.linearYonedaObj`; none states the node.
5. `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`, including
   the item id and `RightModule|dgYoneda|DGModule`, and a second declaration-name collision
   search in Mathlib and both project trees. No exact theorem or arbitrary-R module
   interface. Existing `SemiFreeDGModule` uses additive/integral categories;
   `DGModuleSemiFreeReplacement` uses `ULift ℤ` coefficients and monoidal-opposite
   enrichment. Their full relevant signatures/docstrings were read. Neither interface
   supplies modules over the recorded arbitrary-R `Dg.Cat` without introducing the
   missing R-linear action, so neither is a replacement for this item's definitions.
6. Read the existing `DgCategoryFreeCellCalculus` module in full, Mathlib
   `CategoryTheory/Enriched/Basic`, `Enriched/EnrichedCat`, and
   `Algebra/Homology/HomotopyCategory/HomComplex` and `MappingCone` for the exact APIs.

No statement correction, dependency-record change, new independent node, or disputed
statement is needed. The node copy changes only `lean`.

Validation: prescribed `scompile.py Q19 lem-coef-dgcat-formal-cone-enlargement ...`
compiled both its sandbox and module forms cleanly, with no errors or warnings.
The delivery dry run is the final worker validation; independent second reading is
reserved for the next worker, as instructed.
## Second reading by Q19

Independent second reader, 2026-10-17. I read the whole node and its five proof
steps beside all 548 lines of the proposed module. I also opened the statement,
recorded declarations and full source module of
`lem-coef-dgcat-free-cell-calculus`, including the live source returned by
`scompile.py --source Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`.
No repair note is present for this item. There are no new nodes or dependency
modules in this delivery; the node copy differs from the base only in `lean`.

Source check: the node cites Tabuada, not Stacks, so there is no Stacks .tex
source place to substitute. I read [the cited thesis](https://arxiv.org/pdf/0710.4303),
Chapter 1, section 1.2, printed pp. 25--26, the proof of Proposition 1.7 on
printed p. 27, and the proof of Lemma 1.10 on printed p. 29. Section 1.2 explicitly
fixes an arbitrary commutative ring with 1 and tensor products over that ring.
Definitions 1.3--1.4 give right modules, homogeneous module maps, their commutator
differential and Yoneda. Proposition 1.7 gives the shifted cone differential and
degree-minus-one matrix; Lemma 1.10 uses the full representable/cone subcategory
and its extension to modules over a second dg category. The arbitrary-degree,
simultaneous-label and entrywise-functor formulations are the node's explicitly
identified elementary calculations; they do not add a field or flatness hypothesis.

Here is my independent inventory and match. All names in the right column are in
`CategoryTheory.Dg` unless qualified otherwise. Every row passes.

| Node object, hypothesis or conclusion | Lean rendering and verdict |
| --- | --- |
| Arbitrary commutative ring R with unit | `(R : Type u) [CommRing R]`; no field, nonzero, characteristic or finiteness restriction. Pass. |
| Small R-linear cochain dg category A and dg functors | Recorded `Cat R = EnrichedCat.{u,u+1,u} (CochainComplex (ModuleCat.{u} R) ℤ)` and its `catCategory`; imports and uses the dependency's actual `hom`, `comp`, `mul`, `unit` and functor maps. No private replacement of A. Pass. |
| Right module is a family of complexes with bilinear right action | `RightModule.obj` and `.action`, with the action a curried R-linear map in both arguments and degree j+k. This is equivalent to the stated tensor-bilinear action. Pass. |
| Unit, associativity, signed module Leibniz | `IsRightAction.unit`, `.assoc`, `.leibniz`; the latter uses `j.negOnePow`, the degree of the module element, and only arithmetic transports. Pass. |
| All degree-n R-linear maps commuting with the unchanged action | `ModuleMap.cochain` is an objectwise Mathlib `Cochain` and `.action_comm` has no additional sign or closedness condition. Pass. |
| dgMod(A), all such objects and maps, its commutator differential, ordinary composition and units | `ModuleSystem.object` is an equivalence with all right modules; `.coordinates` is an equivalence with all homogeneous module maps. `.add`, `.smul`, `.differential`, `.composition`, `.identity` prescribe their algebraic operations. Mathlib `δ n (n+1)` has sign `(-1)^(n+1)`, hence exactly `d_N q-(-1)^n q d_M`. Pass. |
| Representable h_x(z)=A(z,x), composition action | `representable.obj` is literally `hom R C z x`; `.action` is `compositionLinear`, the curry of the recorded composition. Its named proof theorem supplies only the laws. Pass. |
| Evaluation at 1_x is a complex isomorphism, inverse m maps a to ma | `ModuleSystem.Yoneda` quantifies over every M and x, supplies a complex isomorphism, fixes its forward component at `unit R C x`, and fixes every inverse component to `M.action`. Pass. |
| Small labels h_x and C_u for every closed degree-zero u:x→y | `ClosedArrow` contains both endpoints, the degree-zero arrow and actual closedness; `ConeLabel.rep`/`.cone` form a disjoint label sum. `ConeSystem.label` is an equivalence with its small `Cat R`. Pass. |
| C_u is h_y plus h_x[1], degree j+1, unchanged graded right action | `ConeSystem.coneCoordinates` is a linear equivalence with `(A(z,y)^n × A(z,x)^(n+1))`; `.cone_action` specifies ordinary composition in both coordinates, with no extra sign. Pass. |
| Cone differential (a,b) maps to (da+ub,-db) | `ConeSystem.cone_differential` gives exactly these two coordinates, using the actual `ClosedArrow.arrow`. Pass. |
| Full dg subcategory: all module maps, same differential, composition and units | `ConeSystem.comparison` is a Hom-complex isomorphism to `moduleHom`; `.comparison_comp` and `.comparison_unit` fix its composition and unit. Pass. |
| Embedding x maps to h_x and identifies all original Hom complexes | `embedding` is an actual dg functor; `.embedding_obj` specifies labels; `.embedding_full` says its actual complex map is an isomorphism; `.embedding_formula` fixes it to actual postcomposition `representableCochain`. Pass. |
| Hom(h_z,C_u) is the displayed cone of actual u∘- | `postcomposition` is made from the actual graded postcomposition cocycle; `homConeIso` targets Mathlib `mappingCone` of that chain map. `HomConeNormalization` identifies its target and shifted-source projections with the two matrix entries. Pass. |
| Four graded coordinate maps of degrees 0,0,-1,1 | `ConeCoordinates.inY`, `.outY`, `.inX`, `.outX` have those exact degrees. Their `module_*` fields fix the actual inclusions/projections in `coneCoordinates`; the `matrix_*` fields fix their elementary unit matrices. Pass. |
| Two identity composites, two zero composites, sum decomposition of identity; maps need not be closed | `outY_inY`, `outX_inX`, `outY_inX`, `outX_inY`, `partition`; no cocycle predicate is imposed on the four maps. Pass. |
| All degree-n cone maps have entries (n,n-1;n+1,n) | `ConeMatrix` uses `n + targetShift - sourceShift`; shifts `(0,1)` give precisely these degrees. `ConeSystem.matrix` is a linear equivalence, not just an injection. Pass. |
| Matrix coordinates describe the underlying graded maps, with ordinary matrix multiplication | `matrix_comp`, `matrix_embedding`, and the elementary coordinate maps determine each entry by projection, composition and inclusion. Thus the matrix equivalences cannot be unrelated coordinates. `coneMatrixMultiply` is the finite sum of ordinary `mul` products. Pass. |
| Differential D_v M-(-1)^n M D_u | `ConeSystem.MatrixDifferential` spells out all four entries: da+vc; db+vd-(-1)^n au; -dc; -dd-(-1)^n cu. These are the expansion with entry degrees above and the target shift's internal sign. Pass. |
| Every dg functor extends with h_x and C_u labels, applying F to entries | `FormalConeCalculus.extend`, `.extend_obj`, `.extend_embedding`, `.extend_matrix`; all rectangular Hom matrices are covered and each entry is the original `F.map`, with only forced object/degree identifications. Pass. |
| Extension preserves identities and composition | `.extend_id` and `.extend_comp` are equalities of dg functors. The simultaneous witness packages the functorial choices required by this clause. Pass. |
| Existence, without extra input hypotheses | `formalConeEnlargement : Nonempty (FormalConeCalculus R)`; its dependent fields quantify over all the C, modules, labels, degrees and functors above. There is no assumption of the desired calculus. Pass. |

I checked the heterogeneous equalities rather than treating them as automatic
transport notation. In `embedding_formula` and `extend_matrix`, the displayed
object equalities imply equality of the Hom types, so the HEq antecedents admit the
actual image element; they do not make the normalization vacuous. In the module
coordinate fields, `representable_eq` gives the corresponding type equalities.
The heterogeneous comparison in composition only identifies the equal integer
degrees p+q and q+p after composing the underlying cochains.

Edge cases: the empty category has no representable or cone labels, but the module
family over it is still allowed. There is no `Nonempty C` requirement. The zero ring,
zero Hom complexes, zero attaching arrow, coincident endpoints, repeated labels,
and nonfaithful dg functors are all admitted. Characteristic two specializes the
integer signs correctly. The shift and matrix degrees work for every integer,
including n=0 and n=-1. In particular the bottom-left entry has degree n+1 and its
internal differential has the negative sign. The four coordinate maps are graded
maps, not improperly assumed closed. No scheme or scheme-emptiness case occurs.

Universe check: arbitrary `u` is bound explicitly. A's object type and each module
value have universe u, as in the dependency's small-universe convention. The type
of all right modules has universe u+1, and `ModuleSystem.category` uses exactly
that object universe, while its homogeneous Hom modules remain in u (products over
u-small objects and integer degrees). The labelled cone category is u-small.
There is no equality between independently required universes and no omitted
larger-module case within the fixed small-module convention. `autoImplicit false`
is set; every variable and universe in the file is bound.

Independent H4 searches, performed with different queries from the worker:

* LeanFinder: `Graded natural transformations between right dg modules evaluation at
  identity representable cone matrices` returned eight hits. I opened
  `CategoryTheory.GradedNatTrans` in `Enriched/Basic.lean`: it concerns a parameter
  in the monoidal center and enriched functors, not the required arbitrary-R right
  module objects, their full Hom complex, or labelled cone calculus. The other hits
  concern single/double complexes, graded objects and unitors.
* Loogle: `"HomComplex", "Cochain"` returned twelve existing HomComplex declarations.
  I opened the actual `Cochain.comp`, `δ`, `δ_v` and mapping-cone projection definitions;
  the module correctly reuses them, including their degree and sign conventions.
* LeanSearch: `The dg category of modules with graded linear maps and a fully faithful
  representable Yoneda embedding` returned eight ordinary Yoneda results. I opened
  `CategoryTheory.linearYoneda` and `ChainComplex.linearYonedaObj`: the former is
  ordinary R-linear Yoneda and the latter applies Hom(-,Y) to a chain complex. Neither
  states this strict dg-module construction or the item.
* Wrapper grep: `graded.*module|module.*graded|Yoneda.*dg|representable.*cone` returned
  graded-algebra/module declarations. `DirectSum.Gmodule` concerns graded monoid
  actions, with no differential, multiple objects or dg Yoneda/cones.
* Direct `rg` over Mathlib, WeilConjectures and project `lean/Sheaf` for
  `dgMod|DgModule|DGModule|SemiFreeDG|formalCone|twistedComplex|TwistedComplex|dgYoneda`,
  and inspection of `dag/lean_names_upstream.json`, found no exact replacement.
  I read `DGModuleSemiFreeReplacement`'s `RightDGModule` (only lifted integer
  coefficients and monoidal-opposite base) and `SemiFreeDGModule`'s
  `IntegralDGCategory.RightModule` (additive/integer coefficients). Neither supplies
  the given arbitrary-R recorded `Dg.Cat` interface, and neither states the cone
  enlargement. No new node or dependency interface repair is needed.

H5/H6/H8/H9: every definition has actual data. The only four postponed theorems are
`representableAction_laws`, `map_closed`, `postcomposition_closed`, and
`formalConeEnlargement`; each has a source, this blueprint id, and its relevant
stepwise proof in the docstring. No theorem was proved. Arithmetic transport proofs
are not missing object data. The main docstring includes all five node proof steps.
All lines satisfy the 100-character limit. The two public imports serve the actual
statement, and the statement/proof dependency module is included. Declaration names
have no `Sheaf` namespace prefix or upstream collision.

Mismatches found: none. Changes: appended this independent reading only; preserved
the correct Lean source and the node's Lean record. The recorded `lean.statement`
is verbatim `theorem formalConeEnlargement : Nonempty (FormalConeCalculus R)`.

Validation: prescribed `scompile.py Q19 lem-coef-dgcat-formal-cone-enlargement
lean/Sheaf/CategoryTheory/DgCategoryFormalConeEnlargement.lean` compiled both the
sandbox form (9.1 seconds) and module form (17.1 seconds) cleanly, with no warnings
or errors. The delivery wrapper will repeat compilation and run server preflight.
