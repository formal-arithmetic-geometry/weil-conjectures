## Worker report

Item: `lem-pur-inverse-image-tensor-adjoint-test`, group N9, stage 2.
Module: `Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest`.
Namespace: `AlgebraicGeometry.ProEtaleTensorComparison`.
The node is unchanged except for `lean`. No new nodes or dependency-node repairs.
All four theorem proofs are exactly `sorry`; no mathematical result is proved here.

The item is represented by three statements, all listed in `lean.declarations`:
`proEtale_inverseImage_tensor_adjoint_test` gives the two bijections, both naturality
assertions, the specified underlying adjunct, and the equality criterion;
`proEtale_inverseImage_tensor_coefficient_evaluations` and
`proEtale_inverseImage_tensor_composition_evaluations` give the two final conditional
calculations. The auxiliary `proEtaleTestModuleUnit_exists` assembles the specified
unit sections into their unique linear sheaf map. `proEtaleTestModuleUnit` selects
this uniquely determined map, rather than data from mere existence. Its components
are the already constructed module-adjunction unit; no action or inverse image is chosen.

Hypotheses and clauses, in the node's order:

| Node text | Lean rendering |
| --- | --- |
| Any morphism h:T'→T | `{T' T : Scheme.{u}} (h : T' ⟶ T)`; no property instance on h |
| Compatible small pro-etale sites | `T.ProEt`, `T'.ProEt`, `ProEt.topology`, `proEtaleBaseChange`; site objects have universe u+1 and morphisms u |
| The specified inverse image, direct image and unit | `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, `proEtaleModuleInverseImage`; `inverseSection` evaluates the existing small-model module unit on original site objects |
| Any commutative coefficient ring sheaf R | `R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}` |
| R-module sheaves M,N | `proEtaleTestModules R`, transparently the recorded `ringedSiteModules`/Mathlib `SheafOfModules` |
| K is an h⁻¹R-module sheaf | `proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)` |
| R-action on h_*K through η_R | `proEtaleTestDirectImage` is Mathlib module `pushforward` along the underlying ring map of the actual commutative-ring adjunction unit |
| The sheaf tensor product and pure tensors | `proEtaleTestTensor`/`tensor` are `siteSheafTensorRight`; `proEtaleTestPure`/`pure` are `siteSheafTensorTmul`, the sheafification-unit image of sectionwise pure tensors |
| α and its displayed adjunct | `α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K`; `proEtaleTestAdjunct h α` is `proEtaleTestModuleUnit ... ≫ (proEtaleTestDirectImage ...).map α` |
| The adjunct is R-linear | It has the actual module-Hom type. The separately named unit-assembly theorem supplies the required linearity/naturality before the definition uses it |
| Hom bijection | First conjunct: `Function.Bijective` of that exact assignment |
| Naturality in M,N,K | Second and third conjuncts: precomposition by `inverse.map (tensorMap a b)` and postcomposition by k, with the corresponding tensor/direct-image maps |
| Underlying maps exactly the specified set adjuncts | Fourth conjunct: equality with `(proEtaleSheafAdjunction h (Type (u+1))).homEquiv`; the existing `moduleSetsIdentification` only identifies the constructed module inverse image with that very set inverse image |
| Bilin_R(M×N,h_*K) | `proEtaleTestBilin`: curried R(V)-linear maps at every V, with compatibility with every restriction. This is exactly a natural map from the pointwise product of underlying sheaves, bilinear on sections, rather than a linear map out of their direct sum |
| Bijection onto Bilin, displayed formula | Fifth conjunct: one family of equivalences E and its explicit evaluation on `α.val.app hV (proEtaleTestUnitSection h (tensor M N) V (pure ...))` |
| Naturality of this bilinear bijection | Two additional clauses on the same family E give its sectionwise precomposition formula in M,N and postcomposition formula in K |
| α=β iff equality on all original unit pure tensors | Last conjunct, with all original V,s,t quantified; no target-site generation hypothesis |
| Supplied b for each map and coefficient ring | Evaluation statements bind b (or bh,bg,bc) as families over every coefficient sheaf on the relevant target and every pair of modules |
| Pure-tensor normalization of b; no invertibility or naturality assumed | `hb`, or `hbh,hbg,hbc`, are precisely the original-unit pure-section equations. There is no naturality or IsIso binder on b |
| Coefficient map φ and canonical π,π' | `φ : R ⟶ S`; existing `coefficientQuotient φ M N`. After inverse image, `scalarIdentification` identifies the two scalar-action presentations; `tensorMap` of these identifications followed by `coefficientQuotient (inverseRingMap h φ)` is π' |
| Both coefficient evaluations | Two conjuncts evaluate the displayed composites on `inverseSection h (tensor (restrict φ M) (restrict φ N)) ... (pure ...)`; both results are `pure ... (inverseSection h M ...) (inverseSection h N ...)` over h⁻¹S |
| Second map g and supplied natural set isomorphism δ | `{T'' T' T}` and `(g : T'' ⟶ T')`; δ is a natural isomorphism between the actual set inverse-image functors for g≫h and h followed by g |
| Compatibility of δ with transported operations | c is the induced ring isomorphism; d gives its linear module isomorphisms after restriction through c.hom. `hc` and `hd` say their underlying maps are exactly δ transported through the existing ring/module set identifications. These bind the algebraic realizations of the compatibility already assumed in the node |
| Unit normalization through the canonical associator | `hδ` is equality of the two unit natural-transformation components for every set sheaf H. `lowerStarComp` is the actual direct-image comparison induced by the canonical fibre-product associator; equality of these sheaf maps is exactly equality on every original object and section |
| Both composition evaluations | First route: d(tensor M N), then g⁻¹(bh), then bg. Second route: bc, tensorMap(d M,d N), then coefficientQuotient c.hom. Both values are the same pure tensor of iterated unit images, explicitly restricted by `(MorphismProperty.Over.pullbackComp ... g h).hom.app V).op` to the composite base-change object |
| Conditional evaluations, no existence assertion for b or δ | All these data and normalization/compatibility equations are binders of the evaluation theorems, not conclusions |

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is explicitly a convention-only collection;
  this item needs only Mathlib `Scheme` and its Hom, not any extra morphism property.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `proEtaleBaseChange`, `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleModelRingUnit`, `proEtaleModuleInverseImage` and the small-model transports.
  The node's action recipe works for the arbitrary R here; no constant-coefficient
  replacement or finite/discrete coefficient assumption is made.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`; this is Mathlib's existing category and linear Hom.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, whose public imports
  expose `siteSheafTensorRight` and `siteSheafTensorTmul` at independent site universes.
  No second tensor is introduced.
- Proof-plan imports: `Sheaf.CategoryTheory.GeometricModuleConstruction`,
  `SheafOfModules.geometric_module_construction`;
  `Sheaf.CategoryTheory.GeometricModuleTransport`,
  `SheafOfModules.geometric_module_transport`;
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`,
  `SheafOfModules.tensor_bilinear_universal`. Their specialized category universes
  are handled on the already specified AsSmall models in the future proof, not by
  equating the object and Hom universes in this statement.
- Reused canonical helpers from the live
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`:
  `Rings`, `Modules`, `inverseRing`, `inverse`, `tensor`, `pure`, `inverseSection`,
  `restrict`, `inverseRingMap`, `coefficientQuotient`, `scalarIdentification`,
  `tensorMap`, `ringSetsIdentification`, `moduleSetsIdentification`, `ringMapSets`,
  `moduleMapSets`; their signatures and docstrings were read, and the current server
  source was checked with `scompile.py --source`. These helpers retain their existing
  constructions and unique normalizations. This delivery does not use that module's
  `comparison`, `comparison_exists`, `moduleComp`, `moduleComp_exists`, `setComp_unique`
  or main `inverseImage_tensor_comparison` theorem to replace the supplied data.

Import-plan issue: the old parent module contains the canonical helpers and its main
statement in one file. Reusing the helpers requires its import here. Consequently the
reverse proof-only import of this module into
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` must be omitted under
stages/2-statements.md §3(7), which explicitly permits omissions that would close an
import cycle. No source file of the read-only library was changed, and no DAG edge to
the parent was added. A future proof-module separation can expose the helpers on their
own; the mathematical proof plan here uses the three generic proof dependencies above,
not the parent's tensor-comparison theorem.

Edge cases checked before finalizing: h or g the identity (the associator is still
present, with no strict-composition assumption); zero M,N,K; the zero coefficient ring;
φ=id and maps to the zero ring; empty source or target schemes; arbitrary commutative
ring sheaves rather than constant or finite coefficients. Bilinear maps are compatible
with all restrictions and the section test quantifies over every original object. No
nonzero, nonempty, finite-generation, invertibility-of-b or naturality-of-b assumption
appears. The site object universe u+1 and Hom universe u remain distinct throughout.
No statement correction or mathematical dispute was found.

Searches actually run (msearch.py N9 and this item):

- LeanFinder: `Adjunction for inverse image of tensor product module sheaves bijection
  to bilinear maps and pure tensor equality test`. Eight hits, including
  `SheafOfModules.PullbackConstruction.adjunction` and sectionwise presheaf tensor
  definitions; none states this node's full test and supplied-data evaluations.
- Loogle: `SheafOfModules.pullbackPushforwardAdjunction,
  SheafOfModules.tensor_bilinear_universal`. Zero hits; the service reports the second
  identifier unknown (it is project/upstream code, not Mathlib). This is not recorded
  as evidence that the theorem does not exist: the project's declaration was opened
  and imported directly.
- Mathlib grep: `homEquiv|[Bb]ilinear` in `Algebra/Category/ModuleCat/Sheaf`. Twenty-five
  hits, including the actual pullback adjunction; no exact statement of the whole node.
- LeanSearch: `Adjunction of inverse image and direct image module sheaves gives a
  natural bijection from tensor morphisms to bilinear sheaf maps`. Eight hits including
  Mathlib's sheaf-module pullback adjunction and presheaf adjunction; no exact match.
- `rg` of `lean/WeilConjectures` for this node id: none. `rg` of both project source
  roots for bilinear/adjunction/tensor names found the upstream tensor universal
  property, the additive-only `CategoryTheory.SiteBilinearMap` (not R-bilinear), and
  the canonical parent helpers listed above. `dag/lean_names_upstream.json` confirms
  the upstream tensor universal property. Exact searches for the new declaration
  names in both roots and the name index found no collision.

Validation uses only prescribed `scompile.py` and `deliver2.py` wrappers. Initial
elaboration failures in an attempted direct transport of the full module unit were
repaired by using the existing evaluated unit and its unique assembly, preserving its
components and linear structure. No timeout limit or launcher script was changed.

## Second reading by N9

This is a second pass by the same dispatcher-started worker; the brief explicitly
forbids starting another agent. The maintainer's independent review remains separate.
I re-opened the complete node and the delivered file side by side.

The core has exactly the arbitrary h,R,M,N,K and action through η_R. It uses the actual
module inverse image, not a new functor or the constant-coefficient pullback. The
underlying-set comparison uses the same set adjunction; Bilin has both scalar-linearity
conditions and restriction compatibility. On this pass I made the naturality of the
bilinear equivalences explicit in M,N,K, on one shared family E. The final iff tests
only original unit pure tensors and imposes no generation assumption.

For coefficient change I checked both domains, the restriction-of-scalars occurrences,
and the scalar identifications: π is the existing canonical quotient and the second
route uses precisely its inverse-ring counterpart. The two asserted results lie in the
larger-ring tensor and contain the two larger-ring unit images.

For composition I checked the actual natural δ type, its unit equation, c and d's
underlying δ equations, and both composites. The common value is transported in the
correct direction along pullbackComp.hom.op. I changed the three b families and their
normalizations to quantify explicitly over every coefficient ring sheaf on the relevant
target, matching the node's supplied-family wording. c and d encode algebraic
compatibility of the supplied δ; no canonical δ or canonical b was substituted.
The theorem does not assert existence, naturality or invertibility of b. All lines
are at most 100 characters, variables/universes are explicitly bound, all theorem
bodies are sorry, and all definition data are actual constructions or uniquely
characterized data. No mismatch requiring a node correction remains.
