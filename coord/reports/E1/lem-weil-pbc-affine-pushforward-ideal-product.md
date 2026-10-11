## Worker report

Module `Sheaf.AlgebraicGeometry.AffinePushforwardIdealProduct` states
`AlgebraicGeometry.Scheme.affine_pushforward_ideal_product`, with a sorry proof.
The source is Stacks Tag 01YP, https://stacks.math.columbia.edu/tag/01YP,
opened and read directly because the local literature checkout has no coherent.tex.
Its first proof paragraph gives quasi-coherence of the upstairs image; its assertion
is equality of the two subsheaves. No statement correction and no disputed statement.

Hypothesis and clause correspondence:

- Schemes X and Y and affine f:Y→X are `{X Y : Scheme.{v}} (f : Y ⟶ X)
  [IsAffineHom f]`. The universe v is arbitrary and shared, as for Mathlib schemes.
- The quasi-coherent O_Y-module F is `(F : Y.Modules) [F.IsQuasicoherent]`.
- The quasi-coherent ideal I⊆O_X is `{I : X.Modules} [I.IsQuasicoherent]
  (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]`.
  An O_X-linear monomorphism into O_X is precisely a sheaf of ideals, up to the
  identification by its inclusion; neither finite type nor coherence is assumed.
- f* and f_* are `Modules.tensorPullback f` and `Modules.pushforward f`.
  epsilon_f is `Modules.tensorPullbackObjUnitToUnit f`, explicitly the adjoint of
  `SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`.
- The upstairs product is `idealModuleProduct ((Modules.tensorPullback f).map ι ≫
  Modules.tensorPullbackObjUnitToUnit f) F`. The existing definition takes the image
  of the tensor of this composite with F followed by the left unitor. Functoriality
  of tensor makes this exactly the node's three-arrow composite, not a different product.
  Pullback of ι is not required to be mono: tensor pullback need not preserve monos.
- Clause (1) is `.IsQuasicoherent` of that image. The image's inclusion is
  `idealModuleProductι`, a canonical image monomorphism, so it is a submodule of F.
- Clause (2) is equality in `Subobject ((Modules.pushforward f).obj F)` of the two
  displayed `Subobject.mk (image.ι ...)` expressions. On the left the inner map is
  the downstairs product inclusion. On the right it is the pushforward of the
  upstairs product inclusion. Taking their images packages both inclusions as
  subobjects without requiring reducibility-based typeclass synthesis for the
  existing `idealModuleProductι` definition. The inner inclusions are monomorphisms
  (images are mono, and pushforward is a right adjoint, hence preserves monos), so
  taking their images changes neither subsheaf. This states equality inside f_*F,
  rather than just an abstract isomorphism between two modules.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `AlgebraicGeometry.IsAffineHom`:
  definition is affineness of preimages of every affine open.
- `pqf-def-coherent`'s module `Sheaf.AlgebraicGeometry.Coherent` was read. Its
  docstring identifies the quasi-coherent clause with Mathlib's
  `SheafOfModules.IsQuasicoherent`, from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, used here directly.
  `RingedSpace.IsCoherent` is not used: the node assumes quasi-coherent only.
- `Sheaf.AlgebraicGeometry.TensorPullback`, `Scheme.Modules.tensorPullback`,
  including full object and map definitions; `Mathlib.AlgebraicGeometry.Modules.Sheaf`,
  `Scheme.Modules.pushforward`, with its section formula.
- Dependency module in this delivery, `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`,
  `Scheme.Modules.tensorPullbackObjUnitToUnit` and its isomorphism/unit-characterization
  theorem; it uses `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`,
  `Scheme.Modules.exists_tensorPullbackAdjunction`, and Mathlib
  `SheafOfModules.unitToPushforwardObjUnit` from `PullbackFree`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` records the existing
  `SheafOfModules.monoidalCategory` and `tensorObjIsoSheafification` in
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`; their signatures,
  definitions and docstrings were read. They are used by the existing product module.
- `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`, `Scheme.idealModuleProduct`
  and `Scheme.idealModuleProductι`. The already-landed node
  `lem-weil-pbc-ideal-module-product-stalk` was added to stmt_deps as allowed by
  brief-stage2 §5; no second product definition was written.
- Mathlib `CategoryTheory.Limits.image`, `image.ι` and `Subobject.mk` package images
  with their canonical inclusions.

Edge cases checked before writing: empty schemes are allowed, and no nonempty or
Noetherian condition is introduced. I=0 gives zero products on both sides; I=O_X
reduces to the whole module on both sides via epsilon's isomorphism. F=0 gives zero.
For f=id this is the identical ideal product; arbitrary affine ring maps, including
nonflat maps, are permitted because no monomorphism is assumed for f*ι. The affine
calculation I(M_A)=((IB)M)_A holds also for zero rings/modules. No finite-generation,
characteristic, or independent test-object-universe restriction is introduced.

Searches made:

- msearch.py leanfinder, query “Affine pushforward commutes with multiplication of a
  quasi-coherent ideal and a quasi-coherent module”: eight results, chiefly
  `Scheme.IdealSheafData.ideal_map`, `ideal_map_of_isAffineHom`, `map_ideal`, and
  `comap_map_le`. These concern ideals themselves, not an ideal acting on a module;
  no exact match.
- msearch.py loogle, query `AlgebraicGeometry.Scheme.Modules.pushforward,
  AlgebraicGeometry.IsAffineHom`: zero results.
- msearch.py grep, query `idealModuleProduct|ideal.*[Pp]roduct|pullbackObjUnitToUnit`
  in AlgebraicGeometry: only IdealSheaf/Functorial's pullback-ideal comment;
  no affine-pushforward ideal-module theorem.
- rg in project lean/Sheaf and source WeilConjectures for idealProduct,
  ideal-times, ideal-product and structure-sheaf pullback: existing landed
  `IdealModuleProductStalk` supplied exactly the reusable product construction.
- grep of source WeilConjectures for the item's blueprint id: no match.
- rg of the intended names `tensorPullbackObjUnitToUnit|affine_pushforward_ideal_product`
  across Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  no existing declarations with these names.

All declaration proofs in this delivery are sorry; all definition data is explicit.
The server compile checks both modules together. The initial check exposed only a
shared universe-name collision in the combined file and the inability to synthesize
Mono through the existing product-inclusion definition; both were repaired as above.

## Dependency modules

`lem-weil-pbc-module-pullback-structure-sheaf`: its mathlib_match supplies epsilon
for `Scheme.Modules.pullback`, Mathlib's abstract chosen left adjoint. The item's
recorded pullback definition is the explicit tensor-formula `tensorPullback`, a
different functor, so that map cannot be applied to the pulled-back ideal here.
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf` defines epsilon using the
Hom equivalence of the landed, sectionwise-characterized tensor-pullback adjunction
and states its isomorphism and the specified unit equation. It supplies exactly
the dependency node's notion, for arbitrary scheme morphisms, not only affine ones.
Only the dependency's lean record changes; its mathlib_match stays. No second
structure-sheaf module or monoidal structure is defined. The epsilon definition
contains no sorry; the named theorem contains the expected sorry and a full
natural-language proof. Its proof is the tensor-unit multiplication isomorphism
and the adjunction characterization, as indicated in the original dependency's
Mathlib-match explanation (that node has no proof steps).

## Second reading by E1

I reread the item node, Stacks Tag 01YP, both delivery modules, and all recorded
dependency declarations. The objects and hypotheses match exactly: `{X Y :
Scheme.{v}}`, `f : Y ⟶ X` with `[IsAffineHom f]`, quasi-coherent `F : Y.Modules`,
quasi-coherent `I : X.Modules`, and `[Mono ι]` for the inclusion into the
structure sheaf. No Noetherian, finite-type, flatness, characteristic,
nonemptiness, or extra universe assumption is present.

Clause (1) is rendered by
`(idealModuleProduct ((Modules.tensorPullback f).map ι ≫
Modules.tensorPullbackObjUnitToUnit f) F).IsQuasicoherent`. The existing
`idealModuleProduct` is precisely the image of tensoring the inclusion followed
by the left-unitor multiplication, so this is the node's `f⁻¹ I · F`. Clause
(2) is equality of `Subobject.mk (image.ι ...)` inside
`(Modules.pushforward f).obj F`; the left expression is the downstairs product
and the right expression is pushforward of the upstairs product. It therefore
states equality of subsheaves, not merely an isomorphism.

The dependency epsilon is exactly
`Modules.tensorPullbackObjUnitToUnit f`, defined from
`exists_tensorPullbackAdjunction`; its theorem gives both the isomorphism and
the unit composite equal to `f.toRingCatSheafHom`. The added
`lem-weil-pbc-ideal-module-product-stalk` dependency supplies the existing product
construction and no duplicate definition. The dependency correction was needed
because the recorded Mathlib match used abstract `Scheme.Modules.pullback`,
whereas this node requires the explicit `tensorPullback` functor.

Empty schemes, zero `I` or `F`, `I = O_X`, identity and nonflat affine maps, and
all characteristics remain covered. Searches of Mathlib, WeilConjectures, and
`lean/Sheaf` found no existing declarations for the theorem or tensor epsilon.
No item statement mismatch was found. Both modules compile together with only
the permitted `sorry` declarations.
