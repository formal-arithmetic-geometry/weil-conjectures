/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Affine pushforward and ideal-module products

Source: Stacks Project, Cohomology of Schemes, Lemma 01YP
(blueprint: lem-weil-pbc-affine-pushforward-ideal-product).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- For an affine morphism, the extended ideal times a quasi-coherent module is
quasi-coherent, and its pushforward equals the ideal times the pushforward, as subobjects.
The upstairs multiplication uses pullback of the inclusion followed by the adjoint
structure-sheaf map; `idealModuleProduct` takes the image after tensoring with `F`.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YP
(blueprint: lem-weil-pbc-affine-pushforward-ideal-product).

Proof:
1. Pullback and tensor product preserve quasi-coherence
   [lem-weil-pbc-module-pullback-quasi-coherent,
   lem-weil-pbc-quasi-coherent-tensor-product-affine-sections]. The image of the
   multiplication map between quasi-coherent modules is quasi-coherent
   [lem-weil-pbc-quasi-coherent-module-cokernel-image].
2. Over an affine `V ⊆ X`, its preimage `U` is affine. Put `A = O_X(V)`, `B = O_Y(U)`.
   The pullback-section comparison and the tensor-section comparison identify the map
   on pure tensors with `a ⊗ b ⊗ s ↦ b f♯(a) s`, by naturality of the adjunction unit
   and the characterization of the adjoint structure-sheaf map
   [lem-weil-pbc-module-pullback-affine-sections,
   lem-weil-pbc-module-pullback-structure-sheaf].
3. Pure tensors generate, so its image on `U` is `I(V) F(U)`: the factor `b` is
   absorbed into `s`, and every generator is obtained with `b = 1`.
4. An affine morphism is quasi-compact and quasi-separated, so its pushforward is
   quasi-coherent [lem-weil-pbc-affine-morphism-permanence, pqf-lem-pushforward-qcoh].
   Pushforward evaluates on the preimage; its upstairs product has sections `I(V) F(U)`.
5. The downstairs product has the same sections by
   [lem-weil-pbc-ideal-times-quasi-coherent-affine-sections].
6. Affine opens form a basis [lem-weil-pbc-affine-opens-basis]. Two subsheaves that agree
   there agree everywhere by restriction and sheaf gluing, proving the subobject equality. -/
theorem affine_pushforward_ideal_product {X Y : Scheme.{v}} (f : Y ⟶ X) [IsAffineHom f]
    (F : Y.Modules) [F.IsQuasicoherent] {I : X.Modules} [I.IsQuasicoherent]
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] :
    (idealModuleProduct
      ((Modules.tensorPullback f).map ι ≫ Modules.tensorPullbackObjUnitToUnit f)
      F).IsQuasicoherent ∧
    Subobject.mk (image.ι (idealModuleProductι ι ((Modules.pushforward f).obj F))) =
      Subobject.mk (image.ι ((Modules.pushforward f).map (idealModuleProductι
        ((Modules.tensorPullback f).map ι ≫ Modules.tensorPullbackObjUnitToUnit f) F))) := by
  sorry

end
end AlgebraicGeometry.Scheme
