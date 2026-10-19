/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionData
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import Sheaf.EtaleCohomology.Purity.Smooth.EtaleProjectionSectionNormalization
import Sheaf.EtaleCohomology.Purity.Smooth.EtaleProjectionStalkNormalization

/-! # Normalization of the étale projection comparison

Source: Stacks Project, Tag 0GKF.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped DirectSum TensorProduct

namespace AlgebraicGeometry.Etale

/-- The canonical, jointly natural projection isomorphism, with its section
formula and its normalized geometric-stalk square.
Source: Stacks, Tag 0GKF (blueprint: lem-pur-etale-sheaf-projection-map).

Proof: (1) Form the bilinear map on the defining sum presheaf using the unit
and graph restriction. Both operations are A-linear, so it is balanced.
Naturality of the unit and of graph restriction checks all restriction maps,
including lifts that merge after restriction. (2) Extend uniquely through module
sheafification using `lem-pc-sites-module-sheafification-bilinear-extension`,
then through the tensor universal property
`lem-pc-sites-sheaf-tensor-bilinear-universal`. Its unit equation is the section
formula below. (3) Uniqueness of these extensions gives joint naturality.
(4) `exists_etaleSumStalksIso`, `etale_stalk_tensor_unique`, and
`upperStarCompSheafFiberIso` compute the two vertical arrows.
The unit-germ calculation is the general-site calculation of
`lem-weil-pbc-inverse-image-stalk-germ`, applied to module-valued sheaves. The graph-restricted
unit has the original target germ, so the stalk map sends `ι m ⊗ n` to
`ι (m ⊗ n)`, giving exactly the displayed commuting square.
(5) Tensor distributes over arbitrary direct sums, with inverse defined on
individual summands. Thus every stalk map is invertible. (6) Geometric-stalk
conservativity makes the sheaf map invertible; its inverse is A-linear.
No flatness, torsion, or finiteness condition on either module is used. -/
theorem etaleLowerShriekProjectionMap (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] :
    ∃ p : ∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      etaleSheafTensor A T ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) N ≅
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj
          (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N)),
      (∀ (M M' : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
        (N N' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (f : M ⟶ M') (g : N ⟶ N'),
        etaleSheafTensorMap A
            ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).map f) g ≫
            (p M' N').hom =
          (p M N).hom ≫ (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).map
            (etaleSheafTensorMap A f ((upperStar (ModuleCat.{u + 1} A) e).map g))) ∧
      (∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
        (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale)
        (m : M.obj.obj (op W))
        (n : N.obj.obj
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))),
        (p M N).hom.hom.app
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
            (etaleSheafTensorSection A _ N
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
              (etaleSumSection A e M W m) n) =
          etaleSumSection A e _ W
            (etaleSheafTensorSection A M _ W m (etaleLiftSection A e N W n))) ∧
      (∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
        (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).map (p M N).hom ≫
            (etaleProjectionTargetStalkIso A e t M N).hom =
          (etaleProjectionSourceStalkIso A e t M N).hom ≫
            (etaleProjectionDirectSumTensorIso A e t M N).hom) := by
  classical
  let p := fun (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ↦
    (etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) (inferInstance : Etale e) M N).symm
  refine ⟨p, ?_, ?_, ?_⟩
  · intro M M' N N' f g
    dsimp [p, etaleSheafTensorMap]
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (etaleLowerShriekTensorIso_hom_naturality
      (ModuleCat.{u + 1} A) (inferInstance : Etale e) f g).symm
  · intro M N W m n
    exact etaleProjection_section_normalization A e M N W m n
  · intro M N Ω _ _ t
    exact etaleProjection_stalk_normalization A e M N (p M N).hom
      (etaleProjection_section_normalization A e M N) t

end AlgebraicGeometry.Etale
