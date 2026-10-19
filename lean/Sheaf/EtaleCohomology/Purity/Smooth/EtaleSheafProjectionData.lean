/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSumStalks
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import Sheaf.CategoryTheory.SheafTensorStructure
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The canonical projection map for étale sum extension

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF, and Étale Cohomology,
Tag 03S5 (blueprint: lem-pur-etale-sheaf-projection-map).
The section equation uses the actual Kan-extension and sheafification units and
the inverse-image unit followed by restriction to the graph. The geometric-stalk
square uses the germ-normalized sum comparison, the tensorator μ, and the
canonical inverse-image stalk comparison, rather than unspecified object isomorphisms.
The direct-sum tensor comparison is the canonical finite-support map, so the statement
also covers empty lift fibres and zero coefficient modules without extra hypotheses.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped DirectSum TensorProduct

namespace AlgebraicGeometry.Etale

/-- The tensor product on sheaves of `A`-modules over a small étale site.
Source: Stacks Project, `sites-modules.tex`, Section 03EK
(blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleSheafTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  @MonoidalCategoryStruct.tensorObj _ _
    (Etale.sheafMonoidalCategory (ModuleCat.{u + 1} A) X).toMonoidalCategoryStruct M N

/-- The map on sheaf tensors induced by two morphisms.
Source: Stacks Project, `sites-modules.tex`, Section 03EK
(blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleSheafTensorMap (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}}
    {M M' N N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : M ⟶ M') (g : N ⟶ N') :
    etaleSheafTensor A X M N ⟶ etaleSheafTensor A X M' N' := by
  letI : MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    Etale.sheafMonoidalCategory (ModuleCat.{u + 1} A) X
  exact tensorHom f g

/-- The canonical local tensor, obtained from the lax tensorator of the inclusion
of sheaves into presheaves.
Source: Stacks Project, Section 03EK (blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleSheafTensorSection (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (W : X.Etale) (m : M.obj.obj (op W)) (n : N.obj.obj (op W)) :
    (etaleSheafTensor A X M N).obj.obj (op W) :=
  letI := (sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
  (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} A)) M N).app (op W) (m ⊗ₜ[A] n)

/-- Insert the section in its lift summand, then sheafify. A test object on the
source is precisely a test object on the target together with a lift through `e`.
Source: Stacks, Tags 03S5 and 0GKF (blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleSumSection (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale)
    (m : M.obj.obj (op W)) :
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) :=
  (toSheafify T.smallEtaleTopology
    ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op.lan.obj M.obj)).app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
    (((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op.lanUnit.app M.obj).app
      (op W) m)

/-- Pull a section back by the unit and restrict along the graph of the lift.
The graph is the unit of the composition/base-change adjunction on étale objects.
Source: Stacks, Tags 0GKF and 03Q1 (blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleLiftSection (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale)
    (n : N.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) :
    ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj.obj (op W) :=
  ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj.map
    (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
      (inferInstance : Etale e) trivial).unit.app W).op)
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app N).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) n)

/-- The germ-normalized sum-stalk isomorphism supplied by `exists_etaleSumStalksIso`.
Its germ formula fixes every summand generator and hence uniquely determines the
linear equivalence; choosing this witness postpones only its proof, not any data.
Source: Stacks, Tag 03S5 (blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleProjectionSumStalkIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≅
      ModuleCat.of A (⨁ v : Over.mk t ⟶ Over.mk e,
        ((Scheme.pointSmallEtale v.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj M) :=
  ((exists_etaleSumStalksIso e A Ω t).choose M).toModuleIso

/-- The tensor-stalk isomorphism: inverse of the μ characterized in
`Scheme.etale_stalk_tensor_unique`, transported by the canonical universe-lift
isomorphism of points. Source: Stacks, Tags 007K, 03EL and 0GKF
(blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleProjectionTensorStalkIso (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T)
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        (etaleSheafTensor A T M N) ≅
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj M ⊗
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj N :=
  ((Scheme.pointSmallEtale t).uliftSheafFiberIso (ModuleCat.{u + 1} A)).symm.app _ ≪≫
    sheafFiberTensorIso t M N ≪≫
      tensorIso
        (((Scheme.pointSmallEtale t).uliftSheafFiberIso (ModuleCat.{u + 1} A)).app M)
        (((Scheme.pointSmallEtale t).uliftSheafFiberIso (ModuleCat.{u + 1} A)).app N)

/-- The inverse-image stalk comparison at a lift, including transport along its
triangle equation. It is the module-valued form of the canonical comparison underlying
`inverseImage_stalk_germ`.
Source: Stacks, Tag 03Q1 (blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleProjectionLiftStalkIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (v : Over.mk t ⟶ Over.mk e)
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((Scheme.pointSmallEtale v.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        ((upperStar (ModuleCat.{u + 1} A) e).obj N) ≅
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj N :=
  (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e v.left).app N ≪≫
    eqToIso (congrArg (fun z ↦
      ((Scheme.pointSmallEtale z).sheafFiber (A := ModuleCat.{u + 1} A)).obj N) v.w)

/-- The left vertical arrow of the projection stalk square. In particular its
codomain is `(⊕ M_v) ⊗ N_t`, including the second tensor factor.
Source: Stacks, Tag 0GKF (blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleProjectionSourceStalkIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  etaleProjectionTensorStalkIso A t
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) N ≪≫
    tensorIso (etaleProjectionSumStalkIso A e t M) (Iso.refl _)

/-- The right vertical arrow: sum comparison, then tensor-stalk and inverse-image
comparisons on each summand. Source: Stacks, Tag 0GKF
(blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleProjectionTargetStalkIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  etaleProjectionSumStalkIso A e t
      (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N)) ≪≫
    (DirectSum.congrLinearEquiv (fun v : Over.mk t ⟶ Over.mk e ↦
      (etaleProjectionTensorStalkIso A v.left M
          ((upperStar (ModuleCat.{u + 1} A) e).obj N) ≪≫
        tensorIso (Iso.refl _) (etaleProjectionLiftStalkIso A e t v N)).toLinearEquiv)).toModuleIso

/-- The lower arrow, `ι_v m ⊗ n ↦ ι_v (m ⊗ n)`, with its genuine tensor-distribution
inverse. Source: Stacks, Tag 0GKF (blueprint: lem-pur-etale-sheaf-projection-map). -/
noncomputable def etaleProjectionDirectSumTensorIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ModuleCat.of A (⨁ v : Over.mk t ⟶ Over.mk e,
      ((Scheme.pointSmallEtale v.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj M) ⊗
        ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj N ≅
      ModuleCat.of A (⨁ v : Over.mk t ⟶ Over.mk e,
        TensorProduct A
          (((Scheme.pointSmallEtale v.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj M)
          (((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj N)) := by
  classical
  exact (TensorProduct.directSumLeft A A
    (fun v : Over.mk t ⟶ Over.mk e ↦
      ((Scheme.pointSmallEtale v.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj M)
    (((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj N)).toModuleIso

end AlgebraicGeometry.Etale
