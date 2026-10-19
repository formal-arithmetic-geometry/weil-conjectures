# AlgebraicGeometry.Etale.etaleLowerShriekProjectionMap

## Reason

The section formula and the geometric-stalk computation are strictly smaller parts of the
argument, and each needs a separate statement module. Their fixed helper definitions must
be available below the parent theorem to avoid an import cycle. Move the eleven existing
helper definitions verbatim to EtaleSheafProjectionData, publicly imported by the original
module. This is organization for the mathematical decomposition, not a compile-time split.
No data, theorem signature, universe, visibility, hypothesis or comparison map changes.

## Old

In lean/Sheaf/EtaleCohomology/Purity/Smooth/EtaleSheafProjectionMap.lean:

```lean
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
```

## New

In lean/Sheaf/EtaleCohomology/Purity/Smooth/EtaleSheafProjectionData.lean, publicly
re-exported by the original module:

```lean
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
```

## Users

`tools/downstream.py Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap
--uses etaleSheafTensor` reports one downstream importer, `Sheaf.Paper.EtaleSumTensorTotalization`, and only
the item as a direct declaration user. The downstream importer does not reference any
relocated name; its imports retain the same public interface. A repository search for all helper names likewise finds only the original item.
All existing signatures and public imports remain available through the original module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap | Q4 | Publicly imports the unchanged definitions; theorem proved from the canonical comparison and two normalization lemmas. |
| Sheaf.Paper.EtaleSumTensorTotalization | unclaimed; unchanged | Existing import continues to re-export all original declarations; no signature or body adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionData | new, Q4 | Holds exactly the original eleven definitions. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleProjectionSectionNormalization | new, Q4 | States the canonical comparison's section equation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleProjectionStalkNormalization | new, Q4 | Proves the stalk calculation for any map with that section equation. |

No target statement or definition body is changed, so the targets retain exactly their
meanings. No other group's module is adapted.

## Status

landed 20261019T005403-L-2762538 2026-10-19 (merge of deliver/Q4/Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap)
