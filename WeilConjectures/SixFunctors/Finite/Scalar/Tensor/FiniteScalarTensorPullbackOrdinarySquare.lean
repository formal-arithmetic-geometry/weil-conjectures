/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackMateUnit
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackFixedPure
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealizationPure
import WeilConjectures.SixFunctors.Supporting.Tensor.ProEtaleTensorPairHomExt
import WeilConjectures.SixFunctors.Supporting.Tensor.ProEtaleTensorPairNaturality

/-! # The ordinary constant-scalar tensor pullback square

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sf-finite-scalar-tensor-pullback-ordinary-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat
attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.presheafToSheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
  AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage
  AlgebraicGeometry.ProEtale.lowerStar
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

private def fixedPair (T : Scheme.{u}) (R : Type u) [CommRing R]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) : (M ⊗ N).obj.obj W :=
  (Functor.LaxMonoidal.μ
    (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) M N).app W
      (m ⊗ₜ[ULift.{u + 1} R] n)

private theorem realizationUnit_map (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    {M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))}
    (f : M ⟶ N) (W : T.ProEtᵒᵖ) (m : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence T R).functor.map f).val.app W
        (sfIntrinsicRealizationUnit T R M W m) =
      sfIntrinsicRealizationUnit T R N W (f.hom.app W m) := by
  exact (congrArg (fun z ↦ z.app W m)
    ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R)).unit.naturality
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)).map
          f.hom))).symm

private theorem realizationUnit_surjective (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : T.ProEtᵒᵖ) : Function.Surjective (sfIntrinsicRealizationUnit T R M W) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T R)
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)
  have : IsIso (adj.unit.app (E.obj M.obj)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [adj, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) AddCommGrpCat.{u + 1})).obj M).property
  exact (ModuleCat.epi_iff_surjective ((adj.unit.app (E.obj M.obj)).app W)).mp inferInstance

private theorem realizationTensor_hom_ext (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R]
    {M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))}
    {H : proEtaleRingModules T (proEtaleConstantRing T R)}
    (a b : (sfIntrinsicModuleEquivalence T R).functor.obj (M ⊗ N) ⟶ H)
    (h : ∀ (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W),
      a.val.app W
          (sfIntrinsicRealizationUnit T R (M ⊗ N) W (fixedPair T R M N W m n)) =
        b.val.app W
          (sfIntrinsicRealizationUnit T R (M ⊗ N) W (fixedPair T R M N W m n))) : a = b := by
  let e := (finiteScalarOrdinaryTensorIso T R).app (M, N)
  apply (cancel_epi e.inv).mp
  apply proEtaleTensorPair_hom_ext T (proEtaleConstantRing T R)
  intro W x y
  obtain ⟨m, rfl⟩ := realizationUnit_surjective T R M W x
  obtain ⟨n, rfl⟩ := realizationUnit_surjective T R N W y
  have ht : e.hom.val.app W
      (sfIntrinsicRealizationUnit T R (M ⊗ N) W (fixedPair T R M N W m n)) =
      proEtaleTensorPair T (proEtaleConstantRing T R)
        ((sfIntrinsicModuleEquivalence T R).functor.obj M)
        ((sfIntrinsicModuleEquivalence T R).functor.obj N) W
        (sfIntrinsicRealizationUnit T R M W m) (sfIntrinsicRealizationUnit T R N W n) :=
    finiteScalarTensorRealization_pure T R M N W m n
  have he := congrArg (fun z ↦ z.val.app W
    (sfIntrinsicRealizationUnit T R (M ⊗ N) W (fixedPair T R M N W m n))) e.hom_inv_id
  change e.inv.val.app W (e.hom.val.app W _) = _ at he
  change e.inv.val.app W _ = _ at he
  change e.hom.val.app W _ = _ at ht
  rw [ht] at he
  change e.inv.val.app W _ =
    sfIntrinsicRealizationUnit T R (M ⊗ N) W (fixedPair T R M N W m n) at he
  change a.val.app W (e.inv.val.app W _) = b.val.app W (e.inv.val.app W _)
  exact (congrArg (a.val.app W) he).trans
    ((h W m n).trans (congrArg (b.val.app W) he).symm)

/-- The scalar realization's ordinary tensor comparison commutes with inverse image.
Source: Stacks, Sites and Sheaves, Tag 00YV; Modules on Sites, Tag 03EL.
(blueprint: lem-sf-finite-scalar-tensor-pullback-ordinary-square).

Proof: precompose both maps by the hom component of the scalar comparison at
M tensor N, an isomorphism. Their source is then intrinsic pullback, so transpose
both maps through the intrinsic pullback adjunction. The inverse mate defining the scalar
comparison is characterized by its adjunction-unit equation. Substitute that
unit equation and the scalar-unit normalization of sfIntrinsicDirectImageComparison.
The ordinary realization tensor comparison is built from the sheafification tensor
isomorphism, which sends the scalar-unit sections of m tensor n to the pair of
scalar-unit sections of m and n. The fixed-coefficient inverse-image tensorator
is the adjoint of tensoring the two inverse-image units. Thus both transposed maps
send every pure tensor m tensor n to the tensor of the two intrinsic inverse-image
unit sections. The characterizing pure-unit equation of
proEtaleOrdinaryTensorPullback gives the same image for the right composite.
The sectionwise tensor universal property followed by the sheafification adjunction
proves equality. This uses only adjunctions and tensor universal properties, so also
covers the zero ring and empty schemes. No complexes or totalization occur here. -/
theorem finiteScalarTensorPullback_ordinary_square
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :
    (sfIntrinsicModuleEquivalence X R).functor.map
        (Functor.OplaxMonoidal.δ
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) M N) ≫
      (finiteScalarOrdinaryTensorIso X R).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M,
         (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj N) ≫
      (uncurry.obj (proEtaleOrdinaryTensor X (proEtaleConstantRing X R))).map
        (Prod.mkHom ((finiteScalarOrdinaryPullbackComparison R p).inv.app M)
          ((finiteScalarOrdinaryPullbackComparison R p).inv.app N)) =
    (finiteScalarOrdinaryPullbackComparison R p).inv.app (M ⊗ N) ≫
      (proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).map
        ((finiteScalarOrdinaryTensorIso Y R).hom.app (M, N)) ≫
      (proEtaleOrdinaryTensorPullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
        ((sfIntrinsicModuleEquivalence Y R).functor.obj M)
        ((sfIntrinsicModuleEquivalence Y R).functor.obj N)).hom := by
  let A := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let F := (sfIntrinsicModuleEquivalence X R).functor
  let G := (sfIntrinsicModuleEquivalence Y R).functor
  let B := proEtaleRingModulePullback p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let b := proEtaleRingModuleAdjunction p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let c := finiteScalarOrdinaryPullbackComparison R p
  let tX := (finiteScalarOrdinaryTensorIso X R).hom.app (A.obj M, A.obj N)
  let tY := (finiteScalarOrdinaryTensorIso Y R).hom.app (M, N)
  let δ := Functor.OplaxMonoidal.δ A M N
  let μ := (proEtaleOrdinaryTensorPullback p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R) (G.obj M) (G.obj N)).hom
  let T := uncurry.obj (proEtaleOrdinaryTensor X (proEtaleConstantRing X R))
  have h : c.hom.app (M ⊗ N) ≫ F.map δ ≫ tX =
      B.map tY ≫ μ ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) := by
    apply (b.homEquiv _ _).injective
    apply realizationTensor_hom_ext Y R
    intro W m n
    let V := (proEtaleBaseChange p).op.obj W
    let a := ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
    let m' := (a.unit.app M).hom.app W m
    let n' := (a.unit.app N).hom.app W n
    have hleft : tX.val.app V
        ((F.map δ).val.app V ((c.hom.app (M ⊗ N)).val.app V
          ((b.unit.app (G.obj (M ⊗ N))).val.app W
            (sfIntrinsicRealizationUnit Y R (M ⊗ N) W (fixedPair Y R M N W m n))))) =
        proEtaleTensorPair X (proEtaleConstantRing X R)
          (F.obj (A.obj M)) (F.obj (A.obj N)) V
          (sfIntrinsicRealizationUnit X R (A.obj M) V m')
          (sfIntrinsicRealizationUnit X R (A.obj N) V n') := by
      rw [finiteScalarTensorPullback_mate_unit R p (M ⊗ N) W]
      erw [realizationUnit_map X R δ V]
      erw [finiteScalarTensorPullback_fixed_pure R p M N W m n]
      exact finiteScalarTensorRealization_pure X R (A.obj M) (A.obj N) V m' n'
    have hn := congrArg (fun z ↦ z.val.app W
      (sfIntrinsicRealizationUnit Y R (M ⊗ N) W (fixedPair Y R M N W m n)))
      (b.unit.naturality tY)
    change (b.unit.app _).val.app W (tY.val.app W _) =
      (B.map tY).val.app V ((b.unit.app _).val.app W _) at hn
    have ht : tY.val.app W
        (sfIntrinsicRealizationUnit Y R (M ⊗ N) W (fixedPair Y R M N W m n)) =
        proEtaleTensorPair Y (proEtaleConstantRing Y R) (G.obj M) (G.obj N) W
          (sfIntrinsicRealizationUnit Y R M W m)
          (sfIntrinsicRealizationUnit Y R N W n) :=
      finiteScalarTensorRealization_pure Y R M N W m n
    have hp := (Classical.choose_spec
      (proEtaleOrdinaryTensorPullback_existsUnique p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).exists).2
          (G.obj M) (G.obj N) W.unop
          (sfIntrinsicRealizationUnit Y R M W m)
          (sfIntrinsicRealizationUnit Y R N W n)
    have hright : (T.map (Prod.mkHom (c.hom.app M) (c.hom.app N))).val.app V
        (μ.val.app V ((B.map tY).val.app V
          ((b.unit.app (G.obj (M ⊗ N))).val.app W
            (sfIntrinsicRealizationUnit Y R (M ⊗ N) W (fixedPair Y R M N W m n))))) =
        proEtaleTensorPair X (proEtaleConstantRing X R)
          (F.obj (A.obj M)) (F.obj (A.obj N)) V
          (sfIntrinsicRealizationUnit X R (A.obj M) V m')
          (sfIntrinsicRealizationUnit X R (A.obj N) V n') := by
      have hn' := congrArg (fun z ↦
        (T.map (Prod.mkHom (c.hom.app M) (c.hom.app N))).val.app V
          (μ.val.app V z)) hn.symm
      refine hn'.trans ?_
      erw [ht]
      change (T.map (Prod.mkHom (c.hom.app M) (c.hom.app N))).val.app V
        (μ.val.app V ((b.unit.app _).val.app W
          (proEtaleTensorPair Y (proEtaleConstantRing Y R) (G.obj M) (G.obj N) W
            (sfIntrinsicRealizationUnit Y R M W m)
            (sfIntrinsicRealizationUnit Y R N W n)))) = _
      have hp' : μ.val.app V ((b.unit.app _).val.app W
          (proEtaleTensorPair Y (proEtaleConstantRing Y R) (G.obj M) (G.obj N) W
            (sfIntrinsicRealizationUnit Y R M W m)
            (sfIntrinsicRealizationUnit Y R N W n))) =
          proEtaleTensorPair X (proEtaleConstantRing X R)
            (B.obj (G.obj M)) (B.obj (G.obj N)) V
            ((b.unit.app (G.obj M)).val.app W (sfIntrinsicRealizationUnit Y R M W m))
            ((b.unit.app (G.obj N)).val.app W (sfIntrinsicRealizationUnit Y R N W n)) := by
        simp only [μ, V, b, B]
        delta proEtaleOrdinaryTensorPullback
        simpa only [Functor.op_obj, Opposite.op_unop] using hp
      rw [hp']
      have hT : T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) =
          c.hom.app M ⊗ₘ c.hom.app N := (tensorHom_def _ _).symm
      erw [hT]
      erw [proEtaleTensorPair_natural X (proEtaleConstantRing X R)
        (c.hom.app M) (c.hom.app N) V]
      erw [finiteScalarTensorPullback_mate_unit R p M W m,
        finiteScalarTensorPullback_mate_unit R p N W n]
      rfl
    exact hleft.trans hright.symm
  have : IsIso (Prod.mkHom (c.hom.app M) (c.hom.app N)) :=
    inferInstanceAs (IsIso ((c.app M).prod (c.app N)).hom)
  apply (cancel_mono (T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)))).mp
  apply (cancel_epi (c.hom.app (M ⊗ N))).mp
  change c.hom.app (M ⊗ N) ≫ (F.map δ ≫ tX ≫
      T.map (Prod.mkHom (c.inv.app M) (c.inv.app N))) ≫
        T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) =
    c.hom.app (M ⊗ N) ≫ (c.inv.app (M ⊗ N) ≫ B.map tY ≫ μ) ≫
      T.map (Prod.mkHom (c.hom.app M) (c.hom.app N))
  simp only [Category.assoc, ← T.map_comp, prod_comp,
    Iso.inv_hom_id_app, ← prod_id, Iso.hom_inv_id_app_assoc]
  erw [T.map_id, Category.comp_id]
  exact h

end WeilConjectures
