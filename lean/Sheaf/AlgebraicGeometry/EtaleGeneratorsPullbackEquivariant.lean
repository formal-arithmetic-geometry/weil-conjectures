/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleIsoTorsor
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackUnitMap
import Sheaf.AlgebraicGeometry.EtaleInverseImageJointRepresentatives
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Pulling back the torsor of generators

Source: Stacks Project, Tag 040E, pullback of local generators, and Tag 03AH.
(blueprint: lem-sc-etale-generators-pullback-equivariant)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of generators gives an equivariant map from the inverse-image torsor
into the generator torsor of the tensor pullback.

Source: Stacks Project, Tag 040E, functoriality of the Isom torsor; Tag 03AH.
(blueprint: lem-sc-etale-generators-pullback-equivariant)

Proof: On a trivializing open U, a generator s of L gives the generator 1 tensor s
of the tensor pullback. On an etale object over U, use the pullback of this
trivialization and the composition isomorphism for module pullback. This construction
commutes with restrictions and hence defines a morphism out of the sheafified set
inverse image. Transport this morphism through eT. For each local unit a,
1 tensor (a s) = c_f(a) (1 tensor s). The assumed compatibility of eT with the
pulled-back action gives equivariance on the images of the adjunction units. Every
section of the sheafified inverse image is locally represented by such an image,
and the action is likewise locally represented by pulled-back group sections.
The equivariance identity therefore holds locally and then globally by the sheaf axiom.
The construction is independent of the trivializing cover since its maps agree on
intersections, by compatibility with restrictions. -/
theorem etale_generators_pullback_equivariant
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)]
    (T' : Sheaf.Torsor ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj X.gmSheaf))
    (eT : (Scheme.etaleSetPullback f).obj (etaleIsoTorsor L).sheaf ≅ T'.sheaf)
    (heT : ∀ (W : X.Etale) (g : X.gmSheaf.obj.obj (op W))
        (t : (etaleIsoTorsor L).sheaf.obj.obj (op W)),
          eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (Y.smallGrothendieckTopology @Etale)).unit.app
                  (etaleIsoTorsor L).sheaf).hom.app (op W)
                ((etaleIsoTorsor L).vadd (op W) g t)) =
          T'.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
                X.gmSheaf).hom.app
              (op W) g)
            (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
                (X.smallGrothendieckTopology @Etale)
                (Y.smallGrothendieckTopology @Etale)).unit.app
                  (etaleIsoTorsor L).sheaf).hom.app (op W) t))) :
    ∃ σ : T'.sheaf ⟶ (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf,
      ∀ (U : Y.Etaleᵒᵖ)
        (a : ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj X.gmSheaf).obj.obj U)
        (t : T'.sheaf.obj.obj U),
        σ.hom.app U (T'.vadd U a t) =
          (etaleIsoTorsor ((tensorPullback f).obj L)).vadd U
            ((upperStarGmSheafToGmSheaf f).hom.app U a) (σ.hom.app U t) := by
  obtain ⟨ρ, hρ⟩ := exists_etale_generators_pullback_unit_map f L
  let σ := eT.inv ≫ ρ
  refine ⟨σ, ?_⟩
  intro U a t
  obtain ⟨R, hR, hrep⟩ := etaleInverseImage_joint_representatives f X.gmSheaf
    (etaleIsoTorsor L).sheaf U a (eT.inv.hom.app U t)
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp
    (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf.property _ hR).isSeparatedFor.ext
  intro V i hi
  obtain ⟨W, k, g, s, ha, ht⟩ := hrep V i hi
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)).unit.app (etaleIsoTorsor L).sheaf
  let ηG := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
    X.gmSheaf
  let Q := etaleIsoTorsor ((tensorPullback f).obj L)
  have hcancel (Z : Y.Etaleᵒᵖ) (x : T'.sheaf.obj.obj Z) :
      eT.hom.hom.app Z (eT.inv.hom.app Z x) = x := by
    exact congrArg (fun q ↦ q.hom.app Z x) eT.inv_hom_id
  have hcancel' (Z : Y.Etaleᵒᵖ)
      (x : ((Scheme.etaleSetPullback f).obj (etaleIsoTorsor L).sheaf).obj.obj Z) :
      eT.inv.hom.app Z (eT.hom.hom.app Z x) = x := by
    exact congrArg (fun q ↦ q.hom.app Z x) eT.hom_inv_id
  have ht' : T'.sheaf.obj.map i.op t =
      T'.sheaf.obj.map k.op (eT.hom.hom.app (op (b.obj W))
        (η.hom.app (op W) s)) := by
    have h := congrArg (eT.hom.hom.app (op V)) ht
    rw [NatTrans.naturality_apply eT.hom.hom i.op,
      NatTrans.naturality_apply eT.hom.hom k.op, hcancel] at h
    exact h
  have hunit : σ.hom.app (op (b.obj W))
      (T'.vadd (op (b.obj W)) (ηG.hom.app (op W) g)
        (eT.hom.hom.app (op (b.obj W)) (η.hom.app (op W) s))) =
      Q.vadd (op (b.obj W))
        ((upperStarGmSheafToGmSheaf f).hom.app (op (b.obj W))
          (ηG.hom.app (op W) g))
        (σ.hom.app (op (b.obj W))
          (eT.hom.hom.app (op (b.obj W)) (η.hom.app (op W) s))) := by
    change ρ.hom.app _ (eT.inv.hom.app _ _) =
      Q.vadd _ _ (ρ.hom.app _ (eT.inv.hom.app _ _))
    rw [← heT W g s, hcancel', hcancel']
    exact hρ W g s
  rw [← NatTrans.naturality_apply σ.hom i.op, T'.map_vadd i.op,
    Q.map_vadd i.op, ← NatTrans.naturality_apply
      (upperStarGmSheafToGmSheaf f).hom i.op,
    ← NatTrans.naturality_apply σ.hom i.op, ha, ht',
    ← T'.map_vadd k.op, NatTrans.naturality_apply σ.hom k.op,
    hunit, Q.map_vadd k.op,
    ← NatTrans.naturality_apply (upperStarGmSheafToGmSheaf f).hom k.op,
    ← NatTrans.naturality_apply σ.hom k.op]

end AlgebraicGeometry.Scheme.Modules
