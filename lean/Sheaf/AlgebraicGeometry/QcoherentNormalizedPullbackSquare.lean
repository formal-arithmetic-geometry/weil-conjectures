/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.QcoherentPullbackSectionNaturality
import Sheaf.AlgebraicGeometry.QcoherentModuleAbelianFMap
import Sheaf.AlgebraicGeometry.QcoherentAbelianEtalePullback

/-! # The normalized cohomology refinement square

Source: Stacks Project, Tags 03P2, 03FD, 010S and 01FD.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj
  moduleAbelianCohomologyLarge zariskiModuleHMap
  moduleCohomologyFMap qcoherentPullbackSection etaleTensorSectionsRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def smallPullbackCoefficient {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) :
    etaleTensorSectionsPresheaf F ⟶
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).op ⋙
        etaleTensorSectionsPresheaf G where
  app U := qcoherentPullbackSection g F G ψ U.unop
    ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U.unop)
    (pullback.fst U.unop.hom g) pullback.condition
  naturality _ _ h := qcoherentPullbackSection_naturality g F G ψ h.unop


private theorem smallPullbackCoefficient_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) (U : X.Etale) :
    (smallPullbackCoefficient g F G ψ).app (op U) =
      qcoherentPullbackSection g F G ψ U
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
        (pullback.fst U.hom g) pullback.condition := rfl

attribute [local irreducible] smallPullbackCoefficient etaleTensorSectionsPresheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def liftSheafMap {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (B : C ⥤ D)
    [hB : B.IsContinuous J K] (P : Sheaf J AddCommGrpCat.{u})
    (Q : Sheaf K AddCommGrpCat.{u}) (f : P.obj ⟶ B.op ⋙ Q.obj) :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj P ⟶
      (B.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj
        ((sheafCompose K AddCommGrpCat.uliftFunctor.{u + 1, u}).obj Q) :=
  ⟨Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1, u} ≫
    (Functor.associator B.op Q.obj AddCommGrpCat.uliftFunctor.{u + 1, u}).hom⟩

private theorem liftSheafMap_app {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (B : C ⥤ D)
    [hB : B.IsContinuous J K] (P : Sheaf J AddCommGrpCat.{u})
    (Q : Sheaf K AddCommGrpCat.{u}) (f : P.obj ⟶ B.op ⋙ Q.obj)
    (U : Cᵒᵖ) (s : P.obj.obj U) :
    (liftSheafMap J K B P Q f).hom.app U (ULift.up s) = ULift.up (f.app U s) := rfl

attribute [local irreducible] liftSheafMap

private theorem smallEtaleContinuous {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).IsContinuous
      X.smallEtaleTopology Y.smallEtaleTopology := Etale.isContinuous_overPullback g

attribute [local instance] smallEtaleContinuous

private def pullbackCoefficient {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) :
    liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G) :=
  liftSheafMap X.smallEtaleTopology Y.smallEtaleTopology
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g)
    (hB := smallEtaleContinuous g) (etaleTensorSectionsSheaf F) (etaleTensorSectionsSheaf G)
    (smallPullbackCoefficient g F G ψ)

attribute [local semireducible] etaleTensorSectionsPresheaf

private theorem pullbackCoefficient_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)) :
    (pullbackCoefficient g F G ψ).hom.app (op U) (ULift.up s) = ULift.up
      (qcoherentPullbackSection g F G ψ U
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
        (pullback.fst U.hom g) pullback.condition s) := by
  have h := liftSheafMap_app X.smallEtaleTopology Y.smallEtaleTopology
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g)
    (hB := smallEtaleContinuous g) (etaleTensorSectionsSheaf F) (etaleTensorSectionsSheaf G)
    (smallPullbackCoefficient g F G ψ) (op U) s
  rw [smallPullbackCoefficient_app] at h
  exact h


attribute [local irreducible] pullbackCoefficient

private theorem combine_squares {A B C D E T : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup T]
    (eX : A ≃+ B) (eY : C ≃+ D) (cX : A ≃+ E) (cY : C ≃+ T)
    (m : A →+ C) (z : B →+ D) (t : E →+ T)
    (hm : ∀ y, eY (m y) = z (eX y))
    (hs : ∀ y, (eY.symm.trans cY) (z y) = t ((eX.symm.trans cX) y))
    (x : E) : cY.symm (t x) = m (cX.symm x) := by
  apply cY.injective
  rw [AddEquiv.apply_symm_apply]
  have h := hs (eX (cX.symm x))
  rw [← hm] at h
  simpa only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply] using h.symm


/-- The Cech comparison intertwines the two canonical cohomology maps.
The comparisons are given; this assertion supplies their pullback compatibility
and the coefficient sheaf morphism, not their existence.

Source: Stacks Project, Cohomology, Tag 01FD; Etale Cohomology, Tag 03P2;
Cohomology on Sites, Tags 03AX and 03FD.
(blueprint: lem-weil-pbc-qcoherent-normalized-pullback-square)

Proof: For each etale U over X, use structural tensor-section pullback to
U times_X Y, followed by the pullback of psi. These maps are additive. To
check restrictions, the two paths around a map of pullback squares are the
same composite structural pullback: use unit naturality and associativity
of the adjunction-mate composition isomorphisms, then coefficient naturality.
Apply ULift to the component maps; its functor law preserves naturality.
This constructs theta, and its evaluation is the displayed section formula.
Choose finite affine covers on X and Y, refining the inverse image of
X's cover by affine opens on Y. Separatedness makes all tuple intersections
affine. The inverse images before refinement need not be affine. Both ordinary
and lifted associated-etale coefficients are acyclic on these intersections,
so their normalized Cech edges are invertible. The maps on tuple sections for
the two covers are structural pullback followed by the pullback of psi.
The component formula just proved identifies theta with exactly this map.
Coordinatewise ULift.down intertwines the two Cech maps. Apply the
ringed-site Cech refinement square in the Zariski and etale sites. Its abelian
specialization computes the etale cohomology map as cohomologyMap followed by
the adjoint coefficient map, since set-valued etale inverse image is exact.
Its module specialization computes the Zariski map as moduleCohomologyFMap of
the tensor adjoint of psi. The normalized Cech comparisons agree with cX and
cY: they are morphisms of delta functors with the same section normalization,
and quasi-coherent cohomology is effaceable on these qcqs schemes. Cancel the
invertible Cech edges to get the stated equality. All transports use the
common-resolution moduleAbelianCohomologyLarge, whose normalized edge square
respects the connecting-class convention. Empty schemes and zero modules
produce zero complexes and are included. No flatness of g is required. -/
theorem qcoherentNormalizedComparison_pullback_square
    (X Y : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
    [CompactSpace Y] [Scheme.IsSeparated Y]
    (cX : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf F) q)
    (cY : ∀ (G : Y.Modules) [G.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj G) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf G) q)
    (hcX : IsNormalizedCoherentEtaleComparison X
      (fun F _ q ↦ (moduleAbelianCohomologyLarge X F q).symm.trans (cX F q)))
    (hcY : IsNormalizedCoherentEtaleComparison Y
      (fun G _ q ↦ (moduleAbelianCohomologyLarge Y G q).symm.trans (cY G q)))
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G) :
    ∃ θ : liftedCoherentEtaleSheaf F ⟶
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G),
      (∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection g F G ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
            (pullback.fst U.hom g) pullback.condition s)) ∧
      ∀ (q : ℕ) (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
        (cY G q).symm (Sheaf.H.map
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
            (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
          q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x)) =
        moduleCohomologyFMap g
          ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ)
          q ((cX F q).symm x) := by
  classical
  let θ := pullbackCoefficient g F G ψ
  have hθ := pullbackCoefficient_app g F G ψ
  refine ⟨θ, hθ, ?_⟩
  intro q x
  let φ := (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ
  exact combine_squares
    (moduleAbelianCohomologyLarge X F q) (moduleAbelianCohomologyLarge Y G q)
    (cX F q) (cY G q) (moduleCohomologyFMap g φ q).hom (zariskiModuleHMap g φ q)
    ((Sheaf.H.map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
        (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ) q).comp
      (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q))
    (moduleAbelianCohomologyLarge_hmap g F G φ q)
    (normalizedAbelianEtale_hmap_square X Y
      (fun F _ q ↦ (moduleAbelianCohomologyLarge X F q).symm.trans (cX F q))
      (fun G _ q ↦ (moduleAbelianCohomologyLarge Y G q).symm.trans (cY G q))
      hcX hcY g F G ψ θ hθ q) x

end
end AlgebraicGeometry.Scheme.Modules
