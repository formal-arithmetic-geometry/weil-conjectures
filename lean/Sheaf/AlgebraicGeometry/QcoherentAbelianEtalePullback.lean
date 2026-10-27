/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentZariskiCohomologyMap
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
import Sheaf.AlgebraicGeometry.QcoherentEtaleInverseImageSquare
import Sheaf.AlgebraicGeometry.QcoherentExactComparisonPullback

/-! # Change of site for abelian Zariski h-maps
Source: Stacks Project, Tags 01FD, 03AX, 03FD and 03P2.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
  moduleAbelianCohomologyLarge zariskiModuleHMap

/-- The normalized change-of-site comparisons intertwine the abelian h-maps.
This is the change-of-site part of the argument: both input and output on the
Zariski side are Ext of underlying abelian sheaves. It does not identify the
module-derived h-map with the abelian one or construct a coefficient morphism.

Source: Stacks Project, Cohomology, Tag 01FD; Etale Cohomology, Tag 03P2;
Cohomology on Sites, Tags 03AX and 03FD.
(blueprint: lem-pbc-abelian-etale-hmap-square).

Proof: Choose a finite affine open cover on X and a finite affine open cover on
Y refining its inverse image. Only the refined opens, not the inverse images,
are asserted affine. Separatedness makes all tuple intersections affine. The
ordinary and lifted associated etale sheaves are acyclic on these intersections,
so normalized Cech edges are invertible. For the abelian Zariski h-map and the
etale h-map, the refinement square identifies their cohomology maps with the
maps of alternating section complexes. Tensor restriction units identify
Zariski sections on an open with tensor sections on that open; the specified
component formula identifies the two section maps, and coordinatewise ULift.down
commutes with them. The section-normalized comparisons are morphisms of delta
functors. Quasi-coherent effacement and delta-functor uniqueness identify their
Cech versions with aX and aY. Cancel the invertible edges. Use the abelian
specialization of the resolved refinement square to identify the derived map
with exact inverse image followed by its adjoint coefficient map, namely
zariskiModuleHMap on the Zariski side and the displayed etale composite. This
includes zero coefficients and empty covers; arbitrary g need not be flat. -/
theorem normalizedAbelianEtale_hmap_square
    (X Y : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
    [CompactSpace Y] [Scheme.IsSeparated Y]
    (aX : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q)
    (aY : ∀ (G : Y.Modules) [G.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source Y G q ≃+ CoherentEtale.Target Y G q)
    (haX : IsNormalizedCoherentEtaleComparison X aX)
    (haY : IsNormalizedCoherentEtaleComparison Y aY)
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G)
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G))
    (hθ : ∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
      θ.hom.app (op U) (ULift.up s) = ULift.up
        (qcoherentPullbackSection g F G ψ U
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
          (pullback.fst U.hom g) pullback.condition s))
    (q : ℕ) (x : CoherentEtale.Source X F q) :
    aY G q (zariskiModuleHMap g
      ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ) q x) =
      Sheaf.H.map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
          (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
        q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q (aX F q x)) := by
  classical
  -- Replace the planned Cech route by the sheaf-level inverse-image square.
  -- Normalization identifies its exact-functor Ext maps with the supplied families.
  obtain ⟨D₁, D₂, τ, hb, hd⟩ := exists_coherentEtale_inverseImage_square g F G ψ θ hθ
  rw [D₂.eq_normalized aY haY G q _, D₁.eq_normalized aX haX F q x]
  exact exactComparison_hmap_square g F G
    ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ)
    θ D₁ D₂ τ hb hd q x

end
end AlgebraicGeometry.Scheme.Modules
