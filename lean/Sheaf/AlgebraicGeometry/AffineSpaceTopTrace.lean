/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q24, G1
-/
module

public import Sheaf.AlgebraicGeometry.AffineTraceConstruction

import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.AffineTraceLinePurity
import Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange
import Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm

/-!
# The affine-space top trace
Source: blueprint sk-prop-an, Steps 5(b) and 6
(blueprint: lem-amb-affine-space-top-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The counit is invertible along the entire ordered coordinate tower.
Source: blueprint affine-space top trace, step 7
(blueprint: lem-amb-affine-space-top-trace). -/
private theorem towerCounit_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    IsIso ((affineTraceAdjunction A N hA t D S hS d).counit.app K) := by
  unfold affineTraceAdjunction
  apply affineTraceAdjunctionTower_counit_isIso
  intro e M
  let := affineTraceNoetherian S e
  exact affineTraceLineCounit_isIso A N hN hA t (affineTraceTower S e)
    (affineTraceInvertible N S hS e) (D _ _) M

/-- The affine-space trace is the actual composite counit, is invertible, and obeys
arbitrary Noetherian base change. The exchange is the pasted compact-support exchange;
the right-object comparison is the normalized Tate pullback comparison above.
Source: blueprint sk-prop-an, Steps 5(b), 6, detailed affine-space top trace lemma
(blueprint: lem-amb-affine-space-top-trace).

Proof: use the normalized projective-line adjunction and its base-change datum.
Push the open-closed triangle to the base and use the projective decomposition.
Only the first restriction component needs to be identity: a triangular coordinate
change makes restriction first projection while preserving trace as second projection.
A morphism to the split distinguished triangle makes the composite line counit
invertible. Induct along the ordered adjunction tower from the identity at dimension
zero. The separately proved tensor, shift and inverse-image induction supplies the
right-functor Tate normal form and boundedness at the constant input.
For base change, naturality of the open counit pastes its exchange square with the
normalized projective-line counit square. Induct through the coordinate tower, then
apply counit naturality to the canonical constant-coefficient pullback comparison.
Every map is the actual specified adjunction counit or canonical comparison.
-/
theorem exists_affineSpaceTopTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum A N hA t T hT),
      OrdinaryFiniteP1BaseChange A N hA t D ∧
      ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ),
        Nonempty (affineTraceRight A N hA S d ≅
          ordinaryFinitePullback A (affineTraceProjection S d) ⋙
            derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S d)
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                (Scheme.finiteEtaleTateSheaf A N (affineTraceTower S d) hA (d : ℤ))) ⋙
            shiftFunctor _ (2 * (d : ℤ))) ∧
        _root_.DerivedCategory.TStructure.t.plus
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ∧
        IsIso (affineTraceCounit A N hA t D S hS d) ∧
        ∀ (S' : Scheme.{u}) [IsNoetherian S'] (g : S' ⟶ S),
          affineTraceExchange A g d
              ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
            (affineTraceLeft A S' d).map
              ((affineTraceRightBaseChange A N hA t g hS d
                (ordinaryFiniteUnit A S)).hom ≫
                (affineTraceRight A N hA S' d).map (ordinaryFiniteUnitPullback A g).hom) ≫
            affineTraceCounit A N hA t D S' (affineTracePullbackInvertible N g hS) d =
          (ordinaryFinitePullback A g).map (affineTraceCounit A N hA t D S hS d) ≫
            (ordinaryFiniteUnitPullback A g).hom := by
  obtain ⟨t, D, hD⟩ := exists_ordinaryFiniteP1Adjunction N hN A hA
  refine ⟨t, D, hD, ?_⟩
  intro S _ hS d
  obtain ⟨e, hb⟩ := affineTraceRight_normalForm A N hN hA S hS d
  refine ⟨e, hb, towerCounit_isIso A N hN hA t D S hS d _, ?_⟩
  intro S' _ g
  have h := affineTraceTowerCounit_baseChange A N hN hA t D hD g hS d (ordinaryFiniteUnit A S)
  have hn := (affineTraceAdjunction A N hA t D S'
    (affineTracePullbackInvertible N g hS) d).counit.naturality
      (ordinaryFiniteUnitPullback A g).hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  dsimp only [affineTraceCounit]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [affineTraceCounit, Category.assoc] using
    congrArg (fun f ↦ f ≫ (ordinaryFiniteUnitPullback A g).hom) h

end AlgebraicGeometry.Etale
