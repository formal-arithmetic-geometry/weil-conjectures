/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
public import Sheaf.Paper.SectionLocalComparisonData
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.AffineTraceConstruction
public import Sheaf.AlgebraicGeometry.AffineTraceTower
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import Sheaf.AlgebraicGeometry.ShriekTensorComposition
public import Sheaf.Paper.CoordinateCounitArrows
public import Sheaf.SixFunctors.AffineDualizingCoefficient
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps
import Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation
import Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Tensor normalization of the ordered ordinary affine-space counit

Source: blueprint sec-smooth-purity/sk-prop-an/lem-amb-affine-space-top-trace.proof.md,
last paragraph, expanded coefficient normalization; Stacks Project, Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization).

The geometric model is the existing ordered coordinate tower, canonically isomorphic
to affine d-space. Reassociation is constructed from the normalized line comparisons;
no isomorphism is selected from the existential right-normal-form theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open OrdinaryAffineCounitTensorNormalization

/-- Tensor normalization of the actual ordered affine counit for every unbounded complex.
The isomorphism is constrained to have exactly the canonical projection as its hom;
its inverse is therefore the inverse specified in the node, not an arbitrary arrow.
Source: affine-space top trace proof, last paragraph; Stacks, Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization).

Proof:
1. The finite-coefficient proper projection and the derived open tensor comparison
are invertible on arbitrary unbounded inputs. Their specified compactification
composite gives the required projection isomorphism with its hom fixed.
2. Cancel that forward projection. The structural projection/reassociation equality
rewrites its composite with the inverse source and left-functor comparisons as the
ordered tensor action, right strength, and mapped right unitor.
3. The normalized projective-line counit has a coefficient-action square by the
associativity of the actual proper projection. Transporting the exact open adjunction
along its canonical right comparison gives its open counit square. Paste the two
squares and induct over the ordered coordinate tower to obtain the actual tower
counit's coefficient square.
4. Naturality of this counit at the right unitor, followed by the tower square,
moves the coefficient outside the counit. Functoriality identifies the remaining
composite with the unchanged definition of the unit trace.
5. This uses exactly the given ordered adjunction and comparisons, including their
identity stage. No truncation, generator choice, scalar division or determination
of arbitrary natural transformations from their unit values is used.
-/
theorem ordinaryAffineCounit_tensor_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    ∃ P : (((derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
          (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d))) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        (((derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower S d)).obj
          ((upperStar (ModuleCat.{u + 1} A)
            (affineTraceProjection S d)).mapDerivedCategory.obj K)).obj
          (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d)),
      P.hom = compactSupportProjectionMap A (affineTraceProjection S d)
        (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K ∧
      counit A N hN hA t D S hS d K = P.inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
          (trace A N hN hA t D S hS d) ≫ (derivedTensorSingleUnitIso K).hom := by
  have hp := isIso_projectionMap_of_finite A (affineTraceProjection S d)
  have hi : IsIso (compactSupportProjectionMap A (affineTraceProjection S d)
      (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K) := by
    unfold compactSupportProjectionMap compactSupportProjectionMapOfCompactification
    change IsIso (_ ≫ ((projectionMap (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).app _).app K ≫ _ ≫ _)
    infer_instance
  refine ⟨asIso (compactSupportProjectionMap A (affineTraceProjection S d)
    (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K),
    rfl, ?_⟩
  apply (cancel_epi (compactSupportProjectionMap A (affineTraceProjection S d)
    (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K)).mp
  simp only [asIso_inv, IsIso.hom_inv_id_assoc]
  unfold counit trace
  have hr := ordinaryAffine_projection_reassociation N hN A hA t S hS d K
  rw [reassoc_of% hr]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (affineTraceAdjunction A N hA t D S hS d).counit.naturality
    (derivedTensorSingleUnitIso K).hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have ht := ordinaryAffineTower_tensorCounit A N hA t D S hS d K
    (ordinaryFiniteUnit A S)
  erw [reassoc_of% ht]
  simp only [affineTraceCounit]
  rfl

end AlgebraicGeometry.Etale
