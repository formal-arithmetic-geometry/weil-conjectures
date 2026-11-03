/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteEtaleSpecializationCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteRankZeroNormalIntegration

/-! # Rank-zero section specialization and integration

Source: latest blueprint sec-smooth-purity/sk-prop-sp-orientation, second and third factors.
(blueprint: lem-pur-finite-etale-section-integration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- For a closed section of an etale map, normalized specialization agrees with
rank-zero bundle integration in the graph-normalized section coordinates.
There is no diagonal factor or supplied smooth orientation in this assertion.
Source: sk-prop-sp-orientation.proof.md, second and third displayed arrows;
lem-pur-finite-smooth-gamma-normalization, proof Steps 2 and 4--7.
(blueprint: lem-pur-finite-etale-section-integration).

Proof: substitute d=0. The section of the separated etale map is clopen. Its ideal
is zero on its image and the unit ideal on the complementary clopen subscheme.
Compute the extended Rees algebra on these two pieces: respectively O[t] and
O[t,t^-1]. The normal cone is therefore the base, with its projection and zero
section inverse to one another. The deformation projection is etale; its section
invariant is the constant coefficient unit in graph-normalized sum coordinates.
The actual exceptional fibre mates at one and zero become the canonical pullback
unit comparisons, by the exchange normalization and triangle identities. The
resulting constant-family comparison is normalized at one. Uniqueness in
FiniteRingSectionDeformation.existsUnique_normalized identifies it with kappa.
Thus specialization has identity coordinates from the section invariant to the
normal invariant. The conormal module has rank zero, so its symmetric algebra is
the structure algebra. On every bundle frame the zero-variable coordinate tower
has the identity adjunction, whose counit is the prescribed rank-zero trace.
Unique frame gluing identifies vectorBundleIntegration with that trace. Taking its
adjunct and restricting by the zero section identifies bundleSectionAdjoint with
the inverse coefficient-unit comparison. The cone/bundle isomorphism preserves
projection and zero section by coneBundleIso_spec and reesConeComparison_spec;
its exceptional mate in normalSectionMap therefore respects these same unit
coordinates. Compose the last two identifications and the zeroLineIso empty-tensor
identification. Both sides of the asserted equality now have identity coordinates.
All calculations are on clopen pieces and include empty pieces and the zero ring. -/
theorem finiteEtaleSectionIntegration
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g] [IsSeparated g] [Etale g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (d : ℕ) (hd : d = 0) [FiniteRingSectionDeformation.Geometry d g s]
    (hS : IsUnit (N : Γ(S, ⊤)))
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    (kappa : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (hKappa : NoetherianSectionSpecialization.Normalized A g s hs kappa)
    (sq : IsPullback
      (reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S)) :
    NoetherianSectionSpecialization.specialization A g s kappa =
      (finiteSmoothSectionCoordinates A C g s).hom ≫ (zeroLineIso A N hA S d hd).inv ≫
        FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA S hS d
          (ConormalGradedAlgebra.piece s 1) ≫ normalSectionMap A d g s hs sq := by
  subst d
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 0)
  have : SmoothOfRelativeDimension 0 (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 0)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : Etale (Scheme.Hom.normalConeProj g s) :=
    (Etale.iff_smoothOfRelativeDimension_zero _).mpr inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  apply (cancel_mono (finiteSmoothSectionCoordinates A C
    (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection).hom).mp
  rw [finiteEtaleSpecialization_coordinates A N hN hA g s hs hS C hC kappa hKappa]
  simp only [Category.assoc]
  rw [finiteRankZeroNormalIntegration_coordinates A N hN hA g s hs hS C hC sq]
  simp only [Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
