/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.CoordinateCounitArrows
public import Sheaf.Paper.SectionCentredChartData
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.SectionReesBaseChangeEtale
import Sheaf.Paper.SectionExceptionalFibreCoherence

/-! # Counit normalization in section deformation coordinates

Source: main-20261015, sk-thm-dnc, Local construction, standard model;
orientation-charts Step 3 (blueprint: lem-trf-section-coordinate-counit-normalization).

All orientations are fixed by the ordered coordinate-tower counit. The local comparison
is formed from the actual source and family chart maps before asserting normalization.
The affine open is retained as a map to the original base, and its fibre comparison is
restriction of the original family's actual exceptional mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open SectionComparisonArrows SectionLocalDualizingComparisons

/-- The adjoint of the actual ordered tower counit is an isomorphism and commutes
with every Noetherian change of base, using the canonical Tate comparison.
Source: sk-thm-dnc, Local construction, standard affine model
(blueprint: lem-trf-section-coordinate-counit-normalization).

Proof: Step 1 identifies the ordered composite left adjoint with ordinary unbounded
compact supports by lem-amb-unbounded-compact-support-comparisons. Uniqueness of right
adjoints (det-sp-unique-right-adjoint) identifies its right adjoint with p^times, and
identifies the counit transpose with affineAdjoint. Thus it is invertible. In Step 2,
transpose pullback(alpha) followed by the actual exceptional mate. The defining mate
identity, naturality of compact-support exchange, and the counit identity reduce its
transpose to pullback(t_p) through inverse exchange. The arbitrary-base-change equality
of lem-amb-affine-space-top-trace identifies this with t_p'. Injectivity of the
adjunction bijection gives the equality, with the Tate comparison of
lem-asd-etale-finite-twist-pullback. The identity tower handles d=0.
-/
theorem affineCoordinateCounit_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    IsIso (CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d) ∧
    ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ S),
      (ordinaryFinitePullback A (affineTraceMap v d)).map
          (CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d) ≫
        dualizingComplexBaseChangeMap A (affineTraceMap_isPullback v d) =
      (affineTraceRightBaseChange A N hA t v hS d (ordinaryFiniteUnit A S)).hom ≫
        (affineTraceRight A N hA T d).map (ordinaryFiniteUnitPullback A v).hom ≫
        CoordinateCounitArrows.towerAdjoint N hN A hA t D T
          (affineTracePullbackInvertible N v hS) d := by
  sorry

/-- The affine adjunction can be presented with exactly the specified tower counit.
This supplies the presentation data used below rather than assuming extra orientations.
Source: sk-thm-dnc, Local construction, affine-space adjunction
(blueprint: lem-trf-section-coordinate-counit-normalization).

Proof: Step 1 transports the composite coordinate-tower adjunction across the unbounded
compact-support comparison and the coordinate isomorphism. Regroup the Tate powers by
the pure-tensor comparisons and move the even shifts. Uniqueness of right adjoints
identifies its inverse dualizing isomorphism with the transpose of its counit. This is
precisely standardAdjoint by its definition. At d=0 all tower adjunctions are identities.
-/
theorem exists_coordinateCounitAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∃ adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣ affineRight A N hA S d,
      CoordinateCounitArrows.IsNormalized N hN A hA t D S hS d adj := by
  sorry

/-- On the standard affine pair the two counit orientations have actual fibre value theta.
Written in their Tate coordinates this says theta is identity. No normalized deformation
comparison is assumed.
Source: sk-thm-dnc, standard model; orientation-charts Step 3
(blueprint: lem-trf-section-coordinate-counit-normalization).

Proof: Step 1 supplies the two counit-normalized affine adjunctions. Step 2 transposes
pullback of alpha followed by the exceptional mate: naturality of compact-support exchange
and the counit identity reduce it to pullback of the specified trace. Trace base change
identifies it with the new trace. Injectivity of adjunction gives the equality. Step 3
uses the base change i1 over X=A1_S and restricts to zero. In the Rees coordinates
x_j=t*u_j, at one x_j=u_j, giving theta i1*oF=oC. Cancelling oF gives the displayed
restriction of rawComparison. The inverse-image section compositor and canonical Tate
pullback are those of restrictionAtOne and affineSectionIso. The zero tower gives d=0.
-/
theorem sectionCoordinateCounit_standard (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∃ (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣ affineRight A N hA S d)
      (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _) ⊣
          affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) S) d),
      CoordinateCounitArrows.IsNormalized N hN A hA t D S hS d adjC ∧
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D
        (AffineSpace (ULift.{u} (Fin 1)) S)
        (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d adjF ∧
      (restrictionAtOne A S
        (rawComparison A N hN hA S hS d _ _
          (affineSectionIso A N hN hA S hS d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) adjC)
          (@affineSectionIso A _ _ N hN hA (AffineSpace (ULift.{u} (Fin 1)) S)
            (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
            (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF))).hom =
        sectionMap A
          (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace.map (ULift.{u} (Fin d))
            (AffineSpace.oneSection (ULift.{u} (Fin 1)) S))
          (AffineSpace.isPullback_map _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
          (AffineSpace.zeroSection_comp_map _) := by
  sorry

/-- For an affine centred chart over T open in the original base S, the actual two
local orientations are invertible and their raw comparison restricts to theta|T.
The equivalent discrepancy is literally the identity of C|T.
Source: sk-thm-dnc, Local construction; orientation-charts Step 3
(blueprint: lem-trf-section-coordinate-counit-normalization).

Proof: Step 1 supplies the two affine adjunctions with their specified counits. Steps 2
and 3 give the standard normalization by transposing base change of the trace and then
restricting to zero at one. Step 4 uses Chart.reesCoordinates and Chart.reesOpen, the
actual extended-Rees maps; the former has coordinates x_j=t*u_j. chartGeometry supplies
the finite-type Noetherian locality domains. Step 5 applies exceptional fibre coherence
to both maps: theta_U i1*bF^e=bC^e theta_0 and theta_U i1*bF^j=bC^j theta_T. The base
square identifies theta_T with restrictedTheta, including the original atOne over S.
Step 6 forms exactly rawComparison from localFamilyMap and localSourceMap; cancellation
of these two squares gives restrictionAtOne=restrictedTheta. Their invertibility supplies
the displayed isomorphisms and theta. Composing with theta inverse gives discrepancy=refl.
The construction assumes no independently chosen orientation or normalized comparison.
-/
theorem sectionCoordinateCounit_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (c : Chart d g s hs) :
    ∃ (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T) ⊣ affineRight A N hA c.T d)
      (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) ↘ _) ⊣
          affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) c.T) d),
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D c.T
        (chartGeometry d g s hs c).noethT
        (invertibleOnSource N c.b hS) d adjC ∧
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D
        (AffineSpace (ULift.{u} (Fin 1)) c.T)
        (chartGeometry d g s hs c).noethLine
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
          (invertibleOnSource N c.b hS)) d adjF ∧
      ∃ (oC : (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj
          (sectionInvariant A g s) ≅ SectionLocalDualizingComparisons.tateObject A N hA c.T d)
        (oF : (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj (family A g s) ≅
            SectionLocalDualizingComparisons.tateObject A N hA
              (AffineSpace (ULift.{u} (Fin 1)) c.T) d)
        (theta : (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A)
              (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj
                (family A g s)) ≅
          (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj (sectionInvariant A g s)),
        oC.hom = localSourceMap A N hN hA hS d g s hs c adjC ∧
        oF.hom = localFamilyMap A N hN hA hS d g s hs c adjF ∧
        theta.hom = restrictedTheta A g s hs c.b ∧
        (restrictionAtOne A c.T
          (rawComparison A N hN hA c.T (invertibleOnSource N c.b hS) d _ _ oC oF)).hom =
            restrictedTheta A g s hs c.b ∧
        discrepancy A c.T
          (rawComparison A N hN hA c.T (invertibleOnSource N c.b hS) d _ _ oC oF) theta =
            Iso.refl _ := by
  sorry

end AlgebraicGeometry.Etale
