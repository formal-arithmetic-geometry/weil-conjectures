/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerCoefficientModels

/-! # Normalized scalar maps on ordinary derived invariants
Source: direct-image proof (3), the actual scalar map on the right-hand side.
(blueprint: def-sfb-kummer-invariant-scalar-map).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- The ordinary right-derived invariants on a specified degree-zero action module,
with canonical localization transport followed by exact point pullback.
Source: direct-image proof (3), p_S* R Gamma
(blueprint: def-sfb-kummer-invariant-scalar-map). -/
def kummerInvariantObject (B : Model A G) (S : Scheme.{u}) (N : Equivariant A G) :
    DerivedCategory (KummerModules A.X S) :=
  (kummerPointPullBig A S).obj
    (B.invariants.functor.rightDerivedFunctor.{u + 2, u + 2,
      u + 1, u + 1, u + 2, u + 2}.obj
        ((DerivedCategory.singleFunctor.{u + 2} _ 0).obj N))

/-- Exact point pullback of the actual invariant-resolution complex.
Source: direct-image proof (3), normalized invariant augmentation
(blueprint: def-sfb-kummer-invariant-scalar-map). -/
def kummerInvariantComplex (B : Model A G) (S : Scheme.{u})
    (J : CochainComplex (Equivariant A G) ℕ) : CochainComplex (KummerModules A.X S) ℕ :=
  (((upperStarFromPoint S).mapMod A.X).mapHomologicalComplex (.up ℕ)).obj
    ((B.invariants.functor.mapHomologicalComplex (.up ℕ)).obj J)

/-- The actual right-derived resolution comparison, followed by exact point pullback.
Source: direct-image proof (3), derived invariant resolution
(blueprint: def-sfb-kummer-invariant-scalar-map). -/
def kummerInvariantResolutionIso (B : Model A G) (S : Scheme.{u})
    {N : Equivariant A G} (J : InjectiveResolution N) :
    kummerInvariantObject A G B S N ≅
      DerivedCategory.Q.obj ((kummerInvariantComplex A G B S J.cocomplex).extend
        ComplexShape.embeddingUpNat) :=
  (kummerPointPullBig A S).mapIso (resolutionComparison B.invariants J) ≪≫
    (kummerPointPullBigFactors A S).app _ ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.mapExtendIso
        ((B.invariants.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
        ComplexShape.embeddingUpNat ((upperStarFromPoint S).mapMod A.X))

/-- Restriction of the continuous field coefficients commutes with exact point pullback.
This is the actual module-pullback scalar comparison, not a chosen transport.
Source: direct-image proof (3), scalar restriction on the stratum
(blueprint: def-sfb-kummer-invariant-scalar-map). -/
def kummerPointScalarIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (S : Scheme.{u}) :
    Mod.comap (tameBoundaryScalarMap ℓ E) ⋙
        (upperStarFromPoint S).mapMod (Profinite.continuousMapRingObj E.1) ≅
      (upperStarFromPoint S).mapMod (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) ⋙
        Mod.comap (coefficientMap (tameBoundaryScalarMap ℓ E) S) :=
  (upperStarFromPoint S).mapModComapIso (tameBoundaryScalarMap ℓ E)

end AlgebraicGeometry.ProEtale.CondensedRing
