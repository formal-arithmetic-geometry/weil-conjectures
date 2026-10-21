/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.BoundaryQFoundation

/-! # Boundary q and evaluation under site comparison

Source: blueprint boundary-duality discharge, final paragraph
(blueprint: def-weil-boundary-q-maps).
The pro-etale transpose is computed in comparison coordinates using the recorded Hom
transport. This uses the actual finite exceptional functor, not an ambient pro-etale adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
open BoundaryComparison

/-- Fixed scalar modules at the actual value universe of the small sites.
Source: blueprint ordinary coefficient modules
(blueprint: def-weil-boundary-q-maps). -/
abbrev coefficients (A : Type (u + 1)) [CommRing A] := ModuleCat.{u + 1} A

/-- The recorded etale exceptional inverse image with the identity-open compactification.
Source: blueprint finite exceptional inverse image;
(blueprint: def-weil-boundary-q-maps). -/
abbrev etaleExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] :=
  letI := (Compactification.ofIsProper i).hasCompactification
  Etale.rightDerivedUpperShriek (coefficients A) i

/-- Its actual adjunction, normalized by the identity-open support comparison.
Source: blueprint ordinary exceptional adjunction; Stacks 0B65
(blueprint: def-weil-boundary-q-maps). -/
def exceptionalAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] :
    etaleImage (coefficients A) i ⊣ etaleExceptional A i :=
  letI := (Compactification.ofIsProper i).hasCompactification
  (Etale.rightDerivedUpperShriekAdjunction
    (coefficients A) i).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (coefficients A) i)

/-- The finite exceptional formula, in fixed constant coefficients. Its factors are the
existing derived functors; only the identity-open compactification instance is installed.
Source: blueprint finite exceptional inverse image
(blueprint: def-weil-boundary-q-maps). -/
abbrev proetaleExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] :=
  (comparisonLowerStar (coefficients A) T).rightDerivedFunctor ⋙
    etaleExceptional A i ⋙ comparison (coefficients A) Z

/-- The specified Hom transport: precompose with b, use the comparison adjunction, use
ordinary exceptional adjunction, then apply C_Z to the resulting morphism.
Source: Stacks 0DV0 and 0B65; blueprint displayed Hom chain
(blueprint: def-weil-boundary-q-maps). -/
def homTransport (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (coefficients A)))
    (L : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (coefficients A)))
    (f : (proetaleImage (coefficients A) i).obj
      ((comparison (coefficients A) Z).obj H.obj) ⟶ L.obj) :
    (comparison (coefficients A) Z).obj H.obj ⟶
      (proetaleExceptional A i).obj L.obj :=
  (comparison (coefficients A) Z).map
    ((exceptionalAdjunction A i).homEquiv _ _
      ((derivedComparisonAdjunction
        (coefficients A) T).homEquiv _ _
        ((directImageMate (coefficients A) i).app H.obj ≫ f)))

/-- The etale exceptional value retains its bounded-below typing from the existing
finite-coefficient interface. Source: blueprint finite exceptional inverse image
(blueprint: def-weil-boundary-q-maps). -/
def exceptionalPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (N : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (coefficients A))) :
    DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (coefficients A)) :=
  letI := (Compactification.ofIsProper i).hasCompactification
  ⟨(etaleExceptional A i).obj N.obj,
    Etale.plus_rightDerivedUpperShriek_obj
      (coefficients A) i N.obj N.property⟩

/-- The identification C_Z G_e N -> G_p C_T N induced by the actual comparison unit.
Source: blueprint displayed Hom chain; Stacks 0DV0
(blueprint: def-weil-boundary-q-maps). -/
def exceptionalOriginMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i]
    (N : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (coefficients A))) :
    (comparison (coefficients A) Z).obj ((etaleExceptional A i).obj N.obj) ⟶
      (proetaleExceptional A i).obj ((comparison (coefficients A) T).obj N.obj) :=
  (comparison (coefficients A) Z).map ((etaleExceptional A i).map
    ((derivedComparisonAdjunction
      (coefficients A) T).unit.app N.obj))

/-- The transported exceptional counit is the uniquely specified preimage of the identity,
written using its etale-origin representative. The identification is exactly the origin-unit
map, and eta is exactly the inverse of the fixed canonical mate.
Source: Stacks 0B65 and 0DV0; blueprint counit formula
(blueprint: def-weil-boundary-q-maps). -/
def CounitComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (N : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (coefficients A))) : Prop :=
  IsIso (exceptionalOriginMap A i N) ∧
  ∃ b : (comparison (coefficients A) T).obj
        ((etaleImage (coefficients A) i).obj (exceptionalPlus A i N).obj) ≅
      (proetaleImage (coefficients A) i).obj
        ((comparison (coefficients A) Z).obj (exceptionalPlus A i N).obj),
    b.hom = (directImageMate (coefficients A) i).app (exceptionalPlus A i N).obj ∧
    ∃ μ : (proetaleImage (coefficients A) i).obj
        ((comparison (coefficients A) Z).obj (exceptionalPlus A i N).obj) ⟶
        (comparison (coefficients A) T).obj N.obj,
      homTransport A i (exceptionalPlus A i N)
        ((siteComparisonDerivedPullbackPlus T (A)).obj N) μ =
          exceptionalOriginMap A i N ∧
      μ = b.inv ≫ (comparison (coefficients A) T).map ((exceptionalAdjunction A i).counit.app N.obj)


/-- The displayed Hom transport on ambient objects. Boundedness is needed for its
bijectivity, not for this composite. On D+ this is exactly `homTransport`.
Source: blueprint boundary-duality discharge, Hom chain
(blueprint: def-weil-boundary-q-maps). -/
def rawHomTransport (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i]
    (H : DerivedCategory (Sheaf Z.smallEtaleTopology (coefficients A)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (coefficients A)))
    (f : (proetaleImage (coefficients A) i).obj
      ((comparison (coefficients A) Z).obj H) ⟶ L) :
    (comparison (coefficients A) Z).obj H ⟶ (proetaleExceptional A i).obj L :=
  (comparison (coefficients A) Z).map
    ((exceptionalAdjunction A i).homEquiv _ _
      ((derivedComparisonAdjunction (coefficients A) T).homEquiv _ _
        ((directImageMate (coefficients A) i).app H ≫ f)))

/-- The exceptional comparison on ambient objects, induced by the same unit as
`exceptionalOriginMap`. Its restriction to D+ is exactly that recorded declaration.
Source: blueprint q comparison (blueprint: def-weil-boundary-q-maps). -/
def rawOriginMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i]
    (N : DerivedCategory (Sheaf T.smallEtaleTopology (coefficients A))) :
    (comparison (coefficients A) Z).obj ((etaleExceptional A i).obj N) ⟶
      (proetaleExceptional A i).obj ((comparison (coefficients A) T).obj N) :=
  (comparison (coefficients A) Z).map ((etaleExceptional A i).map
    ((derivedComparisonAdjunction (coefficients A) T).unit.app N))

/-- The restricted exceptional counit: invert the specified theta_N, then apply the
unique counit fixed by `CounitComparison` and the recorded Hom transport.
Source: blueprint exceptional counit comparison
(blueprint: def-weil-boundary-q-maps). -/
def proCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (coefficients A)))
    (h : CounitComparison A i N) :
    (proetaleImage (coefficients A) i).obj
      ((proetaleExceptional A i).obj ((comparison (coefficients A) T).obj N.obj)) ⟶
        (comparison (coefficients A) T).obj N.obj :=
  letI := h.1
  (proetaleImage (coefficients A) i).map (inv (exceptionalOriginMap A i N)) ≫
    h.2.choose_spec.2.choose



/-- The pro-etale q in comparison coordinates. Transpose t after identifying its
source by the monoidal/pullback comparison and `1 tensor theta_N`, and its target
by the monoidal comparison. Naturality of transposition gives precisely
`sourceComparison ≫ (1 tensor theta_N) ≫ q_p ≫ G_p(tensorComparison.inv)`.
Source: blueprint q comparison, proof steps 1--2
(blueprint: def-weil-boundary-q-maps). -/
def proQInComparisonCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (σZ : ProSignedSymmetry (coefficients A) Z)
    (σT : ProSignedSymmetry (coefficients A) T)
    (M N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (coefficients A)))
    (hc : CounitComparison A i N)
    [IsIso (((ProEtale.rightDerivedLowerStarProjectionMap (coefficients A) i).app
      ((proetaleExceptional A i).obj ((comparison (coefficients A) T).obj N.obj))).app
        ((comparison (coefficients A) T).obj M.obj))] :
    (comparison (coefficients A) Z).obj
      (((Etale.derivedTensor (coefficients A) Z).obj
        ((Etale.upperStar (coefficients A) i).leftDerivedFunctor.obj M.obj)).obj
          ((etaleExceptional A i).obj N.obj)) ⟶
      (proetaleExceptional A i).obj
        ((comparison (coefficients A) T).obj
          (((Etale.derivedTensor (coefficients A) T).obj M.obj).obj N.obj)) :=
  assembleProQ (coefficients A) i σZ σT (etaleExceptional A i) (proetaleExceptional A i)
    (rawHomTransport A i) M.obj N.obj (exceptionalOriginMap A i N) (proCounit A i N hc)


/-- Equality of the two actual q maps, with the target theta and all source
comparisons retained. The right side transposes the pro-etale t in those charts.
Source: blueprint boundary-duality discharge, q comparison
(blueprint: def-weil-boundary-q-maps). -/
def BoundaryQCompatibility (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (P : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology (coefficients A)))) :
    Prop :=
  ∀ (σeZ : EtaleSignedSymmetry (coefficients A) Z)
    (σeT : EtaleSignedSymmetry (coefficients A) T)
    (σpZ : ProSignedSymmetry (coefficients A) Z)
    (σpT : ProSignedSymmetry (coefficients A) T)
    (M N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (coefficients A))),
    P M.obj → P N.obj →
    Etale.DerivedCategory.isBoundedConstructible A Z
      ((etaleExceptional A i).obj N.obj) →
    ∀ (hc : CounitComparison A i N),
      ProjectionComparison (coefficients A) i ((etaleExceptional A i).obj N.obj) M.obj →
      ∀ (_he : IsIso (etaleProjection (coefficients A) i
          ((etaleExceptional A i).obj N.obj) M.obj))
        (_hp : IsIso
          (((ProEtale.rightDerivedLowerStarProjectionMap (coefficients A) i).app
            ((proetaleExceptional A i).obj ((comparison (coefficients A) T).obj N.obj))).app
              ((comparison (coefficients A) T).obj M.obj))),
        comparedEtaleQ (coefficients A) i σeZ σeT
          (etaleExceptional A i) (proetaleExceptional A i) (exceptionalAdjunction A i)
          (rawOriginMap A i) M.obj N.obj =
          proQInComparisonCoordinates A i σpZ σpT M N hc

end AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
