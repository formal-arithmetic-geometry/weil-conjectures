/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfectGeneral
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointFibreTensorModels
public import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat

/-! # Monoidality of the canonical point pullback trivialization

Source: Steps 1 and 3 of the Frobenius pairing proof.
(blueprint: lem-pod-point-pullback-trivialization-monoidal)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical derived pullback trivialization over the separably closed point.
Source: point-sections transport Step 2, the exact pullback/identity comparison.
(blueprint: lem-pod-point-pullback-trivialization-monoidal). -/
def pointActionTrivialization (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : pointAction D Λ ≅ 𝟭 (pointDerived D Λ) :=
  leftDerivedUpperStarIsoMapDerivedCategory Λ (pointGeometricFrobenius D).hom ≪≫
    Functor.mapDerivedCategoryNatIso
      (upperStarIsoIdOfIsSepClosed Λ (pointGeometricFrobenius D).hom) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The canonical point-pullback trivialization respects the fixed native tensorator
and coefficient unit, not a monoidal structure transported from the conclusion.
Source: Steps 2--5 of the point-sections transport plan, over Steps 1 and 3 of
`thm-pod-equivariance-of-the-twisted-pairing.proof.md`.
Proof: the underived point-topos equivalence counit is monoidal. The compositor
identifying point pullback followed by Frobenius pullback with point pullback is
monoidal, so their conjugate `upperStarIsoIdOfIsSepClosed` is monoidal. Apply this
identity termwise to cochain complexes; the two tensor maps agree on each signed
summand. On flat-term K-flat replacements the pullback tensor comparison is the
native derived tensorator. Localizing the termwise square therefore proves the
monoidal tensor equation on all derived objects. The same argument on the
single regular module proves the unit equation. The exact/left-derived comparison
is monoidal for the transported structure displayed below, so the resulting
isomorphism is exactly `pointActionTrivialization`.
(blueprint: lem-pod-point-pullback-trivialization-monoidal). -/
theorem point_action_trivialization_monoidal
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    letI : (pointAction D Λ).Monoidal :=
      Functor.Monoidal.transport
        (leftDerivedUpperStarIsoMapDerivedCategory Λ (pointGeometricFrobenius D).hom).symm
    NatTrans.IsMonoidal (pointActionTrivialization D Λ).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
