/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.TransportCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingDataSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.CartierReductionDataSupplement
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-finite-encoding). -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]

/-- Sheafification of constant functions, followed by the sheafification counit.
This is a literal morphism, before its invertibility proof.
Source: Bhatt--Scholze 5.3.2 (blueprint: def-pur-transport-finite-encoding). -/
public def finiteConstants :=
  (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      (Functor.whiskerRight (Profinite.constantToContinuousRing A)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
    (Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheaf A)).hom

/-- The canonical constant-function map is invertible and multiplicative.
Source: Bhatt--Scholze 5.3.2 (blueprint: def-pur-transport-finite-encoding).
Proof: cover each profinite set by the finitely many clopen fibres of its
continuous finite-valued function. These local constants glue uniquely. The
ring laws hold on constant sections and descend through sheafification. -/
public theorem finiteConstants_spec :
    IsIso (finiteConstants.{u} A) ∧ IsMonHom (finiteConstants.{u} A) := by
  let J := coherentTopology Profinite.{u}
  let φ := Profinite.constantToContinuousAb.{u} A
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  unfold finiteConstants
  exact ⟨inferInstance, inferInstance⟩

/-- The actual constant-function ring comparison.
Source: finite coefficient encoding (blueprint: def-pur-transport-finite-encoding). -/
public def finitePointIso :=
  letI := (finiteConstants_spec.{u} A).1
  asIso (finiteConstants.{u} A)

/-- Multiplicativity of the fixed finite point comparison.
Source: finite coefficient encoding (blueprint: def-pur-transport-finite-encoding). -/
public instance finitePointIso_mon : IsMonHom (finitePointIso.{u} A).hom :=
  (finiteConstants_spec.{u} A).2

/-- Sectionwise encoding with the literal underlying abelian group.
Source: the tensor universal property
(blueprint: def-pur-transport-finite-encoding). -/
public def finiteModuleEncoding (R : Type (u + 1)) [Ring R] :
    Mod Ab.{u + 1} (AddCommGrpCat.of R) ⥤ ModuleCat.{u + 1} R :=
  CategoryTheory.internalToModule R

/-- The internal scalar action and the ordinary module action determine one another.
Source: the tensor universal property
(blueprint: def-pur-transport-finite-encoding).
Proof: recover scalar multiplication by evaluating the action on pure tensors.
The unit and associativity diagrams give the module laws. The inverse uses the
bilinear action, and the two constructions agree on objects and morphisms. -/
public theorem finiteModuleEncoding_isEquivalence (R : Type (u + 1)) [Ring R] :
    (finiteModuleEncoding R).IsEquivalence := by
  change (CategoryTheory.internalToModule R).IsEquivalence
  infer_instance

/-- The sectionwise encoding is an equivalence.
Source: scalar actions (blueprint: def-pur-transport-finite-encoding). -/
public instance finiteModuleEncoding_equiv (R : Type (u + 1)) [Ring R] :
    (finiteModuleEncoding R).IsEquivalence := finiteModuleEncoding_isEquivalence R

/-- The encoding forgets to exactly the original additive group.
Source: sectionwise construction (blueprint: def-pur-transport-finite-encoding).
Proof: the functor changes only the recorded scalar action; the carrier and maps
are the original internal module carrier and additive maps. -/
public theorem finiteModuleEncoding_forget (R : Type (u + 1)) [Ring R] :
    finiteModuleEncoding R ⋙ forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of R) := by
  rfl

/-- The fixed sectionwise encoding, with identity underlying groups and maps.
Source: finite coefficient realization (blueprint: def-pur-transport-finite-encoding). -/
@[expose] public def finiteEncoding (X : Scheme.{u}) :
    FiniteDiscreteProEtaleSheaves A X ≌ FiniteDiscreteInternalModules A X :=
  finiteDiscreteCoefficientEquivalence A (finitePointIso A)
    (finiteModuleEncoding (ULift.{u + 1} A)) (finiteModuleEncoding_forget _) X

/-- The same equivalence applied termwise to complexes and localized.
Source: finite coefficient realization (blueprint: def-pur-transport-finite-encoding). -/
@[expose] public def finiteEncodingDerived (X : Scheme.{u}) :=
  (finiteEncoding A X).mapDerivedCategory

/-- Exact direct images compare by the identity on sections and scalar actions.
Source: Stacks 03CY (blueprint: def-pur-transport-finite-encoding). -/
public def finiteEncodingPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar (Profinite.continuousMapRingObj A) f ⋙
      (finiteEncoding A Y).inverse ≅
    (finiteEncoding A X).inverse ⋙ ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f :=
  CondensedRing.encodingPushforwardNatIso A (finitePointIso A)
    (finiteModuleEncoding (ULift.{u + 1} A)) (finiteModuleEncoding_forget _) Y X f

/-- Exact inverse images compare by the mate of that sections identity.
Source: Stacks 03CY (blueprint: def-pur-transport-finite-encoding). -/
public def finiteEncodingPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finiteEncoding A Y).inverse ⋙ ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ≅
    CondensedRing.upperStar (Profinite.continuousMapRingObj A) f ⋙
      (finiteEncoding A X).inverse :=
  CondensedRing.encodingPullbackNatIso A (finitePointIso A)
    (finiteModuleEncoding (ULift.{u + 1} A)) (finiteModuleEncoding_forget _) Y X f

end AlgebraicGeometry.ProEtale.PurityTransport
