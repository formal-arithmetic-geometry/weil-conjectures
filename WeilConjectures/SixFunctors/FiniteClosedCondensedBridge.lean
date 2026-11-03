/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.Topology.Instances.Shrink

/-!
# Canonically small finite coefficients for the supplied exceptional adjunction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-finite-closed-shriek.md, coefficient convention; and
def-sfb-continuous-map-condensed-ring
(blueprint: lem-coef-finite-closed-shriek).

The recorded supplied adjunction accepts a Type-0 finite ring. Every finite ring in
Type u has the canonical Shrink carrier used below, with its inherited ring structure
and discrete topology. Ring maps are conjugated by Shrink.ringEquiv in the consumer.
Only size and ring-object instances are supplied here. All categories, finite-Tor
predicates, and exceptional functors in the consumer are the recorded condensed ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale


namespace WeilConjectures

/-- Finiteness supplies a small carrier without constraining the scheme universe.
Source: the finite-coefficient convention (a finite set is equivalent to some Fin n).
(blueprint: lem-coef-finite-closed-shriek). -/
noncomputable instance canonicalSmallCarrier (A : Type u) [CommRing A] [Finite A] :
    Small.{0} A := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin A
  exact small_of_surjective e.symm.surjective

/-- The canonically small finite carrier has the discrete topology.
Source: the same coefficient-presentation convention.
(blueprint: lem-coef-finite-closed-shriek). -/
noncomputable instance canonicalShrinkTopology (A : Type u) [CommRing A] [Finite A] :
    TopologicalSpace (Shrink.{0, u} A) := ⊥

/-- Discreteness of that chosen topology. Source: the same coefficient convention.
(blueprint: lem-coef-finite-closed-shriek). -/
noncomputable instance canonicalShrinkDiscrete (A : Type u) [CommRing A] [Finite A] :
    DiscreteTopology (Shrink.{0, u} A) := discreteTopology_bot (Shrink.{0, u} A)

/-- The existing continuous-function ring-object structure on the small carrier.
Source: def-sfb-continuous-map-condensed-ring.
(blueprint: lem-coef-finite-closed-shriek). -/
noncomputable abbrev canonicalShrinkMonObj (A : Type u) [CommRing A] [Finite A] :
    MonObj (Profinite.continuousMapRingObj (Shrink.{0, u} A)) :=
  Profinite.continuousMapRingObjOfUniverseMonObj.{u, 0} (Shrink.{0, u} A)

/-- Its actual inverse-image ring-object structure on each ordinary small pro-etale site.
Source: the pulled-back condensed coefficient convention.
(blueprint: lem-coef-finite-closed-shriek). -/
noncomputable abbrev canonicalShrinkCondensedMonObj (A : Type u) [CommRing A]
    [Finite A] (X : Scheme.{u}) :
    MonObj (condensedRingObj (Profinite.continuousMapRingObj (Shrink.{0, u} A)) X) :=
  letI : MonObj (Profinite.continuousMapRingObj (Shrink.{0, u} A)) :=
    canonicalShrinkMonObj A
  Functor.monObjObj (F := upperStarFromPoint X)
    (Profinite.continuousMapRingObj (Shrink.{0, u} A))

attribute [instance] canonicalShrinkMonObj canonicalShrinkCondensedMonObj

end WeilConjectures
