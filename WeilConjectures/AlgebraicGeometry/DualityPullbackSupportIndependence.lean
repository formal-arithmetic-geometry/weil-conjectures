/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualityPullbackData
import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Independence of the finite compact-support compositor -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The compact-support compositor is independent of its compatible coordinates.
Source: cor-sf-duality-pullback, naturality in the morphism, and the canonical
proper/open tower construction of compact-support composition.
(blueprint: lem-sf-duality-pullback-support-independence).

Proof: on Noetherian schemes apply the existing unbounded tower-coherence
formula to each coordinate pair. Both tower expressions equal the same canonical
unbounded compositor. The inverse of `finiteDualitySupportComp` is exactly that
expression, after expanding horizontal composition as its two whiskerings.
Equality of inverse natural transformations gives equality of the isomorphisms. -/
theorem finiteDualitySupportComp_independent (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact f] [QuasiCompact g] [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)]
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (d' : Compactification g) (e' : Compactification (f ≫ d'.i)) :
    finiteDualitySupportComp Λ f g d e = finiteDualitySupportComp Λ f g d' e' := by
  apply Iso.ext_inv
  have hd := unboundedEtaleLowerShriekCompIso_tower Λ f g d e
  have hd' := unboundedEtaleLowerShriekCompIso_tower Λ f g d' e'
  rw [hd] at hd'
  ext A
  have hA := NatTrans.congr_app hd' A
  simpa only [finiteDualitySupportComp, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, NatTrans.hcomp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using hA


set_option maxHeartbeats 200000 in
-- The normalization calculation uses the concrete compact-support comparisons.
set_option maxRecDepth 4000 in
/-- The explicit family has the prescribed Hom action in every compatible coordinate.
Source: the adjoint-transform construction in cor-sf-duality-pullback.
(blueprint: lem-sf-duality-pullback-support-independence).

Proof: finite type over a field makes all schemes Noetherian. In the coordinates
chosen by the family construction apply the proved five-arrow Hom formula. Expand
the Hom action and replace its support compositor using coordinate independence.
This gives the formula in the arbitrary prescribed coordinates. -/
theorem canonicalFiniteDualityPullbackFamily_normalized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (k : Type u) [Field k] :
    FiniteDualityPullbackNormalized Λ k (canonicalFiniteDualityPullbackFamily Λ k) := by
  intro X Y aY _ _ _ _ f _ _ _ _ _ d e A B h
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let d₀ := HasCompactification.compactification aY
  let e₀ := (HasCompactification.compactification (f ≫ aY)).ofComp d₀
  rw [canonicalFiniteDualityPullbackFamily_hom Λ k f aY A.obj B h]
  unfold finiteDualityPullbackHomAction
  rw [finiteDualitySupportComp_independent Λ f aY d₀ e₀ d e]


end AlgebraicGeometry.Etale
