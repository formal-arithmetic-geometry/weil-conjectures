/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra

/-! # Descent of a split cover to its equivariant function algebra -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Descent first gives the invariant algebra of the whole split cover, before
any decomposition into orbits or stabilizers.

Source: Stacks Project, Tag 03SF (Galois covers), and Tag 023R (affine descent).
Proof: put h=ι(g). Faithful flatness makes D(h) in Spec C a surjective finite
flat cover of D(h) in Spec H. It is etale by assumption, and the unique-rotation
hypothesis makes the map from G copies of this cover to its self-fibre-product
an isomorphism: both are finite etale and it is bijective on geometric fibres.
Pull δ back along k to split Y over D(h) in Spec C into d components. This
principal open is nonempty and connected since C is a domain and h is nonzero.
The descent datum therefore permutes the components, and the cocycle law gives
α : G →* Perm(Fin d), with the convention ρ a (f i)=f(α a i).
Affine faithfully flat descent identifies the descended algebra with these
equivariant functions in C[1/h]. They equal the localization of the explicitly
constructed equivariant algebra in C: clear denominators simultaneously in the
finite product, and use injectivity of C → C[1/h] to remove every factor of h
from the equivariance equations. All algebra maps fix H, so the identification
is in Over(Spec H). If d=0 both sides are empty. No orbit representatives,
stabilizers, or product of fixed rings are asserted by this step.
(blueprint: lem-sbc-affine-torsor-equivariant-descent) -/
theorem affine_torsor_equivariant_descent
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j]
    (d : ℕ) :
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens :=
      PrimeSpectrum.basicOpen (algebraMap H C (ι g))
    Etale (V.ι ≫ q) →
    (∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b) →
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec R) (k : V.toScheme ⟶ T),
      k ≫ t = V.ι ≫ q ≫ Spec.map (CommRingCat.ofHom ι) →
    ∀ (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t →
    ∃ α : G →* Equiv.Perm (Fin d),
      let A := affineTorsorEquivariantAlgebra H C G ρ d α
      let V : (Spec (CommRingCat.of A)).Opens :=
        PrimeSpectrum.basicOpen (algebraMap H A (ι g))
      Nonempty (Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) ≅
        Over.mk (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H A)))) := by sorry

end AlgebraicGeometry.Scheme
