/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.Curve.H1DualTateModule
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Conj

/-!
# Continuous adic characters and the first étale cohomology tower

Source: Weil conjectures blueprint, main-20261015, sec-purity-real-sheaves,
sk-p-real-rankone, equation (3.2) (blueprint: lem-wf-additive-characters-h1).

The inverse system is the existing `curveH1CoefficientSystem`, defined for every scheme.
Its `Sheaf.H` is the Ext model of the recorded `Etale.cohomology` on a sheaf in degree zero.
The helpers below spell out canonical pullback on cohomology and on fibre automorphisms; the
fibre path of a pulled-back cover is the existing `Scheme.FiniteEtale.pullbackFiberIso`.
The upstream `Scheme.EtaleTorsor.continuousMonoidHomPadicEquiv` (and `_comp`) is a bijection
for a connected scheme without additivity, pointed naturality or the Weil-group formula.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme Scheme.FiniteEtale

/-- Pullback on the n-th finite coefficient H¹, followed by the canonical identification of
pullback of a constant sheaf with the same constant sheaf.
Source: blueprint main-20261015, equation (3.2), naturality
(blueprint: lem-wf-additive-characters-h1). -/
noncomputable def padicH1CoordinatePullback {X Y : Scheme.{u}} (f : X ⟶ Y) (ℓ n : ℕ) :
    Sheaf.H (Y.constantZMod (ℓ ^ n)) 1 →+ Sheaf.H (X.constantZMod (ℓ ^ n)) 1 :=
  (Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) 1).comp
      (Etale.cohomologyMap f (Y.constantZMod (ℓ ^ n)) 1)

/-- The map on fundamental groups induced by pullback, with a specified path of fibre
functors. Its value is obtained by whiskering a fibre automorphism with pullback and
conjugating by the path; it is not an arbitrary group homomorphism. It is the map
`Scheme.FiniteEtale.fundamentalGroupMap τ (Aut (fiber x)) (Aut (fiber y))`, written for every
scheme: that declaration needs a `ConnectedSpace` instance on the target, which the theorem
below only has as an explicit geometric-connectedness proof.
Source: blueprint main-20261015, equation (3.2), pointed naturality
(blueprint: lem-wf-additive-characters-h1). -/
noncomputable def padicH1FundamentalMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y)
    (τ : Scheme.FiniteEtale.pullback f ⋙ fiber x ≅ fiber y) :
    Aut (fiber x) →* Aut (fiber y) :=
  τ.conjAut.toMonoidHom.comp
    (((Functor.whiskeringLeft Y.FiniteEtale X.FiniteEtale FintypeCat).obj
      (Scheme.FiniteEtale.pullback f)).mapAut (fiber x))

/-- Continuous adic characters are naturally and Frobenius-equivariantly the inverse limit
of finite constant H¹ groups. The additive type tag on continuous multiplicative homs means
that their target is the additive group of the adic integers and the group law is pointwise
addition. A family of comparisons is asserted simultaneously to express naturality.

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-p-real-rankone,
`lem-wf-additive-characters-h1`, equation (3.2) and the displayed inverse conjugation formula;
chapter setup `sk-d-real-setup`, opening paragraph (ℓ distinct from the base characteristic)
(blueprint: lem-wf-additive-characters-h1).

Proof:
1. The natural additive equivalences of `lem-wf-finite-constant-h1-pi1` identify each H¹
with continuous finite characters and coefficient reduction with reduction of characters.
2. Form the ring of compatible residues. The lift and uniqueness clauses of
`lem-exc-padic-residue-universal-property` identify this ring with the adic integers.
The level-zero residue ring is zero, so adding that coordinate does not change the limit.
3. Reducing an adic character gives compatible continuous characters: residues are locally
constant by the kernel and norm clauses of the residue universal property.
4. Lift compatible characters pointwise. Residue separation proves the homomorphism law.
For continuity choose n with ℓ^(-n) below a given positive radius; the open fibre of the
n-th finite character maps into that ball by the kernel and norm criterion.
5. Separation and the lift equations show the constructions are inverse and additive.
Finite-level naturality gives the pointed pullback equality in every limit coordinate.
6. For a degree-one Weil lift s, finite-level Weil descent precomposes characters with
s⁻¹ g s. Apply the same equation in every coordinate, giving the last clause below.
The geometric fundamental group maps into the arithmetic one by pullback of covers;
the path used to write that map is `pullbackFiberIso`, the first projection on fibre points.
-/
theorem exists_padicCharactersH1 (k₀ : Type u) [Field k₀] [Finite k₀]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k₀) :
    ∃ E : ∀ (U₀ : Scheme.{u}) (p : U₀ ⟶ Spec (.of k₀)),
      GeometricallyConnected p → IsSeparated p → (LocallyOfFiniteType p ∧ QuasiCompact p) →
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ p.geometricFiber),
        Additive (Aut (fiber x) →ₜ* Multiplicative ℤ_[ℓ]) ≃+
          ↥(limit (curveH1CoefficientSystem p.geometricFiber ℓ)),
      (∀ (U₀ V₀ : Scheme.{u}) (p : U₀ ⟶ Spec (.of k₀)) (q : V₀ ⟶ Spec (.of k₀))
        (hp : GeometricallyConnected p) (hp' : IsSeparated p)
        (hp'' : LocallyOfFiniteType p ∧ QuasiCompact p)
        (hq : GeometricallyConnected q) (hq' : IsSeparated q)
        (hq'' : LocallyOfFiniteType q ∧ QuasiCompact q)
        (Ω Ω' : Type u) [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
        (x : Spec (.of Ω) ⟶ p.geometricFiber) (y : Spec (.of Ω') ⟶ q.geometricFiber)
        (f : p.geometricFiber ⟶ q.geometricFiber)
        (τ : Scheme.FiniteEtale.pullback f ⋙ fiber x ≅ fiber y)
        (b : Additive (Aut (fiber y) →ₜ* Multiplicative ℤ_[ℓ])),
        ∃ b' : Additive (Aut (fiber x) →ₜ* Multiplicative ℤ_[ℓ]),
          (∀ g, b'.toMul g = b.toMul (padicH1FundamentalMap f x y τ g)) ∧
          ∀ n : ℕ,
            limit.π (curveH1CoefficientSystem p.geometricFiber ℓ) (.op n)
              (E U₀ p hp hp' hp'' Ω x b') =
            padicH1CoordinatePullback f ℓ n
              (limit.π (curveH1CoefficientSystem q.geometricFiber ℓ) (.op n)
                (E V₀ q hq hq' hq'' Ω' y b))) ∧
      (∀ (U₀ : Scheme.{u}) (p : U₀ ⟶ Spec (.of k₀))
        (hp : GeometricallyConnected p) (hp' : IsSeparated p)
        (hp'' : LocallyOfFiniteType p ∧ QuasiCompact p)
        (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ p.geometricFiber),
        ∀ s : @weilGroup k₀ _ U₀ p Ω _ _ (x ≫ p.geometricFiberProj)
          (Aut (fiber (x ≫ p.geometricFiberProj))) _ _ _ hp,
          @weilGroupDeg k₀ _ U₀ p Ω _ _ (x ≫ p.geometricFiberProj)
            (Aut (fiber (x ≫ p.geometricFiberProj))) _ _ _ hp s = Multiplicative.ofAdd 1 →
          ∀ b : Additive (Aut (fiber x) →ₜ* Multiplicative ℤ_[ℓ]),
          ∃ b' : Additive (Aut (fiber x) →ₜ* Multiplicative ℤ_[ℓ]),
            (∀ g : Aut (fiber x), ∃ h : Aut (fiber x),
              padicH1FundamentalMap p.geometricFiberProj x (x ≫ p.geometricFiberProj)
                (pullbackFiberIso p.geometricFiberProj x) h =
                s.val.1⁻¹ *
                  padicH1FundamentalMap p.geometricFiberProj x (x ≫ p.geometricFiberProj)
                    (pullbackFiberIso p.geometricFiberProj x) g *
                    s.val.1 ∧ b'.toMul g = b.toMul h) ∧
            ∀ n : ℕ,
              limit.π (curveH1CoefficientSystem p.geometricFiber ℓ) (.op n)
                (E U₀ p hp hp' hp'' Ω x b') =
              padicH1CoordinatePullback p.geometricGaloisFrobenius.hom ℓ n
                (limit.π (curveH1CoefficientSystem p.geometricFiber ℓ) (.op n)
                  (E U₀ p hp hp' hp'' Ω x b))) := by
  sorry

end AlgebraicGeometry
