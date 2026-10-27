/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-!
# Equivariant sharp charts for tame geometric stabilizers

Source: Illusie--Laszlo--Orgogozo, Exposé VI, 3.4, Proposition 3.5(a), and 3.7(a),
printed pp. 74--75 (blueprint: lem-per-very-tame-equivariant-sharp-chart).

The coefficient ring is Mathlib's cyclotomic ring over Z, with n inverted.
The strict equivariant map to its monoid spectrum is expressed by its ring map on
an affine chart, the chart condition on the log structure, and equivariance on all
monoid-ring elements. Thus the diagonal action and the specified characteristic
identification are both retained.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The coefficient ring Lambda = Z[zeta_n, 1/n] of ILO VI 3.4, using the
existing Mathlib cyclotomic ring and localization construction.
Source: ILO VI 3.4 (blueprint: lem-per-very-tame-equivariant-sharp-chart). -/
abbrev sharpChartCyclotomicRing (n : ℕ) :=
  Localization.Away (n : CyclotomicRing n ℤ ℚ)

/-- A tame stabilizer trivial on the characteristic admits an equivariant sharp chart.
Source: ILO VI Proposition 3.5(a), 3.4, and proof 3.7(a), printed pp. 74--75
(blueprint: lem-per-very-tame-equivariant-sharp-chart).

Proof plan:
1. Choose an fs chart P and its face F of elements becoming units at t. The
characteristic is P_F/F^gp. By lem-trf-fs-face-sharpening it is fs sharp and its group
completion is free of finite rank. The log unit condition gives the exact sequence
0 -> A^units -> M_t^gp -> Q^gp -> 0.
2. Pointed affine etale neighbourhoods are cofinal
(lemma-weil-pbc-affine-neighbourhood-cofinal). Their ring colimit is strictly henselian
(lem-weil-pbc-strict-henselization-local-structure). Geometric inertia fixes its residue
field, and the tame order is a unit. A group section exists by freeness of Q^gp;
its restriction to Q lands in M_t because the difference from any lift is a unit.
Apply lem-per-tame-unit-extension-character to obtain the section and the pairing chi.
3. Apply lem-trf-fine-log-stalk-chart-spreading to this specified section. Spread the
finitely many action equations for generators and the finite group, together with the
roots of unity. Take a common equivariant pointed affine refinement, then shrink where
n is invertible. This preserves the identity map on the characteristic.
4. Inertia fixes all n-th roots, by uniqueness of their lifts from the residue field;
lem-sbc-strict-local-roots-of-unity supplies a primitive root. Spread it to obtain the
coefficient map from Lambda. The diagonal action fixes Lambda and multiplies z^q by
the prescribed character. The chart's structural map extends to the monoid ring;
its generator equations give equivariance on every element. Being a chart is precisely
strictness for the standard log structure on Spec Lambda[Q]. No log regularity or
condition on the stratum is used.
-/
theorem exists_tame_equivariant_sharp_chart
    (X : FineSaturatedLogScheme.{u}) {G : Type v} [Group G] [Finite G]
    (a : FSLogGroupAction G X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme) (H : Subgroup G)
    (_hH : ∀ g : G, g ∈ H ↔ t ≫ (a.baseAction g).hom = t)
    (_htame : IsUnit (Nat.card H : Ω))
    (_hchar : ∀ (h : H) (W V : X.scheme.Etale) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ (a.logMap h.val).base)
      (w : (Scheme.pointSmallEtale t).fiber.obj W)
      (z : (Scheme.pointSmallEtale t).fiber.obj V), z.left ≫ k = w.left →
        ∀ s : X.logStructure.monoidSheaf.obj.obj (op W),
          Associated
            (X.logStructure.toEtalePrelogStructure.germ t V z
              ((a.logMap h.val).sectionMap W V k hk s))
            (X.logStructure.toEtalePrelogStructure.germ t W w s)) :
    IsFineSaturatedMonoid (X.logStructure.characteristic t) ∧
    (∀ q : X.logStructure.characteristic t, IsUnit q → q = 1) ∧
    ∃ (W : X.scheme.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
      (b : H →* Aut W.left)
      (hb : ∀ h : H, (b h).hom ≫ W.hom = W.hom ≫ (a.logMap h.val).base)
      (β : X.logStructure.characteristic t →*
        X.logStructure.monoidSheaf.obj.obj (op W))
      (unitLift : Γ(W.left, ⊤)ˣ →* X.logStructure.monoidSheaf.obj.obj (op W))
      (χ : TensorProduct ℤ (Additive (Abelianization H))
        (Additive (Algebra.GrothendieckGroup (X.logStructure.characteristic t))) →ₗ[ℤ]
          Additive (rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t)))
      (ρ : rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t) →* Γ(W.left, ⊤)ˣ)
      (c : sharpChartCyclotomicRing (Nat.card H) →+* Γ(W.left, ⊤))
      (e : rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t) ≃*
        rootsOfUnity (Nat.card H) (sharpChartCyclotomicRing (Nat.card H)))
      (d : H →* (MonoidAlgebra (sharpChartCyclotomicRing (Nat.card H))
        (X.logStructure.characteristic t) ≃+*
          MonoidAlgebra (sharpChartCyclotomicRing (Nat.card H))
            (X.logStructure.characteristic t)))
      (θ : MonoidAlgebra (sharpChartCyclotomicRing (Nat.card H))
        (X.logStructure.characteristic t) →+* Γ(W.left, ⊤)),
      IsAffine W.left ∧ X.logStructure.IsChart W β ∧
      (∀ h : H, w.left ≫ (b h).hom = w.left) ∧
      (∀ q : X.logStructure.characteristic t,
        Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W w (β q)) = q) ∧
      (∀ r : Γ(W.left, ⊤)ˣ, X.logStructure.alpha.app (op W) (unitLift r) = (r : Γ(W.left, ⊤))) ∧
      (∀ z : rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t),
        strictLocalGerm X.scheme t W w (ρ z : Γ(W.left, ⊤)) =
          ((z : (strictLocalRing X.scheme t)ˣ) : strictLocalRing X.scheme t)) ∧
      (∀ (h : H) (z : rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t)),
        (b h).hom.appTop (ρ z : Γ(W.left, ⊤)) = (ρ z : Γ(W.left, ⊤))) ∧
      (∀ (h : H) (q : X.logStructure.characteristic t),
        (a.logMap h.val).sectionMap W W (b h).hom (hb h) (β q) =
          unitLift (ρ (Additive.toMul (χ (TensorProduct.tmul ℤ
            (Additive.ofMul (Abelianization.of h))
            (Additive.ofMul (Algebra.GrothendieckGroup.of q)))))) * β q) ∧
      (∀ z : rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t),
        c (((e z : rootsOfUnity (Nat.card H) (sharpChartCyclotomicRing (Nat.card H))) :
          (sharpChartCyclotomicRing (Nat.card H))ˣ) : sharpChartCyclotomicRing (Nat.card H)) =
            (ρ z : Γ(W.left, ⊤))) ∧
      (∀ (h : H) (r : sharpChartCyclotomicRing (Nat.card H)),
        d h (MonoidAlgebra.single 1 r) = MonoidAlgebra.single 1 r) ∧
      (∀ (h : H) (q : X.logStructure.characteristic t),
        d h (MonoidAlgebra.single q 1) = MonoidAlgebra.single q
          (((e (Additive.toMul (χ (TensorProduct.tmul ℤ
            (Additive.ofMul (Abelianization.of h))
            (Additive.ofMul (Algebra.GrothendieckGroup.of q)))))) :
              (sharpChartCyclotomicRing (Nat.card H))ˣ) :
                sharpChartCyclotomicRing (Nat.card H))) ∧
      (∀ r : sharpChartCyclotomicRing (Nat.card H), θ (MonoidAlgebra.single 1 r) = c r) ∧
      (∀ q : X.logStructure.characteristic t,
        θ (MonoidAlgebra.single q 1) = X.logStructure.alpha.app (op W) (β q)) ∧
      ∀ (h : H) (f : MonoidAlgebra (sharpChartCyclotomicRing (Nat.card H))
        (X.logStructure.characteristic t)), θ (d h f) = (b h).hom.appTop (θ f) := by
  sorry

end AlgebraicGeometry
