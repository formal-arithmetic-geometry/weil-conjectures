/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale

/-!
# Kummer log morphisms and strict local standard charts

Source: ILO, Exposé VI 2.1--2.2, printed pp.71--72
(blueprint: def-per-kummer-log-morphism).

The graph of pullback on log stalks is defined directly using section representatives,
so no uncharacterized choice of a stalk homomorphism is needed. Ring pullback in a
strict local chart is characterized on every pointed étale diagram in the same way.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The graph of the canonical map on geometric log stalks. Representatives are related
by the given log morphism on a pointed relative étale diagram. The lift equation says
that the diagram lies over the chosen geometric point. Source: ILO VI 2.1
(blueprint: def-per-kummer-log-morphism). -/
def EtaleLogHom.StalkImage {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (m : Y.logStructure.toEtalePrelogStructure.stalk (t ≫ f.base))
    (n : X.logStructure.toEtalePrelogStructure.stalk t) : Prop :=
  ∃ (W : Y.scheme.Etale) (V : X.scheme.Etale) (k : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ f.base)
    (w : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj W)
    (z : (Scheme.pointSmallEtale t).fiber.obj V),
    z.left ≫ k = w.left ∧
      ∃ s : Y.logStructure.monoidSheaf.obj.obj (op W),
        Y.logStructure.toEtalePrelogStructure.germ (t ≫ f.base) W w s = m ∧
        X.logStructure.toEtalePrelogStructure.germ t V z (f.sectionMap W V k hk s) = n

/-- Kummer on characteristic monoids: injective modulo units, and every target class
has a positive power in the image modulo units. `StalkImage` is the graph of the given
morphism, and `Associated` is equality in the characteristic monoid. Source: ILO VI 2.1
(blueprint: def-per-kummer-log-morphism). -/
def EtaleLogHom.IsKummer {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
    (∀ (m₁ m₂ : Y.logStructure.toEtalePrelogStructure.stalk (t ≫ f.base))
      (n₁ n₂ : X.logStructure.toEtalePrelogStructure.stalk t),
      f.StalkImage t m₁ n₁ → f.StalkImage t m₂ n₂ → Associated n₁ n₂ → Associated m₁ m₂) ∧
    ∀ n : X.logStructure.toEtalePrelogStructure.stalk t,
      ∃ (m : Y.logStructure.toEtalePrelogStructure.stalk (t ≫ f.base))
        (n' : X.logStructure.toEtalePrelogStructure.stalk t) (d : ℕ),
        0 < d ∧ f.StalkImage t m n' ∧ Associated (n ^ d) n'

/-- The graph condition for the actual pullback on strict local rings. It specifies
its values on all geometric germs, hence determines the ring map uniquely. Source:
ILO VI 2.2 (blueprint: def-per-kummer-log-morphism). -/
def EtaleLogHom.IsStrictLocalRingMap {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme)
    (r : strictLocalRing Y.scheme (t ≫ f.base) →+* strictLocalRing X.scheme t) : Prop :=
  ∀ (W : Y.scheme.Etale) (V : X.scheme.Etale) (k : V.left ⟶ W.left)
    (_hk : k ≫ W.hom = V.hom ≫ f.base)
    (w : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj W)
    (z : (Scheme.pointSmallEtale t).fiber.obj V), z.left ≫ k = w.left →
    ∀ s : Γ(W.left, ⊤),
      r (strictLocalGerm Y.scheme (t ≫ f.base) W w s) =
        strictLocalGerm X.scheme t V z (k.appTop s)

/-- A strict local standard Kummer chart consists of actual stalk charts, the given
pullbacks on log germs and on rings, and a cartesian square of spectra of monoid rings.
The group cokernel is finite and killed by one positive integer invertible on the
strict local base. Multiplicative powers express the additive multiple condition.
Source: ILO VI 2.2, printed p.72 (blueprint: def-per-kummer-log-morphism). -/
def EtaleLogHom.HasStrictLocalKummerChart {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme) : Prop :=
  ∃ (P Q : Type u) (_ : CommMonoid P) (_ : CommMonoid Q)
    (a : P →* Y.logStructure.toEtalePrelogStructure.stalk (t ≫ f.base))
    (b : Q →* X.logStructure.toEtalePrelogStructure.stalk t) (h : P →* Q)
    (r : strictLocalRing Y.scheme (t ≫ f.base) →+* strictLocalRing X.scheme t),
    IsFineSaturatedMonoid P ∧ IsFineSaturatedMonoid Q ∧
    Y.logStructure.IsStalkChart (t ≫ f.base) a ∧ X.logStructure.IsStalkChart t b ∧
    (∀ p : P, f.StalkImage t (a p) (b (h p))) ∧ f.IsStrictLocalRingMap t r ∧
    Function.Injective h ∧ (∀ q : Q, ∃ (d : ℕ) (p : P), 0 < d ∧ q ^ d = h p) ∧
    (∃ d : ℕ, 0 < d ∧ IsUnit (d : strictLocalRing Y.scheme (t ≫ f.base)) ∧
      Finite (Algebra.GrothendieckGroup Q ⧸
        (Algebra.GrothendieckGroup.lift
          ((Algebra.GrothendieckGroup.of (M := Q)).comp h)).range) ∧
      ∀ c : Algebra.GrothendieckGroup Q ⧸
        (Algebra.GrothendieckGroup.lift
          ((Algebra.GrothendieckGroup.of (M := Q)).comp h)).range, c ^ d = 1) ∧
    IsPullback (Spec.map (CommRingCat.ofHom r))
      (Spec.map (CommRingCat.ofHom
        (MonoidAlgebra.lift ℤ (strictLocalRing X.scheme t) Q
          ((X.logStructure.toEtalePrelogStructure.stalkAlpha t).comp b)).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (MonoidAlgebra.lift ℤ (strictLocalRing Y.scheme (t ≫ f.base)) P
          ((Y.logStructure.toEtalePrelogStructure.stalkAlpha (t ≫ f.base)).comp a)).toRingHom))
      (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ h)))

end AlgebraicGeometry
