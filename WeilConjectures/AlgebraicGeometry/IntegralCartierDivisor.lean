/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-! # Cartier divisors by local rational equations on integral schemes

Source: Stacks Project, Divisors, Tag 01X5, rational functions and sections; the local Cartier
definition in
lem-sfb-normal-group-vertical-cartier-descent
(blueprint: def-sfb-integral-cartier-divisor).

A germ class is represented by its coset of regular units inside the function field.
Locally representable functions into these cosets are sections of K×/O×. In particular,
no choice of an open cover, or of equations on it, remains part of a divisor.
The partial pullback tests actual local fractions, including for nondominant morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The class of f modulo units of the local ring, realized as its coset in K(X).
Source: the parent node's local Cartier definition; Stacks, Tag 01X5
(blueprint: def-sfb-integral-cartier-divisor). -/
def integralCartierClass (X : Scheme.{u}) [IsIntegral X] (x : X)
    (f : X.functionField) : Set X.functionField :=
  {g | ∃ a : (X.presheaf.stalk x)ˣ,
    g = f * algebraMap (X.presheaf.stalk x) X.functionField a.val}

/-- A Cartier divisor is a locally representable section of the stalk cosets K×/O×.
Its equations are nonzero rational functions; equality is equality of all germ classes.
Source: the parent node's local Cartier definition; Stacks, Tag 01X5
(blueprint: def-sfb-integral-cartier-divisor). -/
def IntegralCartierDivisor (X : Scheme.{u}) [IsIntegral X] :=
  {d : X → Set X.functionField // ∀ x : X,
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : X.functionField, f ≠ 0 ∧
      ∀ y : X, y ∈ U → d y = integralCartierClass X y f}

/-- The zero divisor has the unit equation 1 on the whole scheme.
Source: the parent node's local Cartier definition; Stacks, Tag 01X5
(blueprint: def-sfb-integral-cartier-divisor). -/
def integralCartierZero (X : Scheme.{u}) [IsIntegral X] : IntegralCartierDivisor X :=
  ⟨fun x ↦ integralCartierClass X x 1,
    fun _ ↦ ⟨⊤, trivial, 1, one_ne_zero, fun _ _ ↦ rfl⟩⟩

/-- Support is the locus of nonunit Cartier germ classes.
Source: the parent node's local Cartier definition; Stacks, Tag 01X5
(blueprint: def-sfb-integral-cartier-divisor). -/
def integralCartierSupport {X : Scheme.{u}} [IsIntegral X]
    (D : IntegralCartierDivisor X) : Set X :=
  {x | D.val x ≠ integralCartierClass X x 1}

/-- E is the Cartier pullback of D when local fraction equations pull back to its germs.
Both pulled numerator and denominator must be nonzero. Thus this does not assert that
an arbitrary rational function restricts along a nondominant morphism.
Source: the parent node's local Cartier pullback; Stacks, Tag 01X5
(blueprint: def-sfb-integral-cartier-divisor). -/
def IsIntegralCartierPullback {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (D : IntegralCartierDivisor Y) (E : IntegralCartierDivisor X) : Prop :=
  ∀ x : X, ∃ a b : Y.presheaf.stalk (f x),
    a ≠ 0 ∧ b ≠ 0 ∧ (f.stalkMap x) a ≠ 0 ∧ (f.stalkMap x) b ≠ 0 ∧
    D.val (f x) = integralCartierClass Y (f x)
      (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a /
        algebraMap (Y.presheaf.stalk (f x)) Y.functionField b) ∧
    E.val x = integralCartierClass X x
      (algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x) a) /
        algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x) b))

/-- The canonical partial Cartier pullback, selected only when uniquely determined by
pulling back actual equations. This definition contains no postponed data or proof.
Source: the parent node's local Cartier definition; Stacks, Tag 01X5
(blueprint: def-sfb-integral-cartier-divisor). -/
def integralCartierPullback? {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (D : IntegralCartierDivisor Y) : Option (IntegralCartierDivisor X) := by
  classical
  exact if h : ∃! E : IntegralCartierDivisor X, IsIntegralCartierPullback f D E then
    some (Classical.choose h.exists)
  else none

/-- A rational section has Cartier divisor D if in every regular stalk frame its
nonzero rational coefficient represents the germ of D. One frame at each stalk suffices:
changing a frame multiplies the coefficient by a local regular unit.
Source: Stacks, Tag 01X5, and the parent node's local Cartier definition
(blueprint: def-sfb-integral-cartier-divisor). -/
def HasIntegralCartierDivisor {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    (s : ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint X)))
    (D : IntegralCartierDivisor X) : Prop :=
  ∀ x : X, ∃ t : ↑(TopCat.Presheaf.stalk L.val.presheaf x),
    Submodule.span (X.presheaf.stalk x) {t} = ⊤ ∧
      ∃ a : X.functionField, a ≠ 0 ∧
        s = a • TopCat.Presheaf.stalkSpecializes L.val.presheaf
          ((genericPoint_spec X).specializes (Set.mem_univ x)) t ∧
        D.val x = integralCartierClass X x a

/-- The rational section extends to a regular section generating the line at every point.
The global section, its generic germ and all its stalk generators are specified literally.
Source: Stacks, Tag 01X5 (blueprint: def-sfb-integral-cartier-divisor). -/
def IsInvertibleRegularRationalSection {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    (s : ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint X))) : Prop :=
  ∃ t : Γ(L, ⊤), TopCat.Presheaf.germ L.val.presheaf ⊤ (genericPoint X) trivial t = s ∧
    ∀ x : X, Submodule.span (X.presheaf.stalk x)
      {TopCat.Presheaf.germ L.val.presheaf ⊤ x trivial t} = ⊤

end AlgebraicGeometry.Scheme
