/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier

/-! # Coefficient reduction of supported pro-etale Tate arrows

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier/
lem-amb-cartier-kummer-map.proof.md, coefficient-extension clause in the final paragraph
(blueprint: def-amb-proetale-supported-coefficient-reduction).

## Main definitions

* `CartierKummerFamily`: degree-two supported arrows into the original finite Tate line.
* `cartierCoefficientReduction`: the actual quotient factor for all positive levels.
* `IsCartierDerivedScalarUnit`: the unbounded derived scalar-unit universal property.
* `CartierKummerReduction`: scalar-normalized reduction compatibility of such a family.

These are definitions of an arrow space and a compatibility predicate, with no
existence assertion for a Kummer class and no chosen map or resolution.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

open Scheme

/-- Reuse the existing left-exact sheafification at each pro-etale module site.
This named instance caches search; its value is the existing instance proof.
Source: Stacks 00WX (blueprint: def-amb-proetale-supported-coefficient-reduction). -/
instance cartierHasSheafifyPro (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : HasSheafify (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  inferInstance

/-- Cache the existing weak pro-etale sheafification separately from left exactness.
Source: Stacks 00WX (blueprint: def-amb-proetale-supported-coefficient-reduction). -/
instance cartierHasWeakSheafifyPro (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : HasWeakSheafify (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  inferInstance

/-- Name the existing abelian structure to share its elaboration across Ext expressions.
Source: Stacks 03D0 (blueprint: def-amb-proetale-supported-coefficient-reduction). -/
instance cartierAbelianPro (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Abelian (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  inferInstance

/-- Cache the existing small Ext instance without changing its universe or category.
Source: Stacks 07A6 (blueprint: def-amb-proetale-supported-coefficient-reduction). -/
instance cartierHasExtPro (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  inferInstance

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual closed-support source, in fixed constant scalars.
Source: Stacks 0A45 and 09A5 (blueprint: def-amb-proetale-supported-coefficient-reduction). -/
@[irreducible]
def cartierSupported (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
    ((constantSheaf (Scheme.ProEt.topology D)
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n))).obj
        (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n)))

/-- The constant generator on the base change of a pro-etale object to the divisor.
Source: the canonical supported constant sheaf, Stacks 09A5
(blueprint: def-amb-proetale-supported-coefficient-reduction). -/
def cartierSupportedGenerator (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T)
    (U : T.ProEtᵒᵖ) (a : finiteTateCoefficient l E n) :
    (cartierSupported l E n i).obj.obj U := by
  unfold cartierSupported
  exact (toSheafify (Scheme.ProEt.topology D)
    ((Functor.const D.ProEtᵒᵖ).obj
      (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n)))).app
        ((Scheme.proEtaleBaseChange i).op.obj U) a

/-- The supported restriction A_T to i_* A_D is the constant-section map.
Source: Stacks 0A45 and 09A5 (blueprint: def-amb-proetale-supported-coefficient-reduction). -/
@[irreducible]
def cartierSupportedUnit (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T) :
    (constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n))).obj
        (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n)) ⟶
      cartierSupported l E n i := by
  unfold cartierSupported
  exact Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
    (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n))

/-- A simultaneous family of the asserted supported degree-two arrows.
Source: blueprint, statement (blueprint: def-amb-proetale-supported-coefficient-reduction). -/
def CartierKummerFamily : Type (u + 1) :=
  ∀ (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hT : IsUnit (l : Γ(T, ⊤))),
    Ext (cartierSupported l E n i) (finiteTateProSheaf l E n T 1) 2

/-- The canonical quotient A_{E,b+1} to A_{E,a+1}, for every a ≤ b.
Source: proof, coefficient reduction
(blueprint: def-amb-proetale-supported-coefficient-reduction). -/
def cartierCoefficientReduction (a b : ℕ) (h : a ≤ b) :
    finiteTateCoefficient l E b →+* finiteTateCoefficient l E a :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).comp
      ULift.ringEquiv.toRingHom)

/-- A derived coefficient unit on the pro-etale site, characterized on all unbounded
objects. This spells out tensor extension without assuming quotient flatness.
Source: Stacks 07A6; proof, scalar extension
(blueprint: def-amb-proetale-supported-coefficient-reduction). -/
@[irreducible]
def IsCartierDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj G) : Prop :=
  ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S)),
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ K ↦
      (DerivedCategory.singleFunctor _ 0).map η ≫
        ((Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategorySingleFunctor
          0).inv.app G ≫
            (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategory.map f)

/-- The pro-etale reduction equation; the coefficient maps preserve constants and
send x tensor b to x tensor bar(b) in the published finite twists.
Source: proof, coefficient reductions
(blueprint: def-amb-proetale-supported-coefficient-reduction). -/
@[irreducible]
def CartierKummerReduction (c : CartierKummerFamily l E) : Prop :=
  ∀ (a b : ℕ) (hab : a ≤ b) {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    ∃ (η : cartierSupported l E b i ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology T)
          (cartierCoefficientReduction l E a b hab)).obj (cartierSupported l E a i))
      (θ : finiteTateProSheaf l E b T 1 ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology T)
          (cartierCoefficientReduction l E a b hab)).obj (finiteTateProSheaf l E a T 1)),
      (∀ (U : T.ProEtᵒᵖ) (z : finiteTateCoefficient l E b),
        η.hom.app U (cartierSupportedGenerator l E b i U z) =
          cartierSupportedGenerator l E a i U (cartierCoefficientReduction l E a b hab z)) ∧
      (∀ (U : T.ProEtᵒᵖ) (z : finiteTateCoefficient l E b)
          (x : (Scheme.purTwistZlOne T l).obj.obj U),
        θ.hom.app U (finiteTateProGenerator l E b T U z x) =
          finiteTateProGenerator l E a T U (cartierCoefficientReduction l E a b hab z) x) ∧
      IsCartierDerivedScalarUnit (cartierCoefficientReduction l E a b hab) T
        (cartierSupported l E b i) (cartierSupported l E a i)
        η ∧
      IsCartierDerivedScalarUnit (cartierCoefficientReduction l E a b hab) T
        (finiteTateProSheaf l E b T 1) (finiteTateProSheaf l E a T 1) θ ∧
      (Ext.mk₀ η).comp
          ((c a i hI hT).mapExactFunctor
            (Sheaf.restrictScalars (Scheme.ProEt.topology T)
              (cartierCoefficientReduction l E a b hab))) (zero_add 2) =
        (c b i hI hT).comp (Ext.mk₀ θ) (add_zero 2)

end AlgebraicGeometry.Etale
