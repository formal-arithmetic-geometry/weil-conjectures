/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.Algebra.FinitePresentationColimit

/-! # A bounded free complex on an affine neighbourhood of a stalk

Source: Stacks Project, Tags 0BCD, 0BC7 and 00CR, finite-matrix spreading.
(blueprint: lem-sc-bounded-free-stalk-complex-local-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Ordinary direct image on an open preserves zero morphisms sectionwise.
Source: the definition of module direct image in the direct-image step of
lem-sc-bounded-free-stalk-complex-local-lift. -/
instance openModuleDirectImage_preservesZeroMorphisms (X : Scheme.{u}) (U : X.Opens) :
    Functor.PreservesZeroMorphisms (SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)) where
  map_zero M N := by
    ext V m
    rfl

/-- The affine-local part of bounded free stalk-complex lifting.

Source: Stacks Project, Tags 0BCD and 0BC7 (finite-presentation spreading),
and Algebra Tag 00CR. The stalk of a sheaf on the open is expressed using ordinary
open direct image followed by the ambient stalk functor; no global boundedness or
restriction comparison is asserted here.
(blueprint: lem-sc-bounded-free-stalk-complex-local-lift).

Proof:
1. Use hterms to identify every term with its standard rank-d i free module.
   Express each differential in the standard bases. The hypothesis hd makes all
   ranks zero outside [a,b], so only finitely many matrices have any entries.
2. Choose an affine neighbourhood V of x. Its stalk is the localization of its
   section ring at the prime corresponding to x. Every entry of the finitely many
   matrices is a fraction with denominator outside that prime. Multiply these
   denominators to obtain a principal affine neighbourhood where all entries lift.
3. Each composite of consecutive matrices has zero germ. Every one of its finitely
   many entries therefore vanishes after multiplication by an element outside the
   prime. Shrink again using the product of these elements. The lifted matrices
   now square to zero, and define the differentials between the rank-d i free
   sheaves on the resulting affine open U. Outside [a,b] take the zero differentials;
   rank zero gives zero sheaves there, so the resulting complex L is bounded.
4. The stalks of finite free sheaves have their standard finite bases. The chosen
   bases of F identify them with these stalks and commute with the differentials
   by the definition of the lifted matrices, giving an isomorphism of complexes.
   In the ambient direct image, neighbourhoods contained in U are cofinal at x;
   this identifies that stalk with the local one, compatibly with scalar action
   and differentials, and yields the displayed isomorphism.
For an empty degree interval every rank is zero, so there are no coefficients or
relations to lift. No point exists on an empty scheme; rank-zero terms introduce
no coefficients. Nothing assumes that the open immersion is quasi-compact.
-/
theorem exists_boundedFree_stalk_complex_local_lift
    (X : Scheme.{u}) (x : X) (d : ℤ → ℕ)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (hterms : ∀ i : ℤ, F.X i = ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x)))
    (a b : ℤ) (hd : ∀ i : ℤ, i < a ∨ b < i → d i = 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ L : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∀ i : ℤ, i < a ∨ b < i → IsZero (L.X i)) ∧
        (∀ i : ℤ, Nonempty (L.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin (d i))))) ∧
        Nonempty (F ≅
          (((SheafOfModules.pushforward.{u}
              (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U) ⋙
            RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)) := by sorry

end
end AlgebraicGeometry.Scheme
