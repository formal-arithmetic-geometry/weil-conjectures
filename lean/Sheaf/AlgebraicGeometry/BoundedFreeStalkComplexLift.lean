/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.Algebra.FinitePresentationColimit

/-! # Lifting the differential matrices of a bounded free stalk complex

Source: Stacks Project, Tags 0BCD and 0BC7, finite presentation argument;
Tag 00CR and the definition of the module direct image.
(blueprint: lem-sc-bounded-free-stalk-complex-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A bounded free stalk complex lifts as a complex, without a prescribed derived object.

Source: Stacks Project, Tags 0BCD and 0BC7, descent of finite presentations and maps,
and Tag 00CR. The final direct image is only an auxiliary global complex.
(blueprint: lem-sc-bounded-free-stalk-complex-lift).

Proof:
1. Fix bounds a,b. The stalk ring is nonzero, since it is local. A zero free module
   over it has rank zero, so hfree implies d i = 0 outside [a,b], including when b < a.
   Choose bases using hfree, and express the differentials as finite matrices. There
   are only finitely many entries and finitely many equations for the square to vanish.
2. Choose an affine neighbourhood of x. Its stalk is the prime localization of its
   section ring, the filtered colimit of principal localizations (Tag 00CR). Lift all
   entries to one principal neighbourhood. Every entry of each differential composite
   has zero germ; shrink to a common later principal neighbourhood where these finitely
   many entries vanish. Equivalently use the maps and equality clauses of finite
   presentation descent. The rank-d i free modules and these matrices now define a
   bounded free sheaf complex L on this affine open U. Its stalk complex is isomorphic
   to F, since the chosen bases conjugate the differentials to their lifted matrices.
3. Define H by the termwise ordinary direct image along U into X: on an open V its
   sections are the sections of L on V intersect U, with scalars restricted from V.
   Direct image is additive and preserves zero objects, so H is bounded. Its restriction
   to U is L. Neighbourhoods contained in U are cofinal at x, so its stalk complex is
   the stalk complex of L. These identifications give the free-term and stalk isomorphisms.
No comparison with another derived object is made. Empty spectra have no x; rank-zero
terms and empty degree intervals require no entries or equations to lift.
-/
theorem exists_boundedFree_stalk_complex_lift
    (X : Scheme.{u}) (x : X) (d : ℤ → ℕ)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i))
    (hfree : ∀ i : ℤ, Nonempty (F.X i ≅ ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x)))) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (H.X i)) ∧
        (∀ i : ℤ, Nonempty
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
            (H.X i) ≅ SheafOfModules.free
              (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin (d i))))) ∧
        Nonempty (F ≅
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj H)) := by sorry

end
end AlgebraicGeometry.Scheme
