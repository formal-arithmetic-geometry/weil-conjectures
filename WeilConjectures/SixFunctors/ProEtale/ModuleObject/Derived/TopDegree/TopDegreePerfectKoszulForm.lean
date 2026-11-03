/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeScalarRealization

/-! # The specified perfect trace-cup Koszul form

Source: sk-cor-trace, steps 11--12.
(blueprint: lem-pd-perfect-trace-cup-koszul-form).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
open PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The specified perfect trace-cup Koszul form.
Source: sk-cor-trace, steps 11--12 (blueprint: lem-pd-perfect-trace-cup-koszul-form).

Proof in words.
Use derivedDuality at the actual regular unit and the identity coefficient encoding.
Its coefficient dual is the unit by the right-unitor tensor-Hom adjunction. Compare
its exact scalar realization (over condensedScalarRing) with TraceCupPoint.fiber
(over Gamma Lambda) through the now explicit scalarRealizationComparison, constructed from
sectionGlobalEquiv of the terminal profinite object,
including linear actions and the regular unit. The normalized pure-tensor and
localization squares identify both point cup maps. The identification theorem's
counit equation identifies the smooth orientation with smoothAdjunction.trace;
its proper comparison is the same canonical proper coincidence. Evaluate its
inverse-line pairing on every positive Tate-line section and use the inverse
root-line evaluation to identify its value with Value. This identifies its
bilinear form with pairing, so the two adjoint bijections transport literally.
For symmetry, take the ordinary adjoint of the lax tensor map: after the strong
pullback tensor comparison it is tensor of the two ordinary counits. Braiding
naturality and the pullback braided comparison identify its swapped transpose,
so adjunction injectivity proves the ordinary cup symmetry. On shifted
representatives the signed chain tensor interchange contributes (-1)^(i*j);
transport through K-flat localization and the specified shiftTensorShiftIso.
Point tensor, proper coincidence, the unit multiplication and scalar classEquiv
preserve this equation. Put j=2*d-i; the already proved field-sign assembly gives
all remaining complementary/middle signs and characteristic-zero alternation.
-/
theorem perfect_trace_cup_koszul_form {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∀ _hF : IsField (CategoryTheory.MonObj.Γ (c.obj.{u} ell)),
      (∀ i : ℤ, ∃ b : H ell c X i →ₗ[CategoryTheory.MonObj.Γ (c.obj.{u} ell)]
          H ell c X (2 * (d : ℤ) - i) →ₗ[CategoryTheory.MonObj.Γ (c.obj.{u} ell)]
            Value ell c k d,
        (∀ x y, b x y = pairing ell c hEll X d i x y) ∧
          Function.Bijective b ∧ Function.Bijective b.flip) ∧
      (∀ (i : ℤ) (x : H ell c X i) (y : H ell c X (2 * (d : ℤ) - i)),
        pairing ell c hEll X d (2 * (d : ℤ) - i) y
            ((eqToHom (congrArg (H ell c X) (by omega : i = 2 * (d : ℤ) -
              (2 * (d : ℤ) - i)))) x) =
          sign (i * (2 * (d : ℤ) - i)) • pairing ell c hEll X d i x y) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
