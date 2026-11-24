/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotientCore

/-! # Sheaf quotients on the finite fibres

## References

* Stacks Project, Tags 02OD and 04CJ
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry

/-- The finite fibre immersion is closed, and its direct image of the pulled-back module
is the quotient of the local pullback by the corresponding power of the extended ideal.
The quotient equation specifies the isomorphism uniquely, since the quotient projection
is an epimorphism. No cohomology or transition compatibility is asserted here.
(Stacks, Tags 02OD and 04CJ (1).) -/
theorem formalFunctions_finite_sheaf_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) :
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
          (pullback.fst (Y.fromSpecStalk y) f)
    ∀ n : ℕ, IsClosedImmersion (formalFunctionsFiniteι f y n) ∧
      ∃ e : formalModuleQuotient J (n + 1) F' ≅
          (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
            ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F),
        formalModuleQuotientπ J (n + 1) F' ≫ e.hom =
          formalFunctionsFiniteFMap f y F n := by
  dsimp
  intro n
  refine ⟨formalFunctionsFiniteι_isClosedImmersion f y n, ?_⟩
  exact formalFunctionsFinite_sheaf_quotient_iso f F y n

end AlgebraicGeometry
