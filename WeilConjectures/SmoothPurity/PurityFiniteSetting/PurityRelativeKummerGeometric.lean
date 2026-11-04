/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerArbitraryBaseMaps
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerAssembly

/-! Geometric stalk calculations for the relative affine-line Kummer theorem. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The normalized affine-line Kummer calculation on every geometric fibre of a base scheme.
Source: blueprint prop-pur-gm-relative-kummer, Step 1 and Step 2 (geometric stalks)
(blueprint: lem-pur-relative-kummer-geometric-stalks).

Proof: let Omega be algebraically closed with k-structure s ≫ p. By
lem-pur-relative-kummer-coefficient-normalization, A is finite free over Z/ell^N and the twist
is trivialized naturally by a primitive root zeta, compatibly with the pullback maps.
thm-pur-kummer-affine-line over the algebraically closed field gives: the affine line has
cohomology A in degree 0 only (by p^*), the punctured line has H^0 = A(1) by restriction,
H^1 free of rank one on kappa(t) (Kummer sequence, Pic = 0, Omega^x divisible) and no
cohomology in degrees >= 2 (affine curve). lem-pur-relative-kummer-strict-local-invariance
and lem-pur-relative-kummer-normalized-stalks identify these with the relative units,
Kummer edge section and higher cohomology sheaves over Spec Omega, which are the clauses of
`RelativeKummerConclusions`. In Lean this is the case B = Spec Omega of
`relative_kummer_arbitrary_base_maps`, completed by `relativeKummerConclusions_of_maps`. -/
theorem relative_kummer_geometric_stalk_conclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (B : Scheme.{u})
    (p : B ⟶ Spec (CommRingCat.of P.field.k)) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ B),
      P.RelativeKummerConclusions h (Spec (CommRingCat.of Ω))
        (s ≫ p) := by
  intro Ω _ _ s
  obtain ⟨hu, ht, hzero, hgen, hvan⟩ :=
    relative_kummer_arbitrary_base_maps P h (Spec (CommRingCat.of Ω)) (s ≫ p)
  exact P.relativeKummerConclusions_of_maps h _ (s ≫ p) hu ht hzero hgen hvan

end WeilConjectures.PurityFiniteSetting
