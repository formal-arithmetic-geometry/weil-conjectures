/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.AffineConormalSections

/-! # Affine comparison for the canonical conormal base-change map

Source: Stacks Project, Morphisms, Lemma 0473, affine reduction, and
Schemes, Lemma 01JU (1)
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-base-change-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- On compatible affine ambient charts, the canonical conormal map is conjugate,
as a function on sections, to `Ideal.tensorCotangentHom`. No surjectivity or
injectivity is asserted here.

Source: Stacks Project, Morphisms, Lemma 0473, affine reduction; Schemes,
Lemma 01JU (1), the ideal of a base-changed closed immersion.
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-base-change-comparison).

Proof: Write A = Γ(X', U') and B = Γ(X, U), and let J be the ideal of i' on U'.
The inverse image of U' under i' is Spec(A/J), by the affine closed-immersion
criterion. Restrict the cartesian square to U and U', using open-preimage
pullbacks and cartesian-square pasting. The quotient base-change calculation
identifies i⁻¹(U) with Spec(B/JB), and its immersion ideal with JB.
The affine conormal sections equivalence identifies the conormal on i'⁻¹(U')
with J/J². The affine pullback sections equivalence identifies the source on
i⁻¹(U) with (B/JB) ⊗[A/J] (J/J²). Since J annihilates J/J², the quotient
scalar tensor equivalence identifies this with B ⊗[A] (J/J²).
The multiplication equivalence B ⊗[A] A ≃ B carries the extended ideal
J.map(includeRight) to JB, and induces an equivalence on the cotangent
quotients. Compose its inverse with the target affine conormal sections
equivalence to obtain the second displayed equivalence.
The canonical-map equation in closedImmersion_conormal_functorial sends the
class of a ∈ J, multiplied by b ∈ B, to the class of b times the image of a.
This agrees with tensorCotangentHom_tmul. These classes generate the source
by the affine pullback sections equivalence; tensor induction proves the
commutation equation for every section. -/
theorem closedImmersion_conormal_affine_base_change_comparison
    {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (c : (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules) ⟶
      (tensorPullback i).obj i.ker.toModules)
    (hcanonical : c = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2))
    (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1) :
    letI : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
    ∃ (eS : Γ((tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules),
          i ⁻¹ᵁ U.1) ≃
        Γ(X, U.1) ⊗[Γ(X', U'.1)] (i'.ker.ideal U').Cotangent)
      (eT : Γ((tensorPullback i).obj i.ker.toModules, i ⁻¹ᵁ U.1) ≃
        ((i'.ker.ideal U').map (Algebra.TensorProduct.includeRight.toRingHom :
          Γ(X', U'.1) →+* Γ(X, U.1) ⊗[Γ(X', U'.1)] Γ(X', U'.1))).Cotangent),
      ∀ s, eT (c.app (i ⁻¹ᵁ U.1) s) =
        (i'.ker.ideal U').tensorCotangentHom Γ(X', U'.1) Γ(X, U.1) (eS s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
