/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Invertible sheaves on affine space over a field

Source: Stacks Project, Tag 0BDA, `lemma-open-subscheme-UFD`, clause (2), with the
base ring a field and the open equal to the whole affine space
(blueprint: lem-sfb-affine-space-invertible-trivial).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Every invertible module sheaf on affine `n`-space over a field is trivial.

Source: Stacks Project, Tag 0BDA, `lemma-open-subscheme-UFD`, clause (2), with `R = k`
and the whole affine space (blueprint: lem-sfb-affine-space-invertible-trivial).

Proof: The coordinate ring is a UFD, as is its isomorphic ring of global sections.
The global sections of `M` form an invertible module over this ring. Its Picard group
is trivial, giving a linear equivalence with the ring. The inverse image of `1`
is a basis of global sections and hence, by the affine free-generator criterion,
a free sheaf generator. Multiplication by this generator defines the required
isomorphism from the structure sheaf to `M`. -/
theorem nonempty_iso_unit_of_mvPolynomial_field (k : Type u) [Field k] (n : ℕ)
    (M : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).Modules) [M.IsInvertible] :
    Nonempty (M ≅ Scheme.Modules.unit (Spec (CommRingCat.of (MvPolynomial (Fin n) k)))) := by
  let A := MvPolynomial (Fin n) k
  let X := Spec (CommRingCat.of A)
  let eA := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(X, ⊤) := eA.toMulEquiv.isDomain A
  have : UniqueFactorizationMonoid Γ(X, ⊤) :=
    eA.toMulEquiv.symm.uniqueFactorizationMonoid inferInstance
  have : IsGCDMonoid Γ(X, ⊤) := ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  have := invertible_sections_of_isAffineOpen M (isAffineOpen_top X)
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free Γ(X, ⊤) Γ(M, ⊤))
  have he : Function.Bijective (fun r : Γ(X, ⊤) ↦ r • e.symm 1) := by
    convert e.symm.bijective using 1
    funext r
    rw [← e.symm.map_smul, smul_eq_mul, mul_one]
  have hg := isFreeGenerator_of_bijective_smul M (isAffineOpen_top X) he
  let σ : M.sections := PresheafOfModules.sectionsMk
    (fun U ↦ M.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op (e.symm 1))
    (fun U V f ↦ by
      change M.presheaf.map f.unop.op (M.presheaf.map _ (e.symm 1)) = _
      rw [presheaf_map_map_apply]
      rfl)
  let φ := M.unitHomEquiv.symm σ
  have : IsIso φ := by
    have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map φ) := by
      refine (NatTrans.isIso_iff_isIso_app _).2 fun U ↦ ?_
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hg U.unop le_top
    exact isIso_of_reflects_iso φ
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry.Scheme.Modules
