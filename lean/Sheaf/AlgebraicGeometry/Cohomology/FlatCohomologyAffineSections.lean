/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Canonical base change of sections on an affine open

Source: Stacks Project, Tags 02KG and 02KH.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}}

/-- Base change of sections on one affine open, with its canonical pure-tensor formula.
Source: Stacks Project, Tag 02KG, used in the separated-case proof of Tag 02KH.
(blueprint: lem-pc-flat-affine-base-change-sections)

Proof: The inverse image of W is the fibre product of W with Spec S over Spec R,
hence affine. Its ring of sections is S tensor_R Gamma(W, O_X), by the affine
cartesian ring formula. Apply exists_tensorPullback_affine_sections to W and its
inverse image. Uniqueness of left adjoints identifies tensorPullback with pullback;
the conjugate-isomorphism unit equation preserves the pure-tensor formula.
Tensor associativity then identifies the sections with S tensor_R Gamma(W, M).
Transport through W' = g inverse W and restrict the unit along h. The resulting
S-linear equivalence sends b tensor s to the restricted scalar b times the
restricted adjunction unit of s. This works for the empty affine open as well:
both section modules are zero and the same canonical formula holds. -/
theorem exists_baseChange_affine_section_equiv (f : X ⟶ Spec (.of R))
    (W : X.Opens) (hW : IsAffineOpen W) (M : X.Modules) [M.IsQuasicoherent]
    (W' : (baseChangedScheme (S := S) f).Opens)
    (hW' : W' = baseChangeFst (S := S) f ⁻¹ᵁ W)
    (h : W' ≤ baseChangeFst (S := S) f ⁻¹ᵁ W) :
    let N := baseChangedModule (S := S) f M
    let P := M.presheafModuleCat ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let Q := N.presheafModuleCat ⋙ ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    ∃ e : TensorProduct R S (P.obj (op W)) ≃ₗ[S] Q.obj (op W'),
      ∀ (b : S) (s : P.obj (op W)),
        e (b ⊗ₜ[R] s) =
          ((baseChangedScheme (S := S) f).presheaf.map
            (homOfLE (le_top : W' ≤ ⊤)).op).hom
            (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom b) •
          N.presheaf.map (homOfLE h).op
            ((baseChangeUnit (S := S) f M).val.app (op W) s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
