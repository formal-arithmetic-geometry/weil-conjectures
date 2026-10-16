/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-!
# A finite test for vanishing after pullback from an affine open

Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01I9 and 01IA;
Sheaves, Tag 0097.
(blueprint: lem-pc-affine-finite-type-pullback-zero-test).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite family of sections on an affine open tests vanishing after every pullback.
Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01I9 and 01IA;
Sheaves, Tag 0097.
(blueprint: lem-pc-affine-finite-type-pullback-zero-test).

Proof: finite type and quasi-coherence imply that F(V) is a finite module over O(V).
Choose a finite spanning family. For any g, naturality of its pullback adjunction unit
identifies the image of each pulled-back generator with the pullback of its image
under δ. Hence the hypothesis kills all generators. On any affine open A contained
in g⁻¹(V), the affine pullback-sections comparison identifies sections of g*F with
F(V) tensor O(A); pure tensors of the spanning family generate this module. The
pulled-back map therefore vanishes on A. Affine opens contained in an arbitrary
W cover W. Naturality of δ with respect to restriction, followed by separatedness
of the target sheaf, implies its component on W is zero. No finiteness assumption
on G or g is required. An empty spanning family covers the zero module, and the
empty affine open causes no exception. -/
theorem exists_affine_finiteType_pullback_zero_test
    {Y : Scheme.{u}} (F : Y.Modules) (hF_ft : F.IsFiniteType)
    (hF_qc : F.IsQuasicoherent) (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ s : Finset Γ(F, V),
      ∀ (G : Y.Modules) (_hG_qc : G.IsQuasicoherent) (δ : F ⟶ G)
        (X : Scheme.{u}) (g : X ⟶ Y),
        (∀ x ∈ s, ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
          (op V) (δ.app V x) = 0) →
        ∀ (W : X.Opens), W ≤ g ⁻¹ᵁ V → ((tensorPullback g).map δ).app W = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
