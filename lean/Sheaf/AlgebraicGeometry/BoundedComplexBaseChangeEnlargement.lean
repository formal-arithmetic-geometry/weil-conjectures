/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.TensorPullbackFinitePresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Homology.Functor

/-! # Enlarging a bounded finitely presented complex along base change

Source: Stacks Project, Tags 0095, 0097, 01ZR and 01ZM.
-/

@[expose] public section


universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Pull back a fixed bounded finitely presented complex, preserving its termwise
identification and the comparison with any further base change.
Source: Stacks Project, sheaves.tex, Tags 0095 and 0097; limits.tex, Tags 01ZR and 01ZM.
(blueprint: lem-pc-bounded-complex-base-change-enlargement).

Proof: let F be moduleBaseChange f g. Tensor pullback is additive, since it is a left
adjoint between abelian categories. Apply F degreewise to H and its differentials to
construct K; preservation of zero morphisms proves d squared is zero. The terms of K
are the pulled-back terms, so q is the identity family. Pullback preserves finite
presentation: restrict each local finite free presentation to the inverse-image open,
apply the right exact pullback functor, and identify pullbacks of finite free modules
with finite free modules. Pullback takes zero modules to zero modules, hence K has the
same bounded range as H. Finally baseChangeMap respects composition and tensor
pullback of a composite is naturally isomorphic to successive tensor pullback (0097).
Apply this natural isomorphism to every term of H to obtain e. Its naturality on every
differential is exactly the final equation. The construction is valid for empty
schemes and for the zero complex, and makes no flatness or limit-descent assertion. -/
theorem exists_bounded_complex_baseChange_enlargement
    {X S : Scheme.{u}} (f : X ⟶ S) {T T' T'' : Over S}
    (g : T' ⟶ T) (h : T'' ⟶ T')
    (H : CochainComplex (pullback f T.hom).Modules ℤ)
    (hH_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n))
    (hH_fp : ∀ n : ℤ, (H.X n).IsFinitePresentation) :
    ∃ K : CochainComplex (pullback f T'.hom).Modules ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
      (∀ n : ℤ, (K.X n).IsFinitePresentation) ∧
      (Nonempty (∀ n : ℤ, K.X n ≅ (Scheme.Modules.moduleBaseChange f g).obj (H.X n))) ∧
      ∃ e : ∀ n : ℤ,
        (Scheme.Modules.moduleBaseChange f h).obj (K.X n) ≅
          (Scheme.Modules.moduleBaseChange f (h ≫ g)).obj (H.X n),
        ∀ n m : ℤ,
          (Scheme.Modules.moduleBaseChange f h).map (K.d n m) ≫ (e m).hom =
            (e n).hom ≫ (Scheme.Modules.moduleBaseChange f (h ≫ g)).map (H.d n m) := by
  let F := Scheme.Modules.moduleBaseChange f g
  let : F.IsLeftAdjoint :=
    ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction (baseChangeMap f g)⟩
  let K := (F.mapHomologicalComplex (.up ℤ)).obj H
  obtain ⟨a, b, hab⟩ := hH_bounded
  have hK_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n) :=
    ⟨a, b, fun n hn ↦ F.map_isZero (hab n hn)⟩
  have hK_fp : ∀ n : ℤ, (K.X n).IsFinitePresentation := fun n ↦ by
    let := hH_fp n
    exact Scheme.Modules.isFinitePresentation_tensorPullback (baseChangeMap f g) (H.X n)
  obtain ⟨δ⟩ := Scheme.Modules.nonempty_tensorPullbackComp
    (baseChangeMap f h) (baseChangeMap f g)
  have δ' : Scheme.Modules.moduleBaseChange f (h ≫ g) ≅
      Scheme.Modules.moduleBaseChange f g ⋙ Scheme.Modules.moduleBaseChange f h := by
    exact (eqToIso (congrArg (fun k ↦ Scheme.Modules.tensorPullback k)
      (baseChangeMap_comp f h g))) ≪≫ δ
  refine ⟨K, hK_bounded, hK_fp, ⟨fun n ↦ Iso.refl _⟩,
    fun n ↦ δ'.symm.app (H.X n), ?_⟩
  intro n m
  exact δ'.inv.naturality (H.d n m)

end AlgebraicGeometry
