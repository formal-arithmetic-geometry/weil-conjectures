/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Common-stage descent of finitely many equations between morphisms

Source: Stacks Project, Limits, Tag 01ZM, clause (3).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Finitely many equations between maps of finite-presentation models, true over an
affine-transition qcqs inverse limit, are true after one common base change.

Source: Stacks Project, Limits, Tag 01ZM, clause (3), with common refinement.
(blueprint: lem-weil-pbc-finite-presentation-equalities-descent)

Proof: Apply 01ZM(3) to each equation. A cone over the finite family of refinement
arrows has one map to the original stage. Precompose each descended equality with
the pullback map induced by this cone. Projection identities and functoriality identify
its two sides with the two maps at the common stage. This includes empty families.
-/
theorem exists_finitePresentation_equalities_stage
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {κ : Type v} [Finite κ] (V W : κ → Scheme.{u})
    (pV : ∀ a, V a ⟶ D.obj i) (pW : ∀ a, W a ⟶ D.obj i)
    [∀ a, LocallyOfFinitePresentation (pV a)] [∀ a, QuasiCompact (pV a)]
    [∀ a, QuasiSeparated (pV a)]
    [∀ a, LocallyOfFinitePresentation (pW a)] [∀ a, QuasiCompact (pW a)]
    [∀ a, QuasiSeparated (pW a)]
    (ψ χ : ∀ a, V a ⟶ W a)
    (hψ : ∀ a, ψ a ≫ pW a = pV a) (hχ : ∀ a, χ a ≫ pW a = pV a)
    (heq : ∀ a, pullback.fst (pV a) (c.π.app i) ≫ ψ a =
      pullback.fst (pV a) (c.π.app i) ≫ χ a) :
    ∃ (j : I) (f : j ⟶ i), ∀ a,
      pullback.fst (pV a) (D.map f) ≫ ψ a = pullback.fst (pV a) (D.map f) ≫ χ a := by
  classical
  have hex (a : κ) := Scheme.exists_pullback_fst_comp_eq_of_isLimit hc
    (pV a) (pW a) (ψ a) (χ a) (hψ a) (hχ a) (heq a)
  choose k b hb using hex
  obtain ⟨j, f, m, hm⟩ := IsCofiltered.wideCospan b
  let M (a : κ) := pullback.map (pV a) (D.map f) (pV a) (D.map (b a))
    (𝟙 _) (D.map (m a)) (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← D.map_comp]
      exact congrArg D.map (hm a).symm)
  refine ⟨j, f, fun a ↦ ?_⟩
  have h := congrArg (fun z ↦ M a ≫ z) (hb a)
  simpa [← Category.assoc, M] using h

end AlgebraicGeometry
