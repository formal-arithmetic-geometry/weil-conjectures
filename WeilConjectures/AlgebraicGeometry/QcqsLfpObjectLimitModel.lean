/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Qcqs locally finitely presented objects over affine-transition limits

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 2722](https://stacks.math.columbia.edu/tag/2722)
* [Stacks Project, Tag 2810](https://stacks.math.columbia.edu/tag/2810)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A qcqs scheme locally of finite presentation over a limit with affine transitions
has a model at one stage, without hypotheses on the stages or on the limit. -/
theorem exists_qcqs_lfp_object_limit_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] :
    ∃ (i : I) (X_i : Scheme.{u}) (f_i : X_i ⟶ D.obj (op i)),
      CompactSpace X_i ∧ QuasiSeparatedSpace X_i ∧
        LocallyOfFinitePresentation f_i ∧
        ∃ (e : X ≅ pullback (C := Scheme.{u}) f_i (c.π.app (op i))),
          e.hom ≫ pullback.snd f_i (c.π.app (op i)) = f := by
  classical
  let i0 : I := Classical.choice (inferInstance : Nonempty I)
  let i₀ : Iᵒᵖ := op i0
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_affineOpens_le_preimage (f ≫ c.π.app i₀)).exists_finite_of_isCompact
      (U := ⊤) (by simpa using isCompact_univ)
  have H := descendsToStage_finsetSup (D := D) hc (i₀ := i₀) f hUsfin.toFinset
    (fun W hW ↦ hUsB (hUsfin.mem_toFinset.mp hW))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at H
  replace H := DescendsToStage.comp_iso (D := D) (c := c) X.topIso.symm H
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at H
  obtain ⟨i, X_i, f_i, h, hf_i, hcompact, hqs, hsq⟩ := H
  refine ⟨i.unop, X_i, f_i, hcompact, hqs, hf_i, hsq.isoPullback, ?_⟩
  exact IsPullback.isoPullback_hom_snd hsq

end AlgebraicGeometry
