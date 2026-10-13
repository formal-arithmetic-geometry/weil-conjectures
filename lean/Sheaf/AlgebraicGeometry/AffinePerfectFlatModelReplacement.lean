/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.AlgebraicGeometry.AffinePerfectSectionsProjectiveModel
import Sheaf.AlgebraicGeometry.AffineProjectiveSectionsSheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Affine perfect replacement with a chain-level comparison -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A bounded-above quasi-coherent complex representing a perfect object on an
affine scheme has a bounded finite-projective replacement mapping quasi-isomorphically
to it. Only the structural properties of the replacement and the comparison map
are asserted; no direct-image or universal cohomology conclusion is asserted.
Source: Stacks Project, Tags 08EB, 0656 and 0647.
(blueprint: lem-pc-affine-perfect-flat-model-replacement).

Proof: Identify Y with Spec Gamma(Y,O). Under the affine derived equivalence the
complex of sections of D corresponds to D, since its quasi-coherent terms are
acyclic for global sections. Tag 08EB transfers perfectness to that ring complex.
Tag 0656 gives a bounded complex P of finite projective modules representing it.
Such a complex is K-projective (Tag 0647), so the derived isomorphism from P to the
section complex is represented by a chain map. This map is a quasi-isomorphism
because its localization is invertible. Associate sheaves termwise and use the
quasi-coherent counit to obtain e : C -> D, still a quasi-isomorphism. The terms
of C are direct summands of finite free modules, hence flat, quasi-coherent and
finitely presented. Transfer P's bounds, enlarging the upper bound to a natural
number. For the empty scheme or a zero complex choose the zero complex and
zero map, which is a quasi-isomorphism in the trivial or acyclic case. The object
C is asserted existentially, never defined by choosing an unproved witness. -/
theorem exists_affine_perfect_flat_model_replacement
    (Y : Scheme.{u}) (hY : IsAffine Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (D : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hDle : D.IsStrictlyLE d)
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (hperfect : Y.IsPerfect ((DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).obj D)) :
    ∃ (C : CochainComplex Y.Modules ℤ) (a : ℤ) (b : ℕ),
      C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 Y)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (C.X n).IsFinitePresentation) ∧
      ∃ e : C ⟶ D, QuasiIso e := by
  let : IsAffine Y := hY
  let A := (Γ(Y, ⊤) : Type u)
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let G := @Functor.mapHomologicalComplex ℤ Y.Modules (ModuleCat.{u} A) _ _ _ _
    (SheafOfModules.evaluation.{u} (moduleRings Y.toRingedSpace) (Opposite.op ⊤))
    ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)
  obtain ⟨P, a, b, hbound, hfinite, hprojective, ⟨hPG⟩⟩ :=
    exists_affine_perfect_sections_projective_model Y hY D d hDle hDqc hperfect
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2
    (fun n hn ↦ hbound n (Or.inr hn))
  have : ∀ n : ℤ, Module.Projective A (P.X n) := hprojective
  have : ∀ n : ℤ, Projective (P.X n) := fun n ↦ inferInstance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨q, hQq⟩ :=
    CochainComplex.IsKProjective.exists_Q_map_eq P (G.obj D) hPG.hom
  have hqiso : QuasiIso q := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) q).1
    (by rw [hQq]; infer_instance)
  let F := tilde.functor Γ(Y, ⊤) ⋙ restrictFunctor Y.isoSpec.hom
  let C : CochainComplex Y.Modules ℤ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  obtain ⟨hflat, hqc, hfp, e, he⟩ :=
    affine_projective_sections_sheafification Y D hDqc P hfinite hprojective q hqiso
  refine ⟨C, a, b.toNat, ?_, ?_, hflat, hqc, hfp, e, he⟩
  · apply (C.isStrictlyGE_iff a).2
    intro n hn
    exact F.map_isZero (hbound n (Or.inl hn))
  · apply (C.isStrictlyLE_iff (b.toNat : ℤ)).2
    intro n hn
    exact F.map_isZero (hbound n (Or.inr ((Int.self_le_toNat b).trans_lt hn)))

end AlgebraicGeometry.Scheme.Modules
