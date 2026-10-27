/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Paper.ScalarExtensionEvaluationComparison
import all Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction

/-! # Evaluation of ordinary scalar extension

Source: Stacks Project, Modules on Sites, Section 03EK and Tag 03CY,
applied to the vertical sequence topology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections

open scoped ChangeOfRings

attribute [local irreducible] scalarExtensionSection

private theorem evaluation_smul
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (D : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n, D (n + 1) ⟶ D n) (M : Systems.{c, v, max c v r} J D σ)
    (n : ℕ) (U : Cᵒᵖ) (a : (D n).obj.obj U)
    (x : M.val.obj (op (n, U.unop))) :
    a • (show ((evaluation.{c, v, max c v r} J D σ n).obj M).val.obj U from x) =
      (a • x : M.val.obj (op (n, U.unop))) := by
  change ((eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom.app U).hom a • x = _
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

/-- Evaluation of an ordinary coefficient extension represents coefficient-linear maps.
Source: Stacks Project, sites-modules.tex, Section 03EK and Tag 03CY;
vertical restriction in the proof of blueprint classes (2).
(blueprint: lem-sp-scalar-extension-evaluation).

Proof: restrict the sectionwise tensor presheaf to the vertical slice at n.
The coefficient evaluation equalities identify its sections with the extension
of scalars of the evaluated module. The vertical inclusion is both continuous
and cocontinuous, so restriction of the sheafification unit is locally bijective.
Consequently its restricted sheafification is the sheafification of the restricted
tensor presheaf. Apply the module-sheafification adjunction and the sectionwise
tensor/restriction adjunction. This gives the Hom equivalences. Both adjunctions
commute with postcomposition. Their unit sends x to the sheafified tensor 1 tensor x;
the object equality of S.model transports that formula to S.model.E.
Evaluation retains the underlying section groups and scalar actions. Linearity
therefore gives the formula for arbitrary scalar multiples of a generator. -/
theorem scalarExtension_evaluation
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C)
    (B D : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, D (n + 1) ⟶ D n)
    (α : ∀ n, B n ⟶ D n)
    (φ : systemRing.{c, v, max c v r} J B τ ⟶ systemRing.{c, v, max c v r} J D σ)
    (hφ : ∀ (n : ℕ) (U : Cᵒᵖ), φ.hom.app (op (n, U.unop)) = (α n).hom.app U)
    (S : ScalarData.{c, v, max c v r} φ)
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    ∃ Ψ : ∀ N : Mod.{c, v, max c v r} J (D n),
      ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M) ⟶ N) ≃
        ((evaluation.{c, v, max c v r} J B τ n).obj M ⟶ (res.{c, v, max c v r} (α n)).obj N),
      (∀ {N N'} (f : (evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M) ⟶ N)
        (g : N ⟶ N'), Ψ N' (f ≫ g) = Ψ N f ≫ (res.{c, v, max c v r} (α n)).map g) ∧
      (∀ N (f : (evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M) ⟶ N)
        (U : Cᵒᵖ) (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop)))
        (v : ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M)).val.obj U),
        HEq v (a • scalarExtensionSection.{c, v, r} φ S M (op (n, U.unop)) x) →
        f.val.app U v = a • (show N.val.obj U from (Ψ N f).val.app U x)) := by
  let Q := (evaluation.{c, v, max c v r} J B τ n).obj M
  obtain ⟨e, he⟩ := scalarExtension_evaluation_comparison.{c, v, r}
    J B D τ σ α φ hφ S M n
  let Ψ := fun N ↦ (Iso.homCongr e.symm (Iso.refl N)).trans
    (SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N)
  refine ⟨Ψ, ?_, ?_⟩
  · intro N N' f g
    change SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N'
        (e.hom ≫ (f ≫ g)) =
      SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N (e.hom ≫ f) ≫
        (res.{c, v, max c v r} (α n)).map g
    exact (congrArg
      (SheafOfModules.ScalarReductionProof.tensorHomEquiv (α n) Q N')
      (Category.assoc e.hom f g).symm).trans
        (SheafOfModules.ScalarReductionProof.tensorHomEquiv_naturality_right
          (α n) Q (e.hom ≫ f) g)
  · intro N f U a x v hv
    let z := scalarExtensionSection.{c, v, r} φ S M (op (n, U.unop)) x
    have hv' : v = a •
        (show ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M)).val.obj U
          from z) :=
      (eq_of_heq hv).trans (evaluation_smul.{c, v, r} J D σ (S.model.E.obj M) n U a z).symm
    have hu : f.val.app U
        (show ((evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M)).val.obj U
          from z) = (Ψ N f).val.app U x := by
      exact (congrArg
        (fun t : ((evaluation.{c, v, max c v r} J D σ n).obj
          (S.model.E.obj M)).val.obj U ↦ f.val.app U t) (he U x)).symm
    rw [hv', map_smul]
    exact congrArg (fun t : N.val.obj U ↦ a • t) hu

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
