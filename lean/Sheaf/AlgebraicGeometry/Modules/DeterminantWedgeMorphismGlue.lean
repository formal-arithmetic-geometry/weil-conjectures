module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTensorQuotientComparison
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheafPowerIso_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafPowerIso M n).hom.app U
        (exteriorSheafSection M n U a) = wedge a := by
  rw [← exteriorSheafPowerIso_inv_wedge M n U a]
  exact inv_app_hom_app_apply_of_iso (exteriorSheafPowerIso M n).symm _

set_option backward.isDefEq.respectTransparency false in
/-- Transport the official kernel-annihilation theorem through the canonical
exterior-power comparisons. The source comparison maps the old kernel into the
new kernel by its universal property. Transport the resulting wedge map back;
naturality of tensor sections and the wedge comparison formulas give the old formula.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph. -/
private theorem determinant_liftWedge_kernel_exists_compat {X : Scheme.{v}}
    (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶
      exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₂ r₃ U c)) =
        tmulSection (M := exteriorSheaf S.X₁ r₁) (N := exteriorSheaf S.X₃ r₃)
          (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U (fun i ↦ S.g.val.app (op U) (c i)))) :
    ∃ w : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      kernel.ι q ≫ w = 0 ∧ ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (c : Fin r₃ → S.X₂.val.obj (op U)),
        w.val.app (op U)
            (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
              (exteriorSheafSection S.X₂ r₃ U c)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  let eAB := tensorIso (exteriorSheafPowerIso S.X₁ r₁)
    (exteriorSheafPowerIso S.X₂ r₃)
  let eAC := tensorIso (exteriorSheafPowerIso S.X₁ r₁)
    (exteriorSheafPowerIso S.X₃ r₃)
  let eD := exteriorSheafPowerIso S.X₂ r₂
  let q' := eAB.inv ≫ q ≫ eAC.hom
  have hq' : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q'.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        tmulSection (M := exteriorPower S.X₁ r₁)
          (N := exteriorPower S.X₃ r₃) (U := U)
          (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₃) (r := r₃) (U := U)
            (fun i ↦ S.g.val.app (op U) (c i))) := by
    intro U a c
    change ((exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
      (exteriorSheafPowerIso S.X₃ r₃).hom).app U
      (q.val.app (op U) (((exteriorSheafPowerIso S.X₁ r₁).inv ⊗ₘ
        (exteriorSheafPowerIso S.X₂ r₃).inv).app U
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)))) = _
    rw [tensorHom_app_tmulSection,
      exteriorSheafPowerIso_inv_wedge,
      exteriorSheafPowerIso_inv_wedge]
    rw [hq U a c]
    rw [tensorHom_app_tmulSection,
      exteriorSheafPowerIso_hom_wedge,
      exteriorSheafPowerIso_hom_wedge]
  obtain ⟨w', hwzero, hw⟩ :=
    determinant_liftWedge_kernel_exists S hS r₁ r₂ r₃ hr q' hq'
  have hk : (kernel.ι q ≫ eAB.hom) ≫ q' = 0 := by
    simp only [q', Category.assoc, Iso.hom_inv_id_assoc, kernel.condition_assoc,
      zero_comp]
  have hkzero : (kernel.ι q ≫ eAB.hom) ≫ w' = 0 := by
    rw [← kernel.lift_ι q' (kernel.ι q ≫ eAB.hom) hk, Category.assoc,
      hwzero, comp_zero]
  refine ⟨eAB.hom ≫ w' ≫ eD.inv, ?_, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, hkzero, zero_comp]
  · intro U a c
    change eD.inv.app U (w'.app U (eAB.hom.app U
      (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
        (exteriorSheafSection S.X₂ r₃ U c)))) = _
    change eD.inv.app U (w'.app U
      (((exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
        (exteriorSheafPowerIso S.X₂ r₃).hom).app U _)) = _
    rw [tensorHom_app_tmulSection, exteriorSheafPowerIso_hom_wedge,
      exteriorSheafPowerIso_hom_wedge]
    change eD.inv.val.app (op U) (w'.val.app (op U) _) = _
    rw [hw U a c]
    exact exteriorSheafPowerIso_inv_wedge S.X₂ r₂ U _

set_option linter.unusedVariables false in
/-- A chosen family of local wedge maps glues to a global morphism.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
Proof: Form the epimorphism from tensors of wedges of lifts to tensors of quotient
wedges. The concatenated wedge map kills its kernel, so `Abelian.epiDesc` gives a
morphism on the quotient. Evaluate its factorization on pure wedges to obtain the
displayed formula. This construction does not need the supplied family.
(blueprint: new-wedge-glue-family)
-/
theorem determinant_wedgeMorphism_glue_family {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (φU : ∀ U : X.Opens, exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂)
    (hformula : ∀ (U : X.Opens)
      (a : Fin r₁ → S.X₁.val.obj (op U))
      (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
      (∀ i, S.g.val.app (op U) (c i) = b i) →
      (φU U).val.app (op U)
        (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U b)) =
        exteriorSheafSection S.X₂ r₂ U
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  clear φU hformula
  have : Epi S.g := hS.epi_g
  obtain ⟨q, hqepi, hq⟩ := exteriorSheafTensor_quotient_exists S.X₁ S.X₂ S.X₃ S.g r₁ r₃
  have : Epi q := hqepi
  obtain ⟨w, hwzero, hw⟩ := determinant_liftWedge_kernel_exists_compat S hS r₁ r₂ r₃ hr q hq
  let φ := Abelian.epiDesc q w hwzero
  have hcomp : q ≫ φ = w := Abelian.comp_epiDesc q w hwzero
  refine ⟨φ, ?_⟩
  intro U a b c hc
  have hb : (fun i ↦ S.g.val.app (op U) (c i)) = b := funext hc
  rw [← hb, ← hq U a c]
  have he := congrArg (fun k ↦ k.val.app (op U)
    (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
      (exteriorSheafSection S.X₂ r₃ U c))) hcomp
  exact he.trans (hw U a c)

end AlgebraicGeometry.Scheme.Modules
