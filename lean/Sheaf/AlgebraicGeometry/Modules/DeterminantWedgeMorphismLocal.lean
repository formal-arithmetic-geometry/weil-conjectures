module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheafPowerIso_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafPowerIso M n).hom.app U (exteriorSheafSection M n U a) =
      wedge (M := M) (r := n) (U := U) a := by
  rw [← exteriorSheafPowerIso_inv_wedge M n U a]
  exact inv_app_hom_app_apply_of_iso (exteriorSheafPowerIso M n).symm _

set_option backward.isDefEq.respectTransparency false in
/-- Local existence of wedge maps on every open. The proof constructs the map on each open
by choosing local lifts; compatibility on overlaps is deferred to the gluing theorem.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-determinant-wedge-morphism-local-data).

Proof: Choose local lifts of the finitely many quotient sections using the epimorphism
property of `S.g`. The alternating wedge formula is independent of the choices because
the difference of two lifts lies in the image of `S.f`; after trivializing the finite
locally free first term, every resulting term has more than `r₁` basis factors and
vanishes by alternation. The universal properties of exterior powers and tensor products
then produce the displayed morphism on the open. -/
theorem determinant_wedgeMorphism_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] :
    ∀ (U : X.Opens), ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  intro U
  obtain ⟨φ, hφ⟩ := determinant_wedgeMorphism_local_data_at S hS r₁ r₂ r₃ hr U
  refine ⟨((exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
    (exteriorSheafPowerIso S.X₃ r₃).hom) ≫ φ ≫
      (exteriorSheafPowerIso S.X₂ r₂).inv, ?_⟩
  intro a b c hc
  change (exteriorSheafPowerIso S.X₂ r₂).inv.app U
    (φ.app U ((((exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
      (exteriorSheafPowerIso S.X₃ r₃).hom).app U)
        (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U b)))) = _
  rw [tensorHom_app_tmulSection, exteriorSheafPowerIso_hom_wedge,
    exteriorSheafPowerIso_hom_wedge]
  exact (congrArg ((exteriorSheafPowerIso S.X₂ r₂).inv.app U) (hφ a b c hc)).trans
    (exteriorSheafPowerIso_inv_wedge S.X₂ r₂ U _)

set_option backward.isDefEq.respectTransparency false in
/-- A compatible family of local wedge maps glues to a sheaf morphism.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-determinant-wedge-morphism-glue).

Proof: The local maps have the same displayed formula on restrictions, hence agree on
overlaps by separatedness of the target sheaf. The sheaf gluing property assembles them
into one morphism, and the formula is preserved after restriction and therefore holds
on every open. -/
theorem determinant_wedgeMorphism_of_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (hlocal : ∀ (U : X.Opens), ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
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
  choose φU hφU using hlocal
  let e := tensorIso (exteriorSheafPowerIso S.X₁ r₁)
    (exteriorSheafPowerIso S.X₃ r₃)
  let d := exteriorSheafPowerIso S.X₂ r₂
  let ψU := fun U ↦ e.inv ≫ φU U ≫ d.hom
  have hψU : ∀ (U : X.Opens)
      (a : Fin r₁ → S.X₁.val.obj (op U))
      (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
      (∀ i, S.g.val.app (op U) (c i) = b i) →
      (ψU U).val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
        wedge (M := S.X₂) (r := r₂) (U := U)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
    intro U a b c hc
    change d.hom.app U ((φU U).app U
      (((exteriorSheafPowerIso S.X₁ r₁).inv ⊗ₘ
        (exteriorSheafPowerIso S.X₃ r₃).inv).app U _)) = _
    rw [tensorHom_app_tmulSection, exteriorSheafPowerIso_inv_wedge,
      exteriorSheafPowerIso_inv_wedge]
    exact (congrArg (d.hom.app U) (hφU U a b c hc)).trans
      (exteriorSheafPowerIso_hom_wedge S.X₂ r₂ U _)
  obtain ⟨ψ, hψ⟩ := determinant_wedgeMorphism_glue_family S hS r₁ r₂ r₃ hr ψU hψU
  refine ⟨e.hom ≫ ψ ≫ d.inv, ?_⟩
  intro U a b c hc
  change d.inv.app U (ψ.app U
    (((exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
      (exteriorSheafPowerIso S.X₃ r₃).hom).app U _)) = _
  rw [tensorHom_app_tmulSection, exteriorSheafPowerIso_hom_wedge,
    exteriorSheafPowerIso_hom_wedge]
  exact (congrArg (d.inv.app U) (hψ U a b c hc)).trans
    (exteriorSheafPowerIso_inv_wedge S.X₂ r₂ U _)

end AlgebraicGeometry.Scheme.Modules
