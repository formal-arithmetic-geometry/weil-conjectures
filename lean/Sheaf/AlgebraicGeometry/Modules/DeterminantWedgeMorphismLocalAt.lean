module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafMapExists
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheafPowerIso_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafPowerIso M n).hom.app U
        (exteriorSheafSection M n U a) = wedge a := by
  rw [← exteriorSheafPowerIso_inv_wedge M n U a]
  exact inv_app_hom_app_apply_of_iso (exteriorSheafPowerIso M n).symm _

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility transport from the official exterior-power factorization theorem to
`exteriorSheaf`. Conjugate both maps by the canonical comparison isomorphisms,
apply the upstream theorem, and check the transported factorization on local wedge
generators. Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph. -/
private theorem determinant_wedge_quotient_factor_compat {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    (hr : r₂ = r₁ + r₃) [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶
      exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃)
    (ψ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶ exteriorSheaf S.X₂ r₂)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₂ r₃ U c)) =
        tmulSection (M := exteriorSheaf S.X₁ r₁)
          (N := exteriorSheaf S.X₃ r₃) (U := U)
          (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U (fun i ↦ S.g.val.app (op U) (c i))))
    (hψ : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      ψ.val.app (op U)
        (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₂ r₃ U c)) =
        exteriorSheafSection S.X₂ r₂ U
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      q ≫ φ = ψ := by
  let eA := exteriorSheafPowerIso S.X₁ r₁
  let eB := exteriorSheafPowerIso S.X₂ r₃
  let eC := exteriorSheafPowerIso S.X₃ r₃
  let eD := exteriorSheafPowerIso S.X₂ r₂
  let q' := (eA.inv ⊗ₘ eB.inv) ≫ q ≫ (eA.hom ⊗ₘ eC.hom)
  let ψ' := (eA.inv ⊗ₘ eB.inv) ≫ ψ ≫ eD.hom
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
    change (eA.hom ⊗ₘ eC.hom).app U
      (q.val.app (op U) ((eA.inv ⊗ₘ eB.inv).app U
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)))) = _
    rw [tensorHom_app_tmulSection,
      exteriorSheafPowerIso_inv_wedge,
      exteriorSheafPowerIso_inv_wedge]
    rw [hq U a c]
    rw [tensorHom_app_tmulSection,
      exteriorSheafPowerIso_hom_wedge,
      exteriorSheafPowerIso_hom_wedge]
  have hψ' : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      ψ'.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        wedge (M := S.X₂) (r := r₂) (U := U)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
    intro U a c
    change eD.hom.app U
      (ψ.val.app (op U) ((eA.inv ⊗ₘ eB.inv).app U
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)))) = _
    rw [tensorHom_app_tmulSection,
      exteriorSheafPowerIso_inv_wedge,
      exteriorSheafPowerIso_inv_wedge]
    rw [hψ U a c, exteriorSheafPowerIso_hom_wedge]
  obtain ⟨φ', hφ'⟩ :=
    determinant_wedge_quotient_factor S hS r₁ r₂ r₃ hr q' ψ' hq' hψ'
  refine ⟨(eA.hom ⊗ₘ eC.hom) ≫ φ' ≫ eD.inv, ?_⟩
  apply exteriorSheafTensor_lift_hom_ext (𝟙 S.X₂) r₁ r₃
  intro U a c
  change eD.inv.app U (φ'.app U ((eA.hom ⊗ₘ eC.hom).app U
    (q.val.app (op U)
      (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
        (exteriorSheafSection S.X₂ r₃ U c))))) =
    ψ.val.app (op U)
      (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
        (exteriorSheafSection S.X₂ r₃ U c))
  have H := congrArg (fun z ↦ z.val.app (op U)
    (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
      (wedge (M := S.X₂) (r := r₃) (U := U) c))) hφ'
  change φ'.app U (q'.val.app (op U) _) = ψ'.val.app (op U) _ at H
  rw [hq' U a c, hψ' U a c] at H
  rw [hq U a c, tensorHom_app_tmulSection,
    exteriorSheafPowerIso_hom_wedge, exteriorSheafPowerIso_hom_wedge,
    H, exteriorSheafPowerIso_inv_wedge, hψ U a c]


-- The two exterior presheaves have the same objects and uniquely determined restrictions.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def exteriorPresheafComparison {X : Scheme.{v}}
    (M : X.Modules) (n : ℕ) :
    exteriorSheafPresheaf M n ≅ M.val.exteriorPower (R := X.presheaf) n :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    change exteriorSheafRestriction M n f =
      PresheafOfModules.ExteriorPower.map (R := X.presheaf) M.val n f
    apply ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).2 _ ?_).symm
    intro a
    with_unfolding_all
      exact PresheafOfModules.ExteriorPower.map_ιMulti (R := X.presheaf) M.val n f a)

-- Sheafify the identity-on-sections comparison.
private noncomputable def exteriorComparison {X : Scheme.{v}} (M : X.Modules) (n : ℕ) :
    exteriorSheaf M n ≅ exteriorPower M n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (exteriorPresheafComparison M n)

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorComparison_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorComparison M n).hom.val.app (op U) (exteriorSheafSection M n U a) =
      wedge (M := M) (r := n) (U := U) a := by
  have h := congrArg
    (fun k ↦ k.app (op U) (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) n a))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (exteriorPresheafComparison M n).hom)
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorComparison_inv_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorComparison M n).inv.val.app (op U) (wedge (M := M) (r := n) (U := U) a) =
      exteriorSheafSection M n U a := by
  rw [← exteriorComparison_hom_wedge M n U a]
  change (((exteriorComparison M n).hom ≫ (exteriorComparison M n).inv).val.app (op U)) _ = _
  rw [Iso.hom_inv_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheaf_map_from_upstream {X : Scheme.{v}} {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    ∃ e : exteriorSheaf M n ⟶ exteriorSheaf N n,
      ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U)),
        e.val.app (op U) (exteriorSheafSection M n U a) =
          exteriorSheafSection N n U (fun i ↦ f.val.app (op U) (a i)) := by
  obtain ⟨e, he⟩ := exteriorSheaf_map_exists f n
  refine ⟨(exteriorComparison M n).hom ≫ e ≫ (exteriorComparison N n).inv, ?_⟩
  intro U a
  change (exteriorComparison N n).inv.val.app (op U)
    (e.val.app (op U)
      ((exteriorComparison M n).hom.val.app (op U) (exteriorSheafSection M n U a))) = _
  rw [exteriorComparison_hom_wedge, he, exteriorComparison_inv_wedge]

-- Transport the upstream wedge map through the comparisons, preserving its generator formula.
set_option backward.isDefEq.respectTransparency false in
private theorem wedgeMap_legacy {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s t : ℕ) (ht : t = r + s) :
    ∃ ψ : exteriorSheaf A r ⊗ exteriorSheaf B s ⟶ exteriorSheaf B t,
      ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
          exteriorSheafSection B t U
            (fun i ↦ Fin.append (fun j ↦ f.val.app (op U) (a j)) c (Fin.cast ht i)) := by
  obtain ⟨ψ, hψ⟩ := exteriorSheaf_wedgeMap_exists f r s t ht
  refine ⟨((exteriorComparison A r).hom ⊗ₘ (exteriorComparison B s).hom) ≫
    ψ ≫ (exteriorComparison B t).inv, ?_⟩
  intro U a c
  change (exteriorComparison B t).inv.val.app (op U)
    (ψ.val.app (op U)
      ((((exteriorComparison A r).hom ⊗ₘ (exteriorComparison B s).hom).app U)
        (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)))) = _
  rw [tensorHom_app_tmulSection]
  change (exteriorComparison B t).inv.val.app (op U)
    (ψ.val.app (op U)
      (tmulSection
        ((exteriorComparison A r).hom.val.app (op U) (exteriorSheafSection A r U a))
        ((exteriorComparison B s).hom.val.app (op U) (exteriorSheafSection B s U c)))) = _
  rw [exteriorComparison_hom_wedge, exteriorComparison_hom_wedge,
    hψ U a c, exteriorComparison_inv_wedge]

set_option backward.isDefEq.respectTransparency false in
/-- The local wedge construction on a fixed open, as in the determinant paragraph.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
The construction chooses local lifts, proves independence by finite locally free basis
expansion and alternation, and descends the resulting alternating multilinear map through
exterior powers and tensor products. (blueprint: new-local-wedge-at)
-/
theorem determinant_wedgeMorphism_local_data_at {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] (U : X.Opens) :
    ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  obtain ⟨e, he⟩ := exteriorSheaf_map_from_upstream S.g r₃
  obtain ⟨ψ, hψ⟩ := wedgeMap_legacy S.f r₁ r₃ r₂ hr
  let q : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶
      exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ := 𝟙 _ ⊗ₘ e
  have hq : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (c : Fin r₃ → S.X₂.val.obj (op V)),
      q.val.app (op V)
        (tmulSection (exteriorSheafSection S.X₁ r₁ V a)
          (exteriorSheafSection S.X₂ r₃ V c)) =
        tmulSection (M := exteriorSheaf S.X₁ r₁)
          (N := exteriorSheaf S.X₃ r₃) (U := V)
          (exteriorSheafSection S.X₁ r₁ V a)
          (exteriorSheafSection S.X₃ r₃ V (fun i ↦ S.g.val.app (op V) (c i))) := by
    intro V a c
    change ((𝟙 _ ⊗ₘ e).app V) _ = _
    rw [tensorHom_app_tmulSection]
    change tmulSection (M := exteriorSheaf S.X₁ r₁) (N := exteriorSheaf S.X₃ r₃)
      (U := V) (exteriorSheafSection S.X₁ r₁ V a)
      (e.val.app (op V) (exteriorSheafSection S.X₂ r₃ V c)) = _
    exact congrArg (fun z ↦ tmulSection (M := exteriorSheaf S.X₁ r₁)
      (N := exteriorSheaf S.X₃ r₃) (U := V) (exteriorSheafSection S.X₁ r₁ V a) z)
      (he V c)
  obtain ⟨φ, hφ⟩ := determinant_wedge_quotient_factor_compat S hS r₁ r₂ r₃ hr q ψ hq hψ
  refine ⟨φ, ?_⟩
  intro a b c hc
  have hb : (fun i ↦ S.g.val.app (op U) (c i)) = b := funext hc
  have h := congrArg
    (fun k ↦ k.val.app (op U)
      (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
        (exteriorSheafSection S.X₂ r₃ U c))) hφ
  change φ.val.app (op U) (q.val.app (op U)
      (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
        (exteriorSheafSection S.X₂ r₃ U c))) =
    ψ.val.app (op U)
      (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
        (exteriorSheafSection S.X₂ r₃ U c)) at h
  rw [hq U a c, hb, hψ U a c] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
