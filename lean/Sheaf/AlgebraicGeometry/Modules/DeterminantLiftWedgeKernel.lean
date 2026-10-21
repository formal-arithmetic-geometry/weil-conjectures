/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison

/-!
# The wedge of lifts annihilates the quotient kernel

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
-/

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
/-- The wedge map on the sheaf of lifts annihilates the exterior quotient kernel.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: new-determinant-lift-wedge-kernel).

Proof: Sectionwise send a tensor of wedges to the concatenated wedge of the images
under `S.f` and the second tuple. Exterior multiplication is alternating separately
in these tuples, so the exterior-power and tensor universal properties give a linear
map. The formula commutes with restrictions; sheafification gives `w`. The formula
for `q` determines it on local generators, so it is the tensor of the identity with
the exterior-power map of `S.g`. Locally trivialize `S.X₁`. Exactness identifies the
kernel of `S.g` with the image of `S.f`. The exterior quotient has kernel generated
by wedges with a factor from that image: algebraically exterior powers commute with
quotients, and the relations for the quotient exterior power are precisely wedges
containing such a factor. This description applies after sheafification, since
finite tuples in the quotient lift locally. Every such term, after wedging with
`r₁` first-term factors, contains `r₁ + 1` factors from a free module of rank `r₁`.
Expand them in a local basis; each term has a repeated basis vector and vanishes by
alternation. Hence the composite of the kernel inclusion with `w` is locally zero,
and separatedness makes it zero globally. Degree zero in the second factor gives
an identity quotient and zero kernel; rank zero in the first factor gives `S.f = 0`
and `S.g` an isomorphism, with the same conclusion. -/
theorem determinant_liftWedge_kernel_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
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
  obtain ⟨w, hw⟩ := wedgeMap_legacy S.f r₁ r₃ r₂ hr
  obtain ⟨φ, hφ⟩ := determinant_wedge_quotient_factor_compat S hS r₁ r₂ r₃ hr q w hq hw
  refine ⟨w, ?_, hw⟩
  rw [← hφ, ← Category.assoc, kernel.condition, zero_comp]

end AlgebraicGeometry.Scheme.Modules
