module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafMapExists
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists
import Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def exteriorPresheafIso {X : Scheme.{v}} (M : X.Modules) (n : ℕ) :
    exteriorSheafPresheaf M n ≅ M.val.exteriorPower (R := X.presheaf) n :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V k
    change exteriorSheafRestriction M n k =
      PresheafOfModules.ExteriorPower.map (R := X.presheaf) M.val n k
    apply ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n k)).2
      _ ?_).symm
    intro a
    exact PresheafOfModules.ExteriorPower.map_ιMulti (R := X.presheaf) M.val n k a)

private noncomputable def exteriorComparison {X : Scheme.{v}} (M : X.Modules) (n : ℕ) :
    exteriorSheaf M n ≅ exteriorPower M n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (exteriorPresheafIso M n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem exteriorComparison_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorComparison M n).hom.val.app (op U) (exteriorSheafSection M n U a) =
      wedge (M := M) (r := n) (U := U) a := by
  have h := congrArg
    (fun k ↦ k.app (op U) (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) n a))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (exteriorPresheafIso M n).hom)
  exact h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem exteriorComparison_inv_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorComparison M n).inv.val.app (op U) (wedge (M := M) (r := n) (U := U) a) =
      exteriorSheafSection M n U a := by
  have h := congrArg
    (fun k ↦ k.app (op U) (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) n a))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (exteriorPresheafIso M n).inv)
  exact h.symm

set_option backward.defeqAttrib.useBackward true in
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
  obtain ⟨ψ, hψ⟩ := exteriorSheaf_wedgeMap_exists S.f r₁ r₃ r₂ hr
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
  obtain ⟨φ, hφ⟩ := determinant_wedge_quotient_factor S hS r₁ r₂ r₃ hr q ψ hq hψ
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
