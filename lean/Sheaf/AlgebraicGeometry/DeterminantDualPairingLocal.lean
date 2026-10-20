/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.AlgebraicGeometry.DeterminantDualLocalFrames
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPresheafComparison
import Mathlib.Tactic.DepRewrite
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Local perfection of the exterior dual pairing
Source: Stacks Project, Tag 0BRT, determinant inversion.
(blueprint: lem-sc-exterior-dual-pairing-local-bijective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

-- The transport below has equal section objects but different presheaf restriction maps.
-- Express its dependent recursors as casts, which simplify on the identical section types.
private theorem rec_eq_cast {α : Sort*} {a b : α}
    {β : (b : α) → a = b → Sort*} (h : a = b) (x : β a rfl) :
    Eq.rec (motive := β) x h = cast (by cases h; rfl : β a rfl = β b h) x := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A determinant-formula morphism is bijective on sections below an open on which M
is finite free, in every exterior degree.
Source: Stacks Project, Tag 0BRT, determinant pairing; Mathlib
`exteriorPower.basis_coord` and the finite dual basis.
(blueprint: lem-sc-exterior-dual-pairing-local-bijective).

Proof: restrict the given trivialization to each V contained in U. Sections of the
finite free sheaf and its internal dual become the free section module and its
ring-linear dual; the inverse to evaluation reconstructs a natural sheaf map by
basis coordinates. The wedge bases identify the exterior sheaves on these opens
with the sectionwise exterior powers: the latter are finite free sheaves, and
sheafification restricted to the open is characterized by the same adjunction.
Under these identifications the assumed formula identifies f on pure wedges with
Mathlib's pairingDual. Pure wedges span the sectionwise exterior powers, so the
maps agree everywhere. The wedge of each dual basis vector maps to the
corresponding coordinate functional (`exteriorPower.basis_coord`). Since the wedge
basis is finite, these functionals form its dual basis, proving bijectivity.
When n exceeds the rank, both exterior modules are zero;
when n=0 both are the ring. Zero rings and empty opens are allowed. -/
theorem exterior_dual_pairing_app_bijective (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (f : Scheme.Modules.exteriorSheaf (Scheme.Modules.dual M) n ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n))
    (hf : ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (Scheme.Modules.exteriorSheafSection
        (Scheme.Modules.dual M) n U φ)).app (op (Over.mk (𝟙 U)))
        (Scheme.Modules.exteriorSheafSection M n U a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    Function.Bijective (f.val.app (op V)) := by
  classical
  have h := exterior_dual_local_frames X M n U r e V g
  dsimp +instances only [Scheme.Modules.wedge, Scheme.Modules.toSheafificationObj,
    Scheme.Modules.exteriorPower, Scheme.Modules.sheafificationObj] at h
  rw! (castMode := .all) [← Scheme.Modules.exteriorSheafPresheaf_eq_exteriorPower M n,
    ← Scheme.Modules.exteriorSheafPresheaf_eq_exteriorPower (Scheme.Modules.dual M) n] at h
  obtain ⟨a, φ, b, d, c, hφ, hb, hd, hc⟩ := h
  simp only [rec_eq_cast, cast_eq] at hb hd
  let targetBasis := d.dualBasis.map c.symm
  have hmap (s : Set.powersetCard (Fin r) n) : f.val.app (op V) (b s) = targetBasis s := by
    apply c.injective
    apply d.ext
    intro t
    have hdet : (Matrix.of fun i j ↦
        a.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (a (Set.powersetCard.ofFinEmbEquiv.symm t i))).det =
        d.dualBasis s (d t) := by
      rw [Module.Basis.dualBasis_apply_self]
      calc
        _ = exteriorPower.ιMultiDual (X.presheaf.obj (op V)) n a s
            (exteriorPower.ιMulti_family (X.presheaf.obj (op V)) n a t) := by
          rw [exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
          rfl
        _ = (a.exteriorPower n).coord s ((a.exteriorPower n) t) := by
          rw [exteriorPower.basis_coord, exteriorPower.basis_apply]
        _ = _ := by
          rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    calc
      c (f.val.app (op V) (b s)) (d t) =
          (Matrix.of fun i j ↦
            a.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
              (a (Set.powersetCard.ofFinEmbEquiv.symm t i))).det := by
        rw [hc, hb, hd]
        change (f.val.app (op V) (Scheme.Modules.exteriorSheafSection
          (Scheme.Modules.dual M) n V (φ ∘ Set.powersetCard.ofFinEmbEquiv.symm s))).app
            (op (Over.mk (𝟙 V))) (Scheme.Modules.exteriorSheafSection M n V
              (a ∘ Set.powersetCard.ofFinEmbEquiv.symm t)) = _
        rw [hf]
        simp only [Function.comp_apply, hφ]
      _ = d.dualBasis s (d t) := hdet
      _ = c (targetBasis s) (d t) := by simp [targetBasis]
  have heq : (f.val.app (op V)).hom =
      (b.equiv targetBasis (Equiv.refl _)).toLinearMap := by
    apply b.ext
    intro s
    change f.val.app (op V) (b s) = (b.equiv targetBasis (Equiv.refl _)) (b s)
    rw [Module.Basis.equiv_apply]
    exact hmap s
  rw [show (f.val.app (op V) : _ → _) = b.equiv targetBasis (Equiv.refl _) by
    exact congrArg DFunLike.coe heq]
  exact (b.equiv targetBasis (Equiv.refl _)).bijective

end AlgebraicGeometry
