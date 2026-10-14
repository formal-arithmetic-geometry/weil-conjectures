/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Top exterior powers of trivial sheaves

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-trivial-top-iso).
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private def topIndex (r : ℕ) : Set.powersetCard (Fin r) r :=
  ⟨Finset.univ, by simp⟩

private abbrev topIndexUnique (r : ℕ) : Unique (Set.powersetCard (Fin r) r) where
  default := topIndex r
  uniq s := by
    apply Subtype.ext
    exact Finset.eq_univ_of_card s.val (by
      have hs : s.val.card = r := s.prop
      simpa only [Fintype.card_fin] using hs)

private noncomputable def topEquiv {R A : Type v} [CommRing R] [AddCommGroup A]
    [Module R A] {r : ℕ} (b : Module.Basis (Fin r) R A) : (⋀[R]^r A) ≃ₗ[R] R := by
  letI := topIndexUnique r
  exact (b.exteriorPower r).equivFun.trans
    (LinearEquiv.piUnique R (fun _ : Set.powersetCard (Fin r) r ↦ R))

private lemma topEquiv_apply {R A : Type v} [CommRing R] [AddCommGroup A]
    [Module R A] {r : ℕ} (b : Module.Basis (Fin r) R A) (a : Fin r → A) :
    topEquiv b (exteriorPower.ιMulti R r a) =
      (Matrix.of fun i j ↦
        b.coord (Set.powersetCard.ofFinEmbEquiv.symm (topIndex r) j) (a i)).det := by
  change (b.exteriorPower r).equivFun (exteriorPower.ιMulti R r a) (topIndex r) = _
  rw [Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]

set_option maxHeartbeats 800000 in
-- Comparing the sectionwise ring and sheaf interfaces requires additional elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- A global trivialization of rank `r` gives a trivialization of its top exterior presheaf.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-trivial-top-iso).

Proof: On each open, the trivialization identifies sections with `O(U)^r`. Transport the
standard basis and take its top exterior basis. Its index set consists only of the full
set of `r` indices, so evaluation of its coordinate is a linear equivalence with `O(U)`.
On a pure wedge this coordinate is the determinant of the matrix of coordinates of its
factors. The coordinates commute with restriction by naturality of the trivialization
and of the free-sheaf coordinate projections; determinants commute with ring maps.
Thus the equivalences commute with restriction on pure wedges, hence everywhere because
pure wedges span. They form the required presheaf isomorphism. The empty determinant
is one, so the argument includes rank zero and the zero ring. -/
theorem exteriorSheaf_trivial_top_presheaf_iso {X : Scheme.{v}} (M : X.Modules) (r : ℕ)
    (e : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{v} (Fin r))) :
    Nonempty (exteriorSheafPresheaf M r ≅ (SheafOfModules.unit X.ringCatSheaf).val) := by
  let (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.presheaf.obj U))
  let c (U : X.Opensᵒᵖ) :
      M.val.obj U ≃ₗ[X.ringCatSheaf.obj.obj U] (Fin r → X.ringCatSheaf.obj.obj U) :=
    (SheafOfModules.sectionsLinearEquivOfIsoFree e U).trans
      (LinearEquiv.funCongrLeft _ _ Equiv.ulift.symm)
  let b (U : X.Opensᵒᵖ) := Module.Basis.ofEquivFun (c U)
  refine ⟨PresheafOfModules.isoMk (fun U ↦ (topEquiv (b U)).toModuleIso) ?_⟩
  intro U V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on_range (exteriorPower.ιMulti_span _ _ _)
  intro a
  change topEquiv (b V) (exteriorSheafRestriction M r f
      (exteriorPower.ιMulti (X.presheaf.obj U) r a)) =
    X.presheaf.map f (topEquiv (b U) (exteriorPower.ιMulti (X.presheaf.obj U) r a))
  have h := (Classical.choose_spec (exteriorSheafRestriction_existsUnique M r f)).1 a
  change exteriorSheafRestriction M r f (exteriorPower.ιMulti (X.presheaf.obj U) r a) =
    exteriorPower.ιMulti (X.presheaf.obj V) r (fun i ↦ M.val.map f (a i)) at h
  rw [h]
  have hv := topEquiv_apply (b V) (fun i ↦ M.val.map f (a i))
  have hu := topEquiv_apply (b U) a
  erw [hv, hu]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, b, Module.Basis.coord_apply,
    Module.Basis.ofEquivFun_repr_apply]
  let k := Set.powersetCard.ofFinEmbEquiv.symm (topIndex r) j
  exact PresheafOfModules.naturality_apply
    (e.hom ≫ SheafOfModules.freeπ (ULift.up k)).val f (a i)

end AlgebraicGeometry.Scheme.Modules
