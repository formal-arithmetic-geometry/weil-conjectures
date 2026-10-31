/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTowerLimit

/-! # Invertibility of the normalized base coefficient comparison

Source: the integral-twist paragraph of the Cartesian coefficients and twists proof.
(blueprint: lem-pur-base-completion-pullback-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.CompletedCoefficientNormalization

/-- The residue-normalized comparison for the completed base ring is invertible.
Only this particular inverse limit is asserted to commute with inverse image.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-prop-sfb-cartesian-coefficients-twists.proof.md, Integral twist paragraph;
Stacks Project, Tag 09A5.
(blueprint: lem-pur-base-completion-pullback-iso).

Proof: the tower of constant finite rings Z/ell^(n+1) is represented, as a tower
of set sheaves, by the corresponding constant finite etale schemes. Its limit is
represented by the affine inverse limit of those schemes. Base change of affine
schemes commutes with this inverse limit. The inverse image of each representable
sheaf is represented by its base change, so the projection-induced map from the
inverse image of the base completion to the target base completion is invertible
on underlying set sheaves. Addition and multiplication are coordinatewise, and
forgetting commutative ring sheaves reflects isomorphisms. Thus it is invertible
as a ring-sheaf map. The equations a.projection identify a.alpha with that map by
joint monicity of the target limit projections. No choice of epsilon changes
this argument. Empty schemes give the unique map between zero sheaves. -/
theorem pur_base_completion_pullback_isIso
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    (d : BaseData.{u, u} l) (a : BasePullback l d h) : IsIso a.alpha := by
  let q (n : ℕ) : CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 2)))) ⟶
      CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))
  let Q := Functor.ofOpSequence
    (X := fun n : ℕ ↦ CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) q
  let L := inverse.{u, u} h
  let : ∀ n : ℕ, NeZero (l ^ (n + 1)) :=
    fun n ↦ ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := by
    intro n
    change Finite (ULift.{u + 1} (ZMod (l ^ (n.unop + 1))))
    infer_instance
  let e : Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{u + 1} ⟶
      baseTower.{u, u} l Y := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _)
    (by
      intro n
      simp only [Functor.comp_map, Q, baseTower, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rfl)
  have : ∀ j, IsIso (e.app j) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso e := NatIso.isIso_of_isIso_app e
  have : PreservesLimit (Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}) L :=
    proEtaleSheafInverseImage_preserves_finite_tower h Q
  have : PreservesLimit (baseTower.{u, u} l Y) L :=
    preservesLimit_of_iso_diagram L (asIso e)
  let c : baseTower.{u, u} l Y ⋙ L ⟶ baseTower.{u, u} l X :=
    NatTrans.ofOpSequence
      (fun n ↦ delta.{u, u} h (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))
      (by
        intro n
        simp only [Functor.comp_map, baseTower, Functor.ofOpSequence_map_homOfLE_succ]
        change L.map (baseTransition l Y n) ≫ _ = _ ≫ baseTransition l X n
        change (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
            ((constantSheaf (ProEt.topology Y) _).map (q n)) ≫
            proEtaleConstantInverseImageMap h CommRingCat.{u + 1} _ =
          proEtaleConstantInverseImageMap h CommRingCat.{u + 1} _ ≫
            (constantSheaf (ProEt.topology X) _).map (q n)
        exact proEtaleConstantInverseImageMap_naturality h (q n))
  have : ∀ j, IsIso (c.app j) := fun j ↦ a.constant_iso _
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have he : a.alpha = limit.post (baseTower.{u, u} l Y) L ≫ limMap c := by
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limMap_π, limit.post_π_assoc]
    exact a.projection n.unop
  rw [he]
  infer_instance

end WeilConjectures.CompletedCoefficientNormalization
