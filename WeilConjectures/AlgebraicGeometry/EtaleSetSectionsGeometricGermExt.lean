/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Étale set-sheaf sections are determined by geometric germs

Source: Stacks Project, Étale Cohomology, Theorem 03PU, injectivity criterion.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Étale Cohomology, Theorem 03PU (injectivity criterion). -/
theorem etaleSetSection_ext_of_geometric_germs
    (X : Scheme.{u}) (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U : X.Etale) (a b : G.obj.obj (op U))
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ X) (z : (Scheme.pointSmallEtale x).fiber.obj U),
      (Scheme.pointSmallEtale x).toPresheafFiber U z G.obj a =
        (Scheme.pointSmallEtale x).toPresheafFiber U z G.obj b) : a = b := by
  classical
  have local_agree (v : U.left) : ∃ (V : X.Etale) (m : V ⟶ U) (w : V.left),
      m.left w = v ∧ G.obj.map m.op a = G.obj.map m.op b := by
    let Ω := AlgebraicClosure (U.left.residueField v)
    let t : Spec (.of Ω) ⟶ U.left := (Scheme.SpecToEquivOfField Ω U.left).symm
      ⟨v, CommRingCat.ofHom (algebraMap (U.left.residueField v) Ω)⟩
    let x := t ≫ U.hom
    let z : (Scheme.pointSmallEtale x).fiber.obj U := Over.homMk t rfl
    have he := h Ω x z
    obtain ⟨V, m, w, hw, heq⟩ :=
      ((Scheme.pointSmallEtale x).toPresheafFiber_eq_iff'
        (A := Type (u + 1)) (P := G.obj) U z a b).1 he
    refine ⟨V, m, w.left (default : Spec (.of Ω)), ?_, heq⟩
    have hv := congrArg (fun z ↦ z.left (default : Spec (.of Ω))) hw
    simpa [Scheme.pointSmallEtale, Scheme.Etale.forget, x, z, t,
      Scheme.SpecToEquivOfField,
      Scheme.Hom.comp_apply] using hv
  choose V m w hw heq using local_agree
  have hcover : Sieve.ofArrows V m ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext v
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨v, w v, hw v⟩
  have H : (↾(fun _ : PUnit.{u + 2} ↦ a)) = (↾(fun _ : PUnit.{u + 2} ↦ b)) := by
    apply G.property.hom_ext_ofArrows m hcover
    intro v
    ext z
    exact heq v
  exact ConcreteCategory.congr_hom H PUnit.unit

end AlgebraicGeometry
