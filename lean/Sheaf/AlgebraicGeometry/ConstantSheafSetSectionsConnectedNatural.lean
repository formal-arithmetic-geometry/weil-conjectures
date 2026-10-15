/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf

/-!
# Constant etale sheaf sections on a connected scheme

Source: Stacks Project, Remark 59.23.2 (Tag 03P5), set-valued form, and
Modules on Sites, Section 18.43 (Tags 093I and 093R)
(blueprint: lem-weil-pbc-constant-sheaf-set-sections-connected-natural).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem coproductConstant_bijective (U : Scheme.{u}) [ConnectedSpace U]
    (E : Type u) :
    Function.Bijective (fun e : E ↦
      (⟨Sigma.ι (fun _ : E ↦ U) e, by simp⟩ :
        {f : U ⟶ ∐ fun _ : E ↦ U // f ≫ Sigma.desc (fun _ : E ↦ 𝟙 U) = 𝟙 U})) := by
  classical
  obtain ⟨_, _, _, ⟨b, hb⟩, hc, _⟩ :=
    AlgebraicGeometry.coproductCopiesMorphismsClopen U U E (𝟙 U)
  let x : U := Classical.choice inferInstance
  let c (e : E) :
      {f : U ⟶ ∐ fun _ : E ↦ U // f ≫ Sigma.desc (fun _ : E ↦ 𝟙 U) = 𝟙 U} :=
    ⟨Sigma.ι (fun _ : E ↦ U) e, by simp⟩
  have hval (e : E) : b (c e) x = e := by
    have h := hb (c e) e
    have hc' := hc e e
    simp only [Category.id_comp, if_true] at hc'
    change ((Sigma.ι (fun _ : E ↦ U) e) ⁻¹ᵁ
      (Sigma.ι (fun _ : E ↦ U) e).opensRange : Set U) = _ at h
    rw [hc'] at h
    have hx : x ∈ (⊤ : U.Opens) := by trivial
    change x ∈ ((⊤ : U.Opens) : Set U) at hx
    rw [h] at hx
    exact hx
  have hconst (e : E) : b (c e) = LocallyConstant.const U e := by
    rw [(b (c e)).eq_const x, hval]
  constructor
  · intro e e' h
    have := congrArg (fun f ↦ b f x) h
    change b (c e) x = b (c e') x at this
    simpa only [hval] using this
  · intro f
    refine ⟨b f x, b.injective ?_⟩
    exact (hconst (b f x)).trans ((b f).eq_const x).symm

/-- On a nonempty connected scheme over an algebraically closed field, the canonical
constant-section map is bijective. Under every morphism over the field its pullback
is the constant section with the same value, without connectedness of the source.
Source: Stacks Project, Remark 59.23.2 (Tag 03P5), and Tags 093I and 093R
(blueprint: lem-weil-pbc-constant-sheaf-set-sections-connected-natural).

Proof: `lem-galois-constant-sheaf-sets-representable` identifies the constant sheaf
with the sheaf represented by the disjoint union of copies of the base, carrying
`e` to its coprojection. By `lem-galois-coproduct-copies-morphisms-clopen`, a section
is an indexed clopen decomposition. The nonempty connected base forces this
decomposition to have exactly one nonempty piece, by
`lem-weil-pbc-connected-locally-constant-map`, proving bijectivity.
For a morphism `v`, apply `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`;
its canonical isomorphism carries the unit-pullback of the section of value `e`
to that same constant value. No condition on `V` is used. In the formula the
base-changed terminal object is `U ×_U V`, canonically
isomorphic to `V`, so its sections are global sections on `V`. -/
theorem constantSheaf_set_sections_connected_natural
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (U : Scheme.{u}) [U.Over (Spec (.of Ω))] [ConnectedSpace U] (E : Type u) :
    Function.Bijective (fun e : E =>
      (toSheafify U.smallEtaleTopology
        ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
          (Opposite.op (Etale.mk (𝟙 U))) ⟨e⟩) ∧
    ∀ (V : Scheme.{u}) [V.Over (Spec (.of Ω))] (v : V ⟶ U) [v.IsOver (Spec (.of Ω))],
      let b := MorphismProperty.Over.pullback @Etale ⊤ v
      let F := (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (ULift.{u + 1, u} E)
      let G := (constantSheaf V.smallEtaleTopology (Type (u + 1))).obj
        (ULift.{u + 1, u} E)
      let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        b (Type (u + 1)) (U.smallGrothendieckTopology @Etale)
          (V.smallGrothendieckTopology @Etale)
      ∃ γ : (etaleSetPullback v).obj F ≅ G, ∀ e : E,
        γ.hom.hom.app (Opposite.op (b.obj (Etale.mk (𝟙 U))))
          (((adj.unit.app F).hom.app (Opposite.op (Etale.mk (𝟙 U))))
            ((toSheafify U.smallEtaleTopology
              ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
                (Opposite.op (Etale.mk (𝟙 U))) ⟨e⟩)) =
          (toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
              (Opposite.op (b.obj (Etale.mk (𝟙 U)))) ⟨e⟩ := by
  classical
  constructor
  · obtain ⟨hH, c, hc, φ, hφ, hIso, _⟩ := constantSheaf_sets_representable U E
    have := hIso
    let W := Etale.mk (𝟙 U)
    have hcbij : Function.Bijective (fun e : E ↦ c.app (Opposite.op W) ⟨e⟩) := by
      have hd := coproductConstant_bijective U E
      have hc' (e : E) : (c.app (Opposite.op W) ⟨e⟩).down.left =
          Sigma.ι (fun _ : E ↦ U) e := by
        have h := hc W e
        change _ = 𝟙 U ≫ Sigma.ι (fun _ : E ↦ U) e at h
        simpa only [Category.id_comp] using h
      constructor
      · intro e e' h
        apply hd.injective
        apply Subtype.ext
        simpa only [hc'] using congrArg (fun t ↦ t.down.left) h
      · intro t
        obtain ⟨e, he⟩ := hd.surjective ⟨t.down.left, t.down.w⟩
        refine ⟨e, ?_⟩
        apply ULift.ext
        apply Over.OverMorphism.ext
        exact (hc' e).trans (congrArg Subtype.val he)
    have hφbij : Function.Bijective (φ.hom.app (Opposite.op W)) := by
      exact (CategoryTheory.isIso_iff_bijective _).1 inferInstance
    have heq : (fun e : E ↦ φ.hom.app (Opposite.op W)
        ((toSheafify U.smallEtaleTopology
          ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
            (Opposite.op W) ⟨e⟩)) = (fun e : E ↦ c.app (Opposite.op W) ⟨e⟩) := by
      funext e
      exact congrArg (fun f ↦ f.app (Opposite.op W) ⟨e⟩) hφ
    apply (Function.Bijective.of_comp_iff' hφbij _).1
    change Function.Bijective (fun e : E ↦ φ.hom.app (Opposite.op W)
      ((toSheafify U.smallEtaleTopology
        ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
          (Opposite.op W) ⟨e⟩))
    rw [heq]
    exact hcbij
  · intro V _ v _
    obtain ⟨γ, hγ, hIso, _⟩ := etaleSetInverseImageConstantSheaf U V v E
    have := hIso
    exact ⟨asIso γ, hγ⟩

end AlgebraicGeometry.Scheme
