/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraColimit

/-!
# Existence of inverse limits with affine transition morphisms

Source: Stacks Project, Limits, Lemmas 01YX and 01YW
(blueprint: lem-weil-pbc-limit-affine-transition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Core existence of the limit cone for a cofiltered diagram with affine transitions.

The proof constructs the relative spectrum of the filtered colimit of the pushforward
structure algebras along one stage.  On every affine open of that stage, the resulting
cone is the spectrum of a filtered colimit of rings, hence is limiting; compatible local
factorizations glue uniquely.  This is the construction in Stacks, Limits, Lemma 01YX.
(blueprint: lem-weil-pbc-limit-affine-transition-core). -/
theorem exists_limit_affine_transition_core
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] :
    ∃ c : Cone D, Nonempty (IsLimit c) := by
  sorry

/-- The affine-stage comparison for a limiting cone.

When every stage is affine, the cone with vertex the spectrum of the filtered colimit of
global sections is limiting by the affine-scheme limit theorem.  Uniqueness of limits then
gives the displayed isomorphism and its compatibility with every projection.  This is
Stacks, Limits, Lemma 01YW (blueprint: lem-weil-pbc-limit-affine-transition-affine-comparison).
-/
theorem limit_affine_transition_affine_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (ha : ∀ i : Iᵒᵖ, IsAffine (D.obj i)) :
    ∃ e : c.pt ≅ Spec (colimit (D.op ⋙ Scheme.Γ)),
      ∀ i : Iᵒᵖ, e.hom ≫ Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (op i)) =
        c.π.app i ≫ (ΓSpec.adjunction.unit.app (D.obj i)) := by
  let (i : Iᵒᵖ) : IsAffine (D.obj i) := ha i
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let (i : Iᵒᵖᵒᵖ) : IsAffine (D.op.obj i).unop := ha i.unop
  let hΓ := isColimitOfPreserves Scheme.Γ hc.op
  let eΓ := hΓ.coconePointUniqueUpToIso (colimit.isColimit (D.op ⋙ Scheme.Γ))
  refine ⟨c.pt.isoSpec ≪≫ Scheme.Spec.mapIso eΓ.symm.op, ?_⟩
  intro i
  change c.pt.isoSpec.hom ≫ Spec.map eΓ.inv ≫
    Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (op i)) = _
  rw [← Spec.map_comp]
  have hι := hΓ.comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit (D.op ⋙ Scheme.Γ)) (op i)
  change colimit.ι (D.op ⋙ Scheme.Γ) (op i) ≫ eΓ.inv = (c.π.app i).appTop at hι
  rw [hι]
  exact Scheme.isoSpec_hom_naturality (X := c.pt) (Y := D.obj i) (c.π.app i)

/-- An inverse system over a directed set with affine transition morphisms has a limit,
its projections are affine, and inverse images of arbitrary opens of any stage are limits
of the corresponding inverse images. For affine stages the limit is the spectrum of the
colimit of their global sections.

Source: Stacks Project, Limits, Lemmas 01YX and 01YW
(blueprint: lem-weil-pbc-limit-affine-transition). -/
theorem exists_limit_affine_transition
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] :
    ∃ c : Cone D, Nonempty (IsLimit c) ∧
      (∀ i : Iᵒᵖ, IsAffineHom (c.π.app i)) ∧
      (∀ (i : Iᵒᵖ) (U : (D.obj i).Opens),
        Nonempty (IsLimit (opensCone D c i U)) ∧
          ∀ {j k : Over i} (f : j ⟶ k), IsAffineHom ((opensDiagram D i U).map f)) ∧
      ((∀ i : Iᵒᵖ, IsAffine (D.obj i)) →
        ∃ e : c.pt ≅ Spec (colimit (D.op ⋙ Scheme.Γ)),
          ∀ i : Iᵒᵖ, e.hom ≫ Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (op i)) =
            c.π.app i ≫ (ΓSpec.adjunction.unit.app (D.obj i))) := by
  obtain ⟨c, ⟨hc⟩⟩ := exists_limit_affine_transition_core D
  refine ⟨c, ⟨hc⟩, ?_, ?_, ?_⟩
  · intro i
    exact isAffineHom_π_app D c hc i
  · intro i U
    refine ⟨⟨isLimitOpensCone D c hc i U⟩, ?_⟩
    intro j k f
    infer_instance
  · intro ha
    exact limit_affine_transition_affine_comparison D c hc ha

end AlgebraicGeometry
