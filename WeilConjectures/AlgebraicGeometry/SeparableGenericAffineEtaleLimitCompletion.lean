/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SeparableGenericAffineEtaleStages
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed

/-! # Canonical strict-henselization completion steps

The two statements below are deliberately about the canonical reindexed
neighbourhood system.  They do not quantify over arbitrary diagrams or arbitrary
maps out of the specified separable closure.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

/-- Transport the canonical strict-henselization limit to the specified relative
separable closure.

Source: Stacks Project, Tags 04HX, 03QL and 0032; the landed declarations
`strictHenselizationAffineProperties` and `exists_directed_reindexing`.
(blueprint: new-lem-pd-separable-generic-affine-etale-limit)

The proof obtains the canonical colimit-to-residue comparison from the affine
étale neighbourhood/triple comparison, proves that the generic strict
henselization has zero maximal ideal, and transports the canonical inverse-limit
cone through the resulting ring isomorphism and the directed reindexing.
-/
theorem separableGeneric_affineEtale_limit
    (S : Scheme.{u}) [IsIntegral S]
    (Ω : Type u) [Field Ω] [Algebra S.functionField Ω]
    [IsAlgClosure S.functionField Ω] :
    let F := S.functionField
    let Fs := separableClosure F Ω
    let X := Spec (CommRingCat.of Fs)
    letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    let η : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ S.fromSpecFunctionField
    let J := SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods η)
    letI : SmallCategory J := inferInstance
    let D₀ := (Scheme.strictHenselizationAffineDiagram η).op ⋙ Scheme.Spec
    ∀ (A : Type u) (_ : Preorder A) (_ : IsDirected A (· ≤ ·)) (_ : Nonempty A)
      (R : A ⥤ Jᵒᵖ) (_ : Functor.Initial R.op)
      (π₀ : ∀ i : Aᵒᵖ,
        Spec (Scheme.strictHenselizationRing η) ⟶ (R.op ⋙ D₀).obj i)
      (hπcan : ∀ j : Aᵒᵖ,
        π₀ j = (Scheme.strictHenselizationCone η).π.app (R.op.obj j)),
      ∃ e : Scheme.strictHenselizationRing η ≃+* Fs,
        (∀ a : Scheme.strictHenselizationRing η,
          Fs.subtype (e a) = Scheme.strictHenselizationPointEvaluation η a) ∧
        Nonempty (IsLimit
          ({ pt := X
             π := { app := fun i ↦
                      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ π₀ i
                    naturality := by
                      intro i j f
                      change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ π₀ j =
                        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ π₀ i ≫
                          ((Scheme.strictHenselizationAffineDiagram η).op ⋙ Scheme.Spec).map (R.op.map f)
                      rw [hπcan j, hπcan i]
                      change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
                          (Scheme.strictHenselizationCone η).π.app (R.op.obj j) =
                        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
                          (Scheme.strictHenselizationCone η).π.app (R.op.obj i) ≫
                            ((Scheme.strictHenselizationAffineDiagram η).op ⋙ Scheme.Spec).map (R.op.map f)
                      simpa only [Category.assoc] using
                        (congrArg (fun q ↦
                          Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)
                          ((Scheme.strictHenselizationCone η).w (R.op.map f)).symm) } } :
            Cone (R.op ⋙ D₀))) := by
  sorry

/-- Pointedness of the canonical reindexed strict-henselization cone.

Source: Stacks Project, Tags 04HX and 03QL; the landed declaration
`strictHenselizationPointEvaluation_pointed`.
(blueprint: new-lem-pd-separable-generic-affine-etale-pointed)

The proof substitutes the canonical cone-leg equation from
`strictHenselizationPointEvaluation_pointed`, the displayed ring comparison,
and the structural-map equation for each canonical affine neighbourhood.
Functoriality of the over-category supplies the final map to `S`.
-/
theorem separableGeneric_affineEtale_pointed
    (S : Scheme.{u}) [IsIntegral S]
    (Ω : Type u) [Field Ω] [Algebra S.functionField Ω]
    [IsAlgClosure S.functionField Ω] :
    let F := S.functionField
    let Fs := separableClosure F Ω
    let X := Spec (CommRingCat.of Fs)
    letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    let η : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ S.fromSpecFunctionField
    let J := SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods η)
    letI : SmallCategory J := inferInstance
    let D₀ := (Scheme.strictHenselizationAffineDiagram η).op ⋙ Scheme.Spec
    ∀ (A : Type u) (_ : Preorder A) (_ : IsDirected A (· ≤ ·)) (_ : Nonempty A)
      (R : A ⥤ Jᵒᵖ)
      (π₀ : ∀ i : Aᵒᵖ,
        Spec (Scheme.strictHenselizationRing η) ⟶ (R.op ⋙ D₀).obj i)
      (u : ∀ i : A, (R.op ⋙ D₀).obj (op i) ⟶ S)
      (e : Scheme.strictHenselizationRing η ≃+* Fs)
      (hEval : ∀ a : Scheme.strictHenselizationRing η,
        Fs.subtype (e a) = Scheme.strictHenselizationPointEvaluation η a)
      (hπcan : ∀ j : Aᵒᵖ,
        π₀ j = (Scheme.strictHenselizationCone η).π.app (R.op.obj j))
      (hucan : ∀ i : A,
        u i =
          Spec.map (Scheme.ΓSpecIso
            (Opposite.unop ((equivSmallModel
              (Scheme.strictHenselizationNeighbourhoods η)).inverse.obj
                (Opposite.unop (R.obj i))).1.left)).inv ≫
            ((Scheme.AffineEtale.Spec S).obj
              ((equivSmallModel
                (Scheme.strictHenselizationNeighbourhoods η)).inverse.obj
                (Opposite.unop (R.obj i))).1).hom),
      ∀ i : A,
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ π₀ (op i) ≫ u i =
          Spec.map (CommRingCat.ofHom (algebraMap F Fs)) ≫ S.fromSpecFunctionField := by
  sorry

end
end AlgebraicGeometry
