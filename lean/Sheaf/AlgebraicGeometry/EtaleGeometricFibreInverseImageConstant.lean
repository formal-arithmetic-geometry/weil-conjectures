/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Inverse image over a geometric point is constant

Source: Stacks Project, Étale Cohomology, Lemma 59.39.3 (Tag 0A3H), final paragraph
(blueprint: lem-weil-pbc-etale-geometric-fibre-inverse-image-constant).
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Lemma 59.39.3 (Tag 0A3H), final paragraph
(blueprint: lem-weil-pbc-etale-geometric-fibre-inverse-image-constant).
The inverse image along `h ≫ s` is naturally the constant sheaf of the geometric stalk.
The isomorphism at `Spec Ω` sends each pulled-back pointed section to its germ,
fixing the canonical identification. The family is compatible with every further
morphism over `Ω`.
This compatibility is expressed on constant-presheaf generators: pulling a generator
back through the inverse-image unit and its composition comparison gives the generator
with the same stalk value on the source. Sheafification makes this equivalent to the
usual square with the canonical inverse-image comparison for constant sheaves.
The composition comparison is the unit-preserving witness of
`etaleSetInverseImageCompositionUnits`, whose uniqueness makes the choice immaterial.

Proof:
1. Put `G = s⁻¹F`. By lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant,
   the constant sheaf of the global sections of `G` is canonically `G`.
2. The same lemma identifies these sections with the stalk at the identity point.
   By lem-weil-pbc-sets-etale-inverse-image-stalk-germ this is the stalk of `F` at `s`,
   compatibly with germs of pulled-back sections.
3. Pull this identification back along `h`. Use
   lem-weil-pbc-sets-etale-inverse-image-composition-units to compare the iterated
   inverse image with that along `h ≫ s`, and
   lem-weil-pbc-sets-etale-inverse-image-constant-sheaf to pull back the constant sheaf.
4. Naturality in `F` follows from the naturality of all three comparisons.
   For `v : V → U`, associativity of the composition comparison and the fact that
   the constant-sheaf comparison preserves constant generators give the displayed
   equation. Its uniqueness extends the equality from generators to sheaf morphisms,
   giving naturality in `U` and in every further `Ω`-morphism. -/
theorem etaleGeometricFibreInverseImageConstant
    (S : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ α : ∀ (U : Scheme.{u}) (h : U ⟶ Spec (.of Ω)),
      Scheme.etaleSetPullback (h ≫ s) ≅
        (Scheme.pointSmallEtale s).sheafFiber ⋙
          constantSheaf U.smallEtaleTopology (Type (u + 1)),
      (∀ (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (W : S.Etale)
        (t : (Scheme.pointSmallEtale s).fiber.obj W)
        (a : Scheme.Etale.mk (𝟙 (Spec (.of Ω))) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 (Spec (.of Ω)) ≫ s)).obj W)
        (σ : F.obj.obj (op W)),
        a.left ≫ CategoryTheory.Limits.pullback.fst W.hom (𝟙 (Spec (.of Ω)) ≫ s) =
          t.left →
        ((α (Spec (.of Ω)) (𝟙 _)).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
          (((Scheme.etaleSetPullback (𝟙 (Spec (.of Ω)) ≫ s)).obj F).obj.map a.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 (Spec (.of Ω)) ≫ s))
              (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
              ((Spec (.of Ω)).smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op W) σ)) =
        (toSheafify (Spec (.of Ω)).smallEtaleTopology
          ((Functor.const (Spec (.of Ω)).Etaleᵒᵖ).obj
            ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
              (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
              ((Scheme.pointSmallEtale s).toPresheafFiber W t F.obj σ)) ∧
      ∀ (U V : Scheme.{u}) (h : U ⟶ Spec (.of Ω)) (v : V ⟶ U)
        (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
        (W : U.Etale) (e : (Scheme.pointSmallEtale s).sheafFiber.obj F),
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S U V (h ≫ s) v).hom.app F).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
            (U.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app (op W)
            (((α U h).inv.app F).hom.app (op W)
              ((toSheafify U.smallEtaleTopology
                ((Functor.const U.Etaleᵒᵖ).obj
                  ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app (op W) e))) =
        (((α V (v ≫ h)).inv.app F ≫
          eqToHom (congrArg
            (fun k : V ⟶ S => (Scheme.etaleSetPullback k).obj F)
            (Category.assoc v h s))).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
          ((toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj
              ((Scheme.pointSmallEtale s).sheafFiber.obj F))).app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e) := by
  sorry

end AlgebraicGeometry
