/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import Sheaf.AlgebraicGeometry.ClosedProperSupportLocality
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Canonical proper-support pullback map

Source: Stacks Project, More on Étale Cohomology, Tag 0F55 (lemma-base-change-f-shriek-separated).
(blueprint: lem-cbc-proper-support-pullback-section-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry

/-- The projection of the pulled-back étale test scheme to the original test scheme.
Source: Stacks Project, More on Étale Cohomology, Tag 0F55.
(blueprint: lem-cbc-proper-support-pullback-section-map) -/
noncomputable def properSupportBaseChangeProjection
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
      ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)).left ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U).left := by
  let U' := (MorphismProperty.Over.pullback @Etale ⊤ b).obj U
  have h :
      (pullback.snd U'.hom f' ≫ a) ≫ f =
        (pullback.fst U'.hom f' ≫ pullback.fst U.hom b) ≫ U.hom := by
    simp only [Category.assoc]
    rw [sq.w]
    rw [← Category.assoc, ← (pullback.condition (f := U'.hom) (g := f'))]
    rw [CategoryTheory.MorphismProperty.Over.pullback_obj_hom]
    simp only [Category.assoc]
    rw [← (pullback.condition (f := U.hom) (g := b))]
  let q₀ : pullback U'.hom f' ⟶ pullback U.hom f :=
    pullback.lift (pullback.fst U'.hom f' ≫ pullback.fst U.hom b)
      (pullback.snd U'.hom f' ≫ a) h.symm
  simpa only [CategoryTheory.MorphismProperty.Over.pullback_obj_left, U'] using q₀

/-- The lift of the Cartesian projection to the pulled-back étale test object.
Source: Stacks Project, Tag 0F55, evaluation of the ordinary pullback map.
(blueprint: lem-cbc-proper-support-pullback-section-map) -/
noncomputable def properSupportBaseChangeEtaleMap
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b) (U : Y.Etale) :
    (MorphismProperty.Over.pullback @Etale ⊤ f').obj
        ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ a).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (properSupportBaseChangeProjection a f b f' sq U)
      (pullback.snd _ f') (by
        simp [properSupportBaseChangeProjection]))
    (by simp)

/-- Unit pullback on all ambient sections, followed by restriction along the canonical lift.
Source: Stacks Project, Tag 0F55; Étale Cohomology, equation-pullback.
(blueprint: lem-cbc-proper-support-pullback-section-map) -/
noncomputable def properSupportUnitPullback
    {Λ : Type (u + 1)} [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale) :
    F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ⟶
      ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
          ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ≫
    ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj.map
      (properSupportBaseChangeEtaleMap a f b f' sq U).op

/-- The unit of constant-coefficient inverse image induces the canonical pullback map on
sections with proper geometric support in a Cartesian square.
Source: Stacks Project, More on Étale Cohomology, Tag 0F55 (lemma-base-change-f-shriek-separated).
(blueprint: lem-cbc-proper-support-pullback-section-map)

Proof:
1. Evaluate the constant-coefficient inverse-image/direct-image unit on each étale
object (prop-weil-pbc-inverse-image-modules-exact). Restrict along
`properSupportBaseChangeEtaleMap`, the lift of `properSupportBaseChangeProjection`.
This gives `properSupportUnitPullback` on every ambient section before imposing support.
2. The inverse-image stalk-and-germ comparison (lem-weil-pbc-inverse-image-stalk-germ)
identifies nonzero germs with those over the original point. The zero-open criterion
(lem-sc-etale-section-zero-open) makes this exactly equality of the support loci.
3. Local finite type is stable under base change (lem-weil-pbc-lft-base-change).
Closed proper supports pull back to closed proper supports
(lem-cbc-closed-proper-support-locality). The section descriptions therefore put the
unit image in H. The monomorphism ιH makes this lift unique and hence linear.
4. Naturality of the unit on test objects makes the lifts commute with restriction;
monicity of ιH detects these equalities. Thus the lifts form the sheaf morphism α.
The displayed component equation determines α uniquely, proving canonicity.
5. A coefficient morphism decreases support, and properness passes to closed subsets
(lem-weil-pbc-closed-subset-proper-over-base-properties). Thus it induces the maps γ
and δ between proper-support subsheaves. Naturality of the unit, followed by restriction,
identifies the two ambient composites. Monicity of the target inclusion ιH₂ yields
γ ≫ α₂ = α ≫ b_*δ, the stated coefficient-naturality square. -/
theorem properSupportPullbackSectionMap
    {Λ : Type (u + 1)} [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f]
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ιG : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F)
    (ιH : H ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) f').obj
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F))
    [Mono ιG] [Mono ιH]
    (hG : ∀ (U : Y.Etale)
      (s : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj.obj (op U)),
      (∃ t, (ιG.hom.app (op U)) t = s) ↔
        SectionHasProperSupport Λ F
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)
          (pullback.fst U.hom f) s)
    (hH : ∀ (V : Y'.Etale)
      (s : ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj.obj (op V)),
      (∃ t, (ιH.hom.app (op V)) t = s) ↔
        @SectionHasProperSupport Λ _ X' V.left
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
          ((MorphismProperty.Over.pullback @Etale ⊤ f').obj V)
          (pullback.fst V.hom f')
          (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
            (IsPullback.of_hasPullback V.hom f').flip
            (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance)) s) :
    ∃ α : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) b).obj H,
      (∀ (U : Y.Etale) (s : G.obj.obj (op U)),
        (ιH.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)))
            ((α.hom.app (op U)) s) =
          (properSupportUnitPullback a f b f' sq F U)
            ((ιG.hom.app (op U)) s)) ∧
      (∀ (U : Y.Etale) (s : G.obj.obj (op U)) (t : H.obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))),
        t = (α.hom.app (op U)) s →
        ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (v : Spec (.of Ω) ⟶
            ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
              ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)).left),
          ((Scheme.pointSmallEtale
            (v ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
              ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)).hom)).toPresheafFiber
                ((MorphismProperty.Over.pullback @Etale ⊤ f').obj
                  ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))
                (Over.homMk v) ((upperStar (ModuleCat.{u + 1} Λ) a).obj F).obj
                  ((ιH.hom.app
                    (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U))).hom t) ≠ 0) ↔
          ((Scheme.pointSmallEtale
            ((v ≫ properSupportBaseChangeProjection a f b f' sq U) ≫
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U).hom)).toPresheafFiber
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)
                (Over.homMk (v ≫ properSupportBaseChangeProjection a f b f' sq U))
                F.obj ((ιG.hom.app (op U)) s) ≠ 0)) ∧
      (∀ (F₂ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (G₂ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (H₂ : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (ιG₂ : G₂ ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F₂)
        (ιH₂ : H₂ ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F₂)) [Mono ιH₂]
        (φ : F ⟶ F₂) (γ : G ⟶ G₂) (δ : H ⟶ H₂)
        (α₂ : G₂ ⟶ (lowerStar (ModuleCat.{u + 1} Λ) b).obj H₂),
        γ ≫ ιG₂ = ιG ≫ (lowerStar (ModuleCat.{u + 1} Λ) f).map φ →
        δ ≫ ιH₂ = ιH ≫ (lowerStar (ModuleCat.{u + 1} Λ) f').map
          ((upperStar (ModuleCat.{u + 1} Λ) a).map φ) →
        (∀ (U : Y.Etale) (s : G₂.obj.obj (op U)),
          (ιH₂.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)))
              ((α₂.hom.app (op U)) s) =
            (properSupportUnitPullback a f b f' sq F₂ U)
              ((ιG₂.hom.app (op U)) s)) →
        γ ≫ α₂ = α ≫ (lowerStar (ModuleCat.{u + 1} Λ) b).map δ) := by
  sorry

end AlgebraicGeometry.Etale
