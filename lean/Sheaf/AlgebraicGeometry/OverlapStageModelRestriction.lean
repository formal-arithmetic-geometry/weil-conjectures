/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.OverlapConjugateRestriction
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Restricting a stage morphism through a commutative model diagram

Source: Stacks Project, Tags 0095 and 0096; Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-stage-model-restriction). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport of any stage morphism through the model square.
This is transport of an arbitrary tensor compatibility equation, independent of
a limit module, its component isomorphisms, or a prescribed descent transition.
Source: Stacks Project, Tags 0095 and 0096; Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-stage-model-restriction).

Proof: Substitute the four comparison equalities. Expand the stage comparison
and the two direct restriction comparisons.
Use functoriality to separate the three factors defining the stage morphism.
Naturality of the composition comparisons moves the central morphism alpha
past them. The equality z ≫ p₀ = l ≫ d identifies the two inverse-image
routes from the iterated overlap to Hₖ. For each chart, the associativity
pentagon and the stated projection equations identify the exterior
composition comparisons. Convert tensor pullbacks to abstract pullbacks
using the unique adjunction comparison. The comparison for the composite
is compatible with the two individual comparisons: apply conjugateIsoEquiv
to both sides, where both become the same pushforward composition map.
The resulting middle factors are σ_F, the tensor pullback of alpha, and
σ_G inverse. Postcompose the supplied compatibility equation by σ_G inverse
and cancel σ_G to identify this middle morphism with theta. Substitute the
equation naming phi. Cancel the remaining source and target comparisons. No
faithfulness or finiteness is used; all arrows may be identities and any
overlap or module may be empty or zero. -/
theorem overlap_stage_model_restriction
    {X Y Z H₀ Hₖ Hlim : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (a b : U.I₀)
    (q₀ : Hₖ ⟶ H₀) (p₀ : Hlim ⟶ Hₖ) (t₀ : Hlim ⟶ H₀) (h₀ : p₀ ≫ q₀ = t₀)
    (r₀a : H₀ ⟶ U.X a) (r₀b : H₀ ⟶ U.X b)
    (d : pullback ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) ⟶ Hₖ)
    (ha : Hlim ⟶ (U.pullback₁ t).X a) (hb : Hlim ⟶ (U.pullback₁ t).X b)
    (hka : (d ≫ q₀) ≫ r₀a = pullback.fst _ _ ≫ U.pullbackHom q a)
    (hkb : (d ≫ q₀) ≫ r₀b = pullback.snd _ _ ≫ U.pullbackHom q b)
    (ka : Hlim ⟶ U.X a) (kb : Hlim ⟶ U.X b)
    (hla : t₀ ≫ r₀a = ka) (hlb : t₀ ≫ r₀b = kb)
    (hda : ha ≫ U.pullbackHom t a = ka)
    (hdb : hb ≫ U.pullbackHom t b = kb)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ Hlim)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (hz : z ≫ p₀ =
      pullback.lift
        (pullback.fst _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
        (pullback.snd _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p b) (by
          rw [Category.assoc, Category.assoc, Scheme.Cover.pullbackHom_map,
            Scheme.Cover.pullbackHom_map, ← Category.assoc, ← Category.assoc,
            pullback.condition]) ≫ d) :
    let F := (Scheme.Modules.pullback r₀a).obj (N a)
    let G := (Scheme.Modules.pullback r₀b).obj (N b)
    let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ h₀
    let canonicalτa := overlapDirectModelComparison t₀ r₀a ka ha
      (U.pullbackHom t a) hla hda (N a)
    let canonicalτb := overlapDirectModelComparison t₀ r₀b kb hb
      (U.pullbackHom t b) hlb hdb (N b)
    let canonicalsa := overlapStageModelComparison d q₀ r₀a
      (pullback.fst _ _) (U.pullbackHom q a) hka (N a)
    let canonicalsb := overlapStageModelComparison d q₀ r₀b
      (pullback.snd _ _) (U.pullbackHom q b) hkb (N b)
    ∀ (τa : (Scheme.Modules.tensorPullback t₀).obj F ≅
        (Scheme.Modules.pullback ha).obj
          ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
      (τb : (Scheme.Modules.tensorPullback t₀).obj G ≅
        (Scheme.Modules.pullback hb).obj
          ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b)))
      (sa : (Scheme.Modules.pullback d).obj ((Scheme.Modules.tensorPullback q₀).obj F) ≅
        (Scheme.Modules.pullback
          (pullback.fst ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
          ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)))
      (sb : (Scheme.Modules.pullback d).obj ((Scheme.Modules.tensorPullback q₀).obj G) ≅
        (Scheme.Modules.pullback
          (pullback.snd ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
          ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))),
      τa = canonicalτa → τb = canonicalτb → sa = canonicalsa → sb = canonicalsb →
    let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
      (pullback.fst _ _) hza ((Scheme.Modules.tensorPullback t₀).obj F) τa
    let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
      (pullback.snd _ _) hzb ((Scheme.Modules.tensorPullback t₀).obj G) τb
    ∀ α : (Scheme.Modules.tensorPullback q₀).obj F ⟶
        (Scheme.Modules.tensorPullback q₀).obj G,
    ∀ θ : (Scheme.Modules.tensorPullback t₀).obj F ⟶
        (Scheme.Modules.tensorPullback t₀).obj G,
      σ.hom.app F ≫ (Scheme.Modules.tensorPullback p₀).map α = θ ≫ σ.hom.app G →
    ∀ φ : (Scheme.Modules.pullback
        (pullback.fst ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
        ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)) ⟶
      (Scheme.Modules.pullback
        (pullback.snd ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
        ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b)),
      φ = sa.inv ≫ (Scheme.Modules.pullback d).map α ≫ sb.hom →
      modulesPseudofunctor.overlapPairBaseChangeHom
        ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) p
        (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
        (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)
        (((U.pullback₁ q).pullback₁ p).f a) (((U.pullback₁ q).pullback₁ p).f b)
        (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p a)
        (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p b)
        ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))
        ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))
        φ = ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom := by sorry

end
end AlgebraicGeometry
