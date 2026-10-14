/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.OverlapSingleChartRestriction

/-! # Restricting a conjugated transition to an iterated overlap

Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-conjugate-restriction). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry
noncomputable section
set_option allowUnsafeReducibility true
attribute [local reducible] Precoverage.ZeroHypercover.pullback₁
  Scheme.Cover.pullbackHom
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The comparison of tensor and abstract inverse image determined by their adjunctions.
Source: Stacks Project, Tag 0096.
(blueprint: lem-pc-overlap-conjugate-restriction). -/
@[irreducible]
def overlapAdjunctionComparison {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
  Adjunction.leftAdjointUniq
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction p)

/-- The direct model comparison with prescribed chart projections.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: lem-pc-overlap-conjugate-restriction). -/
@[irreducible]
def overlapDirectModelComparison {H H₀ A B : Scheme.{u}}
    (t : H ⟶ H₀) (r : H₀ ⟶ A) (k : H ⟶ A)
    (v : H ⟶ B) (u : B ⟶ A) (htr : t ≫ r = k) (hvu : v ≫ u = k)
    (N : A.Modules) :
    (Scheme.Modules.tensorPullback t).obj ((Scheme.Modules.pullback r).obj N) ≅
      (Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback u).obj N) :=
  (overlapAdjunctionComparison t).app _ ≪≫
    pullbackCompOfEq t r k htr N ≪≫ (pullbackCompOfEq v u k hvu N).symm

/-- The stage model comparison with prescribed chart projections.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: lem-pc-overlap-conjugate-restriction). -/
@[irreducible]
def overlapStageModelComparison {K H H₀ A B : Scheme.{u}}
    (d : K ⟶ H) (q : H ⟶ H₀) (r : H₀ ⟶ A)
    (s : K ⟶ B) (u : B ⟶ A) (h : (d ≫ q) ≫ r = s ≫ u) (N : A.Modules) :
    (Scheme.Modules.pullback d).obj
        ((Scheme.Modules.tensorPullback q).obj ((Scheme.Modules.pullback r).obj N)) ≅
      (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback u).obj N) :=
  (Scheme.Modules.pullback d).mapIso ((overlapAdjunctionComparison q).app _) ≪≫
    (Scheme.Modules.pullbackComp d q).app _ ≪≫
    pullbackCompOfEq (d ≫ q) r (s ≫ u) h N ≪≫
    ((Scheme.Modules.pullbackComp s u).app N).symm

/-- The part of the iterated comparison preceding the component isomorphism.
Source: Stacks Project, Tag 0095.
(blueprint: lem-pc-overlap-conjugate-restriction). -/
def overlapIteratedRestrictionIso {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀) :
    (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapIteratedChartHom U q p t h d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) :=
  (Scheme.Modules.pullbackComp _ _).app (N d) ≪≫
    (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _).symm).app (N d) ≪≫
    ((Scheme.Modules.pullbackComp _ _).app (N d)).symm

/-- Comparison from a model restriction to the iterated chart restriction.
Source: Stacks Project, Tag 0095, composition of inverse images.
(blueprint: lem-pc-overlap-conjugate-restriction). -/
def overlapDirectRestrictionIso {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (a b d : U.I₀)
    (hd : H ⟶ (U.pullback₁ t).X d)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (r : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ ((U.pullback₁ q).pullback₁ p).X d)
    (hz : z ≫ hd = r ≫ overlapIteratedChartHom U q p t h d)
    (S : H.Modules)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))) :
    (Scheme.Modules.pullback z).obj S ≅
      (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
          ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d))) :=
  (Scheme.Modules.pullback z).mapIso τ ≪≫
    pullbackCompOfEq z hd (r ≫ overlapIteratedChartHom U q p t h d) hz
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) ≪≫
    ((Scheme.Modules.pullbackComp r (overlapIteratedChartHom U q p t h d)).app _).symm ≪≫
    (Scheme.Modules.pullback r).mapIso (overlapIteratedRestrictionIso U q p t h N d).symm

/-- The explicit conjugation of a transition on a direct model overlap.
Source: Stacks Project, Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-conjugate-restriction). -/
@[irreducible]
def overlapConjugatedTransition {X Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (t : Z ⟶ X) (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) : S ⟶ T :=
  let D := (modulesPseudofunctor.toDescentData (U.pullback₁ t).f).obj M
  τa.hom ≫ (Scheme.Modules.pullback ha).map (e a).hom ≫
    D.hom ν ha hb hνa hνb ≫ (Scheme.Modules.pullback hb).map (e b).inv ≫ τb.inv


/-- Explicit-transition intermediate for the conjugated restriction theorem.
A pair morphism whose base change is this restricted conjugate satisfies the pair square.
There is no tensor stage morphism or recovery hypothesis in this statement.
Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-conjugate-restriction-explicit).

Proof: Substitute the equation naming the conjugated transition. Expand the two
direct restriction isomorphisms. Naturality moves the
pullbacks of the component maps through the composition comparisons. Cancel
τ_a and τ_b against their inverses. The naturality equation of the descent datum
on the direct cover identifies the pulled-back transition along z with the
transition on the maps r_a followed by the iterated chart map and r_b followed
by that map. The composition pentagon then identifies its two exterior
comparisons with the comparisons for the descent datum of M on the iterated
cover. The source comparison becomes the hom of overlapIteratedComparison;
the inverse target comparison cancels its hom. Substitute the given base-change
identity and use associativity to obtain overlapPairSquare. Projection equations hz_a,
hz_b and hν give exactly the prescribed base and chart maps. This argument
uses only naturality and invertible comparisons, and also applies to empty
overlaps, repeated charts, zero modules, and identity base changes. -/
theorem overlap_conjugate_restriction_explicit {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) (θ : S ⟶ T) :
    let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
      (pullback.fst _ _) hza S τa
    let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
      (pullback.snd _ _) hzb T τb
    let W := (U.pullback₁ q).pullback₁ p
    let D := (modulesPseudofunctor.toDescentData W.f).obj M
    let ε := overlapIteratedComparison U q p t h N M e
    let V : Y.OpenCover.{u} := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    ∀ (φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b)),
      modulesPseudofunctor.overlapPairBaseChangeHom (V.f a) (V.f b) p
        (V.pullbackHom p a) (V.pullbackHom p b) (W.f a) (W.f b)
        (V.pullbackHom_map p a) (V.pullbackHom_map p b) (A a) (A b) φ =
        ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom →
      overlapPairSquare V A p D ε a b φ := by sorry

theorem overlap_conjugate_restriction {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) :
    ∀ (θ : S ⟶ T),
      θ = overlapConjugatedTransition U t N M e a b ν ha hb hνa hνb S T τa τb →
    let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
      (pullback.fst _ _) hza S τa
    let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
      (pullback.snd _ _) hzb T τb
    let W := (U.pullback₁ q).pullback₁ p
    let D := (modulesPseudofunctor.toDescentData W.f).obj M
    let ε := overlapIteratedComparison U q p t h N M e
    let V : Y.OpenCover.{u} := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    ∀ (φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b)),
      modulesPseudofunctor.overlapPairBaseChangeHom (V.f a) (V.f b) p
        (V.pullbackHom p a) (V.pullbackHom p b) (W.f a) (W.f b)
        (V.pullbackHom_map p a) (V.pullbackHom_map p b) (A a) (A b) φ =
        ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom →
      overlapPairSquare V A p D ε a b φ := by
  intro θ hθ
  subst θ
  apply overlap_conjugate_restriction_explicit U q p t h N M e a b ν ha hb hνa hνb
    z hza hzb S T τa τb

end
end AlgebraicGeometry
