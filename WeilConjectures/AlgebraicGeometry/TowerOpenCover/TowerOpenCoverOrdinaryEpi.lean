/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import all WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Covering ordinary counits are jointly epimorphic.
Source: current blueprint, tower-geometric Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-ordinary-epi).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

private theorem iso_map_eq {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} {a b : M ⟶ N}
    (h : F.map a = F.map b) : G.map a = G.map b := by
  apply (cancel_epi (e.hom.app M)).1
  rw [← e.hom.naturality, ← e.hom.naturality, h]

private theorem sheaf_eq_of_cover {C A : Type*} [Category* C] [Category* A]
    {J : GrothendieckTopology C} {ι : Type*} {U : ι → C}
    (hU : J.CoversTop U) {M N : Sheaf J A} {a b : M ⟶ N}
    (h : ∀ i, (J.overPullback A (U i)).map a = (J.overPullback A (U i)).map b) :
    a = b := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply N.property.hom_ext (hU.cover W.unop)
  rintro ⟨Y, f, ⟨i, ⟨g⟩⟩⟩
  have he := congrArg (fun k ↦ k.hom.app (op (Over.mk g))) (h i)
  change a.hom.app (op Y) = b.hom.app (op Y) at he
  change a.hom.app W ≫ N.obj.map f.op = b.hom.app W ≫ N.obj.map f.op
  rw [← a.hom.naturality, ← b.hom.naturality, he]

private theorem slice_restriction_map_eq {S Z : Scheme.{u}} (j : S ⟶ Z)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : _)
    {M N : proEtaleRingModules Z R} {a b : M ⟶ N}
    (h : (proEtaleRingModulePullback.{u} j R R' c).map a =
      (proEtaleRingModulePullback.{u} j R R' c).map b) :
    (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (ProEt.mk j)).map a =
    (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (ProEt.mk j)).map b := by
  let F := proEtaleRingModulePullback.{u} j R R' c
  let G := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (ProEt.mk j)
  have : G.Additive := ⟨by intros; rfl⟩
  let d : M ⟶ N := a - b
  have hd : F.map d = 0 := by simp [F, d, Functor.map_sub, h]
  have hk : IsIso (F.map (kernel.ι d)) :=
    KernelFork.IsLimit.isIso_ι _ (isLimitOfHasKernelOfPreservesLimit F d) hd
  let := hk
  have hg : IsIso (G.map (kernel.ι d)) :=
    Scheme.RingedRestrictionExchange.slice_restriction_isIso j R R' c (kernel.ι d)
  let := hg
  let e := asIso (G.map (kernel.ι d))
  have hz : G.map d = 0 := by
    have hc : e.hom ≫ G.map d = 0 := by
      change G.map (kernel.ι d) ≫ G.map d = 0
      rw [← G.map_comp, kernel.condition, G.map_zero]
    calc
      G.map d = e.inv ≫ (e.hom ≫ G.map d) := by simp
      _ = 0 := by rw [hc, comp_zero]
  apply sub_eq_zero.mp
  change G.map a - G.map b = 0
  simpa only [d, G.map_sub] using hz

private theorem finite_pull_jointly_faithful
    {X : Scheme.{u}} (A : Type u) [CommRing A] (ι : Type (u + 1))
    (V : ι → Scheme.{u}) (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (cover : ∀ x : X, ∃ (i : ι) (v : V i), (j i).base v = x)
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)} {a b : M ⟶ N}
    (h : ∀ i, (proEtaleConstantRingPullback A (j i)).map a =
      (proEtaleConstantRingPullback A (j i)).map b) : a = b := by
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)
  apply (SheafOfModules.toSheaf R).map_injective
  apply sheaf_eq_of_cover
    (Scheme.RingedRestrictionExchange.opens_coverTop V j cover)
  intro i
  have hi := slice_restriction_map_eq (j i) (proEtaleConstantRing X A)
    (proEtaleConstantRing (V i) A) (proEtaleConstantRingComparison (j i) A) (h i)
  exact congrArg (SheafOfModules.toSheaf (R.over (ProEt.mk (j i)))).map hi

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

set_option maxHeartbeats 2000000 in
-- Comparing the two evaluations expands the fixed coefficient transports.
private theorem ordinary_pull_jointly_faithful {U V X : Scheme.{u}}
    (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (cover : Set.range jU ∪ Set.range jV = Set.univ)
    {M N : SpTowerShriek.S l E X} {a c : M ⟶ N}
    (hU : (o.geometry jU).pull.map a = (o.geometry jU).pull.map c)
    (hV : (o.geometry jV).pull.map a = (o.geometry jV).pull.map c) : a = c := by
  have hn (n : ℕ) : (SpTowerShriek.ev l E X n).map a =
      (SpTowerShriek.ev l E X n).map c := by
    let Z : ULift.{u + 1} Bool → Scheme.{u} := fun i ↦ Bool.rec V U i.down
    let j : ∀ i, Z i ⟶ X := fun i ↦ by
      rcases i with ⟨i⟩
      cases i
      · exact jV
      · exact jU
    have (i : ULift.{u + 1} Bool) : IsOpenImmersion (j i) := by
      rcases i with ⟨i⟩
      cases i <;> dsimp [j, Z] <;> infer_instance
    apply finite_pull_jointly_faithful (SpTowerShriek.R l E n) _ Z j
    · intro x
      have hx : x ∈ Set.range jU ∪ Set.range jV := by rw [cover]; trivial
      rcases hx with ⟨v, hv⟩ | ⟨v, hv⟩
      · exact ⟨⟨true⟩, v, hv⟩
      · exact ⟨⟨false⟩, v, hv⟩
    · rintro ⟨i⟩
      cases i
      · exact iso_map_eq ((o.geometry jV).ordinaryPullEvaluation n)
          (congrArg (SpTowerShriek.ev l E V n).map hV)
      · exact iso_map_eq ((o.geometry jU).ordinaryPullEvaluation n)
          (congrArg (SpTowerShriek.ev l E U n).map hU)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext x
  exact congrArg (fun f ↦ f.val.app (op Z.unop.2) x) (hn Z.unop.1)

/-- The sum of the ordinary extension counits is epi for a covering pair.
No overlap object or nested comparison occurs in this assertion.

Source: current blueprint, tower-geometric Gluing paragraph; Stacks 03DI--03DJ.
(blueprint: lem-dla1-tower-open-cover-ordinary-epi).

Proof: Sheaf separatedness makes restriction to a covering family jointly faithful.
To compare native geometric restriction with slice restriction, take the kernel
of the difference of two maps. Exact native pullback makes its inclusion invertible
when the pulled-back maps agree. The proved ringed open comparison transfers that
invertibility to the slice; cancellation gives equality on the slice. Apply this
at each coefficient level, using the specified ordinary evaluation comparisons.
Strict tower maps are equal when their component functions at every (n,T) agree.
Finally, equality after precomposition with the counit sum gives equality after
precomposition with each counit. The adjunction Hom bijection and triangle identity
identify these equations with equality after restriction to the two opens, so joint
faithfulness proves the desired right-cancellation. The proof includes empty X,
empty or repeated opens, and zero towers. -/
theorem ordinaryCounitSum_epi {U V X : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    (_cover : Set.range jU ∪ Set.range jV = Set.univ) (M : SpTowerShriek.S l E X) :
    Epi (biprod.desc ((o.openOp jU).ordinaryAdjunction.counit.app M)
      ((o.openOp jV).ordinaryAdjunction.counit.app M)) := by
  constructor
  intro N a c h
  apply ordinary_pull_jointly_faithful l E b o jU jV _cover
  · have he := congrArg (fun k ↦ biprod.inl ≫ k) h
    simp only [biprod.inl_desc_assoc] at he
    have ht := congrArg ((o.openOp jU).ordinaryAdjunction.homEquiv _ _) he
    simpa only [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.right_triangle_components, Category.id_comp] using ht
  · have he := congrArg (fun k ↦ biprod.inr ≫ k) h
    simp only [biprod.inr_desc_assoc] at he
    have ht := congrArg ((o.openOp jV).ordinaryAdjunction.homEquiv _ _) he
    simpa only [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.right_triangle_components, Category.id_comp] using ht

end AlgebraicGeometry.ProEtale.TowerOpenCover
