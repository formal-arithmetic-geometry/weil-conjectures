/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageRoosLimitData

/-! Canonical derived-limit projection normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The conjugate limit comparison preserves the canonical counit projections:
```
Rf_* (Rlim M) ── pushLimitIso ──> Rlim (Rf_* M)
     │ Rf_*(π_n)                      │ π_n
     v                                v
Rf_* (M_n) <── pushEvaluationMap ── (Rf_* M)_n
```
Source: blueprint direct-image limits, proof (1); Stacks Tag 0A07.
(blueprint: lem-pbc-direct-image-roos-projection-compatibility)

Proof: expand pushLimitIso as the conjugate of constantInterchange under the two
composite adjunctions. The counit identity for conjugate transformations expresses
constant of this comparison followed by the target counit as pushforward of the
source counit, after the constant/pullback interchange. Evaluate this identity at n.
The evaluation mate identity moves pushEvaluationMap through the tower counit.
Coherence of exact localization identifies constantInterchange followed by
pullEvaluation with the two canonical constantEvaluationIso components. Cancel
these components and use their naturality. The remaining equality is precisely
the displayed square, naturally in M; the adjunction triangle identities give
the same formula for identity morphisms and zero towers. -/
theorem directImage_roos_projection_compatibility {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DTow l E X) (n : ℕ) :
    (pushLimitIso l E f).hom.app M ≫
        (levelProjection l E Y n).app ((rpush l E f).obj M) ≫
        (pushEvaluationMap l E f n).app M =
      (rpushModule l E f).map ((levelProjection l E X n).app M) := by
  let U := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  let p := dpullModule l E f
  let adjp := moduleAdjunction l E f
  let adjP := towerAdjunction l E f
  let cX := constantLimitAdjunction l E X
  let cY := constantLimitAdjunction l E Y
  let eX := constantEvaluationIso l E X n
  let eY := constantEvaluationIso l E Y n
  let ci := constantInterchange l E U
  let β := (pullEvaluation l E f n).inv
  have hcoh (N : DerivedCategory (AdicCompletion.Modules l E Y)) :
      p.map (eY.inv.app N) ≫ β.app ((dconstant l E Y).obj N) =
        eX.inv.app (p.obj N) ≫ (dev l E X n).map (ci.hom.app N) := by
    let e := DerivedCategory.Q.objObjPreimageIso N
    have h := constant_coherence_Q l E f n (DerivedCategory.Q.objPreimage N)
    have n1 := eY.inv.naturality e.hom
    have n2 := β.naturality ((dconstant l E Y).map e.hom)
    have n3 := eX.inv.naturality (p.map e.hom)
    have n4 := ci.hom.naturality e.hom
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n1 n2 n3 n4
    rw [← cancel_epi (p.map e.hom), ← p.map_comp_assoc, n1, p.map_comp_assoc, n2,
      reassoc_of% h, ← (dev l E X n).map_comp, ← n4, (dev l E X n).map_comp,
      reassoc_of% n3]
  have hA : p.map ((pushEvaluationMap l E f n).app M) ≫ adjp.counit.app ((dev l E X n).obj M) =
      β.app ((rpush l E f).obj M) ≫ (dev l E X n).map (adjP.counit.app M) :=
    mateEquiv_counit adjP adjp (.mk _ _ _ _ β) M
  have hC := conjugateEquiv_counit (adjp.comp cX) (cY.comp adjP) ci.symm.hom M
  have hγ : (pushLimitIso l E f).hom = conjugateEquiv (adjp.comp cX) (cY.comp adjP) ci.symm.hom :=
    rfl
  rw [← hγ, Adjunction.comp_counit_app, Adjunction.comp_counit_app] at hC
  simp only [Functor.comp_obj, Functor.comp_map, Iso.symm_hom] at hC
  apply (adjp.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [hA, adjp.counit_naturality]
  rw [levelProjection_app, levelProjection_app]
  have n2 := β.naturality (cY.counit.app ((rpush l E f).obj M))
  have n3 := eX.inv.naturality (p.map ((pushLimitIso l E f).hom.app M))
  have n4 := ci.hom.naturality ((pushLimitIso l E f).hom.app M)
  have n5 := eX.inv.naturality (adjp.counit.app ((rlim l E X).obj M))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n2 n3 n4 n5
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% n2, reassoc_of% (hcoh _), reassoc_of% n3]
  simp only [← (dev l E X n).map_comp]
  erw [reassoc_of% n4, hC, ci.hom_inv_id_app_assoc]
  simp only [(dev l E X n).map_comp]
  erw [reassoc_of% n5]

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
