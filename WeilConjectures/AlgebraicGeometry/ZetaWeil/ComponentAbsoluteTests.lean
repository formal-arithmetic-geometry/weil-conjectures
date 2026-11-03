/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentLiftBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.ProperBaseChange.CondensedFieldContinuousRealization
import WeilConjectures.AlgebraicGeometry.ZetaWeil.ProfiniteTestObjectMappingProperty

/-! # Coordinate-preserving absolute component tests

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem point_prod_ext {P S : Profinite.{u}} {x y : (P ⨯ S : Profinite.{u})}
    (h₁ : (prod.fst : P ⨯ S ⟶ P) x = (prod.fst : P ⨯ S ⟶ P) y)
    (h₂ : (prod.snd : P ⨯ S ⟶ S) x = (prod.snd : P ⨯ S ⟶ S) y) : x = y := by
  apply Concrete.isLimit_ext (pair P S) (limit.isLimit _) x y
  intro j
  rcases j with ⟨j⟩
  cases j
  · exact h₁
  · exact h₂

private theorem absolute_test_ext (X : Scheme.{u})
    {V : X.ProEt} [IsAffine V.left] {S : Profinite.{u}}
    {f g : V ⟶ profiniteTestObject X S}
    (h : ∀ y, profiniteTestObjectProj X S (f.left.base y) =
      profiniteTestObjectProj X S (g.left.base y)) : f = g :=
  (profinite_test_object_mapping_property X
    ((profiniteTestObjectProj X S).comp f.left.base.hom)).unique
      (fun _ ↦ rfl) (fun y ↦ (h y).symm)

/-- Relative component tests on a product identify with the absolute profinite tests,
preserving the profinite coordinate.

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9
(blueprint: lem-zl-component-absolute-tests).

Proof: the universal properties of relative component lifts and absolute profinite
tests give maps in both directions. Their composites preserve the base and the
profinite coordinates, so uniqueness makes them inverse. The same uniqueness gives
naturality in the profinite set. All maps use the specified relative coordinate. -/
theorem component_absolute_tests (X : Scheme.{u}) [IsAffine X] :
    ∃ e : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
        profiniteToProEtOf X,
      ∀ (S : Profinite.{u})
        (z : ((relativeComponentLift X).obj ((Over.star (affineComponentSpace X)).obj S)).left),
        (prod.snd : affineComponentSpace X ⨯ S ⟶ S)
            (relativeComponentCoordinate X ((Over.star (affineComponentSpace X)).obj S) z) =
          profiniteTestProjection X S ((e.hom.app S).left z) := by
  classical
  let P := affineComponentSpace X
  let F := CondensedRing.componentTests X
  let H := profiniteToProEtOf X
  have hF := (component_relative_profinite_site X).choose_spec
  let p := hF.2.1.choose
  have hp := hF.2.1.choose_spec.1
  have hnat := hF.2.1.choose_spec.2.1
  have hmap := hF.2.1.choose_spec.2.2
  have ha (E : Over P) : IsAffine (F.obj E).left := hF.1 E
  have he (S : Profinite.{u}) : ∃ e : (Over.star P ⋙ F).obj S ≅ H.obj S,
      ∀ z, profiniteTestObjectProj X S (e.hom.left z) =
        (prod.snd : P ⨯ S ⟶ S) (p ((Over.star P).obj S) z) := by
    let E := (Over.star P).obj S
    let A := F.obj E
    have : IsAffine A.left := ha E
    let c : C(A.left, S) :=
      (prod.snd : P ⨯ S ⟶ S).hom.hom.comp (p E)
    obtain ⟨m, hm, -⟩ := profinite_test_object_mapping_property X c
    let B := H.obj S
    have : IsAffine (profiniteToScheme.obj S) := by
      dsimp [profiniteToScheme]
      infer_instance
    have : IsAffine specZ.{u} := by
      dsimp [specZ]
      infer_instance
    have : IsAffine B.left := by
      change IsAffine (pullback (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X))
      infer_instance
    let q : affineComponentSpace B.left ⟶ S := ConcreteCategory.ofHom
      (⟨(profiniteTestObjectProj X S).continuous.connectedComponentsLift,
        (profiniteTestObjectProj X S).continuous.connectedComponentsLift_continuous⟩ :
          C(affineComponentSpace B.left, S))
    let r : affineComponentSpace B.left ⟶ P := affineComponentMap B.hom
    let d : C(B.left, E.left) :=
      ⟨fun z ↦ prod.lift r q (ConnectedComponents.mk z),
        (prod.lift r q).hom.hom.continuous.comp ConnectedComponents.continuous_coe⟩
    have hd (z : B.left) : E.hom (d z) = ConnectedComponents.mk (B.hom z) := by
      simp only [E, Over.star_obj_hom, prod.lift_fst]
      change (prod.fst : P ⨯ S ⟶ P) ((prod.lift r q) (ConnectedComponents.mk z)) = _
      rw [← ConcreteCategory.comp_apply, prod.lift_fst]
      rfl
    obtain ⟨n, hn, hnu⟩ := hmap ((Scheme.ProEt.forget X).obj B) E d hd
    let n' : B ⟶ A := MorphismProperty.Over.homMk n.left n.w
    have hd_snd (z : B.left) : (prod.snd : P ⨯ S ⟶ S) (d z) =
        profiniteTestObjectProj X S z := by
      change (prod.snd : P ⨯ S ⟶ S) ((prod.lift r q) (ConnectedComponents.mk z)) = _
      rw [← ConcreteCategory.comp_apply, prod.lift_snd]
      change (profiniteTestObjectProj X S).continuous.connectedComponentsLift
        (ConnectedComponents.mk z) = _
      exact Continuous.connectedComponentsLift_apply_coe _ z
    have hd_m (z : A.left) : d (m.left z) = p E z := by
      apply point_prod_ext
      · have hh := (hd (m.left z)).trans
          ((congrArg ConnectedComponents.mk (congrArg (fun k : A.left ⟶ X ↦ k z) m.w)).trans
            (hp E z).symm)
        have hef : E.hom = (prod.fst : P ⨯ S ⟶ P) := by
          simp [E, Over.star_obj_hom]
        exact (congrArg (fun a : E.left ⟶ P ↦ a (d (m.left z))) hef.symm).trans
          (hh.trans (congrArg (fun a : E.left ⟶ P ↦ a (p E z)) hef))
      · exact (hd_snd (m.left z)).trans (hm z)
    have hmn : m ≫ n' = 𝟙 A := by
      apply (Scheme.ProEt.forget X).map_injective
      apply (hmap ((Scheme.ProEt.forget X).obj A) E (p E) (hp E)).unique
      · intro z
        exact (hn (m.left z)).trans (hd_m z)
      · intro z
        rfl
    have hnm : n' ≫ m = 𝟙 B := by
      apply absolute_test_ext X
      intro z
      change profiniteTestObjectProj X S (m.left (n.left z)) = profiniteTestObjectProj X S z
      rw [hm]
      change (prod.snd : P ⨯ S ⟶ S) (p E (n.left z)) = _
      rw [hn]
      exact hd_snd z
    exact ⟨⟨m, n', hmn, hnm⟩, hm⟩
  choose e he using he
  let e₀ : Over.star P ⋙ F ≅ H := NatIso.ofComponents e (by
    intro S T f
    have : IsAffine ((Over.star P ⋙ F).obj S).left := ha _
    apply absolute_test_ext X
    intro z
    change profiniteTestObjectProj X T ((e T).hom.left ((F.map ((Over.star P).map f)).left z)) =
      profiniteTestObjectProj X T (((H.map f).left) ((e S).hom.left z))
    rw [he T]
    erw [profiniteTestObjectProj_naturality]
    rw [he S]
    have hn := hnat _ _ ((Over.star P).map f) z
    change p ((Over.star P).obj T) ((F.map ((Over.star P).map f)).left z) = _ at hn
    rw [hn]
    simp only [Over.star_map_left]
    change (prod.snd : P ⨯ T ⟶ T)
      ((prod.map (𝟙 P) f) (p ((Over.star P).obj S) z)) = _
    rw [← ConcreteCategory.comp_apply, prod.map_snd, ConcreteCategory.comp_apply])
  refine ⟨e₀, ?_⟩
  intro S z
  exact (he S z).symm

end AlgebraicGeometry.ProEtale
