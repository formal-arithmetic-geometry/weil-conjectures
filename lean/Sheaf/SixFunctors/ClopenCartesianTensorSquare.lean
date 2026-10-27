/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClopenComparisonTensorSquareData
import Sheaf.SixFunctors.ClopenPullbackTensorCompatibility

/-! # Cartesian tensor square for normalized open base change -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized open base-change map respects the canonical tensor comparisons.
Source: Stacks 07A4 and 0GL1.
(blueprint: lem-sf-clopen-cartesian-tensor-square).

Proof: transpose the inverse square under the base-changed open adjunction.
Substitute the beta and gamma inverse-transpose formulas. Naturality moves theta
past gamma, and tensor compatibility of the pullback compositor identifies the
middle three factors. Tensor naturality moves the remaining open unit. Apply the
inverse-transpose formula for the base-changed open tensor comparison, and use
its naturality and the beta inverse-transpose formula once more. The two
transposes agree. Cancel the gamma, beta and open tensor isomorphisms to recover
the forward Cartesian tensor square. -/
theorem cartesian_tensor {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s) :
  ∀ (H : ProjectionRestriction.Der (restrictRing m d.j d.R))
      (N : ProjectionRestriction.Der d.R),
    o.gPull.derived.map (a.gamma.hom.app (H, N)) ≫
        a.beta.hom.app (o.tensorU.functor.obj (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (v.tensorQ.comparison.hom.app (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (o.tensorU'.functor.map
          (Prod.mkHom (𝟙 _) (o.theta.inv.app N))) =
      v.tensorP.comparison.hom.app (o.opens.jShriek.obj H, N) ≫
        o.tensorX'.functor.map (Prod.mkHom (a.beta.hom.app H) (𝟙 _)) ≫
        v.tensorB.delta.hom.app (o.gUPull.derived.obj H, o.gPull.derived.obj N) := by
  intro H N
  let P := o.gPull.derived
  let Q := o.gUPull.derived
  let I := o.opens.jStar
  let J := o.opens.jShriek
  let B := o.opens.jShriek'
  let R := o.opens.jStar'
  let T := o.tensorX.functor
  let U := o.tensorU.functor
  let V := o.tensorX'.functor
  let W := o.tensorU'.functor
  let mi : T ⋙ I ≅ I.prod I ⋙ U := o.tensorComparison.comparison
  let mb : V ⋙ R ≅ R.prod R ⋙ W := v.tensorB.tensorComparison.comparison
  let mp := v.tensorP.comparison
  let mq := v.tensorQ.comparison
  let ab := o.opens.adj'
  have hi :
      a.beta.inv.app (U.obj (H, I.obj N)) ≫ P.map (a.gamma.inv.app (H, N)) ≫
          mp.hom.app (J.obj H, N) =
        B.map (mq.hom.app (H, I.obj N)) ≫
          B.map (W.map (Prod.mkHom (𝟙 _) (o.theta.inv.app N))) ≫
          v.tensorB.delta.inv.app (Q.obj H, P.obj N) ≫
          V.map (Prod.mkHom (a.beta.inv.app H) (𝟙 _)) := by
    apply (ab.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
    erw [a.beta_inverse]
    simp only [Functor.map_comp, Category.assoc]
    have ht := o.theta.inv.naturality (a.gamma.inv.app (H, N))
    dsimp only [Functor.comp_map, Functor.comp_obj] at ht
    slice_lhs 2 3 => exact ht.symm
    have hg := a.gamma_inverse H N
    rw [Adjunction.homEquiv_unit] at hg
    slice_lhs 1 2 =>
      rw [← Q.map_comp]
      erw [hg]
    rw [Q.map_comp]
    have hc := pullback_tensor_compatibility a v (J.obj H) N
    slice_lhs 2 4 => exact hc
    have hn := mq.hom.naturality (Prod.mkHom (o.opens.adj.unit.app H) (𝟙 (I.obj N)))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hn
    slice_lhs 1 2 => exact hn
    have hq := ab.unit.naturality (mq.hom.app (H, I.obj N))
    have hw := ab.unit.naturality
      (W.map (Prod.mkHom (𝟙 (Q.obj H)) (o.theta.inv.app N)))
    dsimp only [Functor.id_map, Functor.comp_map] at hq hw
    erw [Adjunction.homEquiv_unit]
    simp only [Category.assoc]
    slice_rhs 1 2 => exact hq.symm
    slice_rhs 2 3 => exact hw.symm
    have hd := v.tensorB.inverse_transpose (Q.obj H) (P.obj N)
    rw [Adjunction.homEquiv_unit] at hd
    slice_rhs 3 4 => exact hd
    change _ = mq.hom.app (H, I.obj N) ≫
      W.map (Prod.mkHom (𝟙 (Q.obj H)) (o.theta.inv.app N)) ≫
      (W.map (Prod.mkHom (ab.unit.app (Q.obj H)) (𝟙 (R.obj (P.obj N)))) ≫
        mb.inv.app (B.obj (Q.obj H), P.obj N)) ≫
      R.map (V.map (Prod.mkHom (a.beta.inv.app H) (𝟙 (P.obj N))))
    have hb := mb.inv.naturality (Prod.mkHom (a.beta.inv.app H) (𝟙 (P.obj N)))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hb
    simp only [Category.assoc]
    slice_rhs 4 5 => exact hb.symm
    slice_lhs 2 3 => erw [← W.map_comp]
    slice_rhs 2 4 => erw [← W.map_comp, ← W.map_comp]
    congr 2
    apply congrArg W.map
    ext
    · change Q.map (o.opens.adj.unit.app H) ≫ o.theta.inv.app (J.obj H) =
        𝟙 (Q.obj H) ≫ (ab.unit.app (Q.obj H) ≫ R.map (a.beta.inv.app H))
      simpa only [Category.id_comp, Adjunction.homEquiv_unit]
        using (a.beta_inverse H).symm
    · change Q.map (𝟙 (I.obj N)) ≫ o.theta.inv.app N =
        o.theta.inv.app N ≫ 𝟙 (R.obj (P.obj N)) ≫ R.map (𝟙 (P.obj N))
      rw [Q.map_id, R.map_id]
      simp only [Category.id_comp]
      exact (Category.comp_id (o.theta.inv.app N)).symm
  let e := P.mapIso (a.gamma.app (H, N)) ≪≫
    a.beta.app (U.obj (H, I.obj N))
  let j := V.mapIso (Iso.prod (a.beta.app H) (Iso.refl (P.obj N))) ≪≫
    v.tensorB.delta.app (Q.obj H, P.obj N)
  let g := B.map (mq.hom.app (H, I.obj N)) ≫
    B.map (W.map (Prod.mkHom (𝟙 _) (o.theta.inv.app N)))
  suffices he : e.hom ≫ g = mp.hom.app (J.obj H, N) ≫ j.hom by
    simpa only [e, j, g, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Category.assoc] using he
  have hh : e.inv ≫ mp.hom.app (J.obj H, N) = g ≫ j.inv := by
    simpa only [e, j, g, Iso.trans_inv, Functor.mapIso_inv,
      Iso.prod_inv, Iso.refl_inv, Iso.app_inv, Functor.id_obj, Category.assoc] using hi
  apply (cancel_epi e.inv).1
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [← Category.assoc, hh, Category.assoc, j.inv_hom_id]
  exact (Category.comp_id g).symm

end SheafOfModules.ClopenComparisonTensorSquare
