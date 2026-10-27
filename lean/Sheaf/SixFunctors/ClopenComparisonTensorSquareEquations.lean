/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClopenComparisonTensorSquareData
import all Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.ClopenCartesianTensorSquare

/-! # Formal tensor compatibility of the clopen projection and its composites -/

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
private theorem derived_counit_normalization {m : Mode} {d : Input.{u} m}
    {t : SiteSquare d} {o : Operations d t} {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s)
    (M : Der (restrictRing m s (restrictRing m d.j' d.S))) :
    (exactDerivedAdjunction v.extensionS.adjunction).unit.app M ≫
      (exactDerivedAdjunction v.rightAdjunction).counit.app M = 𝟙 M := by
  let L := v.extensionS.ordinary
  let S := restrict m s (restrictRing m d.j' d.S)
  let a := exactDerivedAdjunction v.extensionS.adjunction
  let b := exactDerivedAdjunction v.rightAdjunction
  have he : a.unit ≫ b.counit = 𝟙 _ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (Mod (restrictRing m s (restrictRing m d.j' d.S)))
        (.up ℤ))
    intro P
    change a.unit.app (DerivedCategory.Q.obj P) ≫
      b.counit.app (DerivedCategory.Q.obj P) = 𝟙 _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map
            ((v.extensionS.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          S.mapDerivedCategoryFactors.inv.app _ ≫
            S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, exactDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    have hc : b.counit.app (DerivedCategory.Q.obj P) =
        S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
          S.mapDerivedCategoryFactors.hom.app _ ≫
            DerivedCategory.Q.map
              ((v.rightAdjunction.mapHomologicalComplex (.up ℤ)).counit.app P) := by
      simp only [b, exactDerivedAdjunction, Adjunction.localization_counit_app]
      rfl
    rw [hu, hc]
    simp only [Category.assoc]
    slice_lhs 3 4 =>
      rw [← Functor.map_comp, Iso.inv_hom_id_app]
      exact S.mapDerivedCategory.map_id _
    erw [Category.id_comp]
    slice_lhs 2 3 => rw [Iso.inv_hom_id_app]
    erw [Category.id_comp, ← Functor.map_comp]
    have hh : (v.extensionS.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P ≫
        (v.rightAdjunction.mapHomologicalComplex (.up ℤ)).counit.app P = 𝟙 P := by
      ext n : 1
      exact v.counit_normalization (P.X n)
    rw [hh]
    exact DerivedCategory.Q.map_id P
  exact NatTrans.congr_app he M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem clopen_tensor {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (v : Data o s) (F V : Der (restrictRing m d.j' d.S)) :
    v.rho.app (o.tensorU'.functor.obj (F, V)) ≫
        v.extensionS.ordinary.mapDerivedCategory.map
          (v.tensorS.tensorComparison.comparison.hom.app (F, V)) =
      o.tensorU'.functor.map (Prod.mkHom (v.rho.app F) (𝟙 V)) ≫
        v.tensorS.delta.hom.app
          ((restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.obj F, V) := by
  let a := exactDerivedAdjunction v.extensionS.adjunction
  let b := exactDerivedAdjunction v.rightAdjunction
  let L := v.extensionS.ordinary.mapDerivedCategory
  let S := (restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory
  let T := o.tensorU'.functor
  let U := v.tensorA.functor
  let mu : T ⋙ S ≅ (S.prod S) ⋙ U := v.tensorS.tensorComparison.comparison
  have hn (M : Der (restrictRing m s (restrictRing m d.j' d.S))) :=
    derived_counit_normalization v M
  have (M : Der (restrictRing m s (restrictRing m d.j' d.S))) :
      IsIso (a.unit.app M) := derivedUnit_isIso v.extensionS M
  have hd (M : Der (restrictRing m s (restrictRing m d.j' d.S))) :
      S.map (v.tensorS.delta.hom.app (M, V)) ≫
          b.counit.app (U.obj (M, S.obj V)) =
        mu.hom.app (L.obj M, V) ≫
          U.map (Prod.mkHom (b.counit.app M) (𝟙 (S.obj V))) := by
    apply (cancel_epi (S.map (v.tensorS.delta.inv.app (M, V)))).1
    slice_lhs 1 2 =>
      rw [← S.map_comp, Iso.inv_hom_id_app]
      exact S.map_id _
    rw [Category.id_comp]
    apply (cancel_epi (a.unit.app (U.obj (M, S.obj V)))).1
    have ht := v.tensorS.inverse_transpose M V
    change a.unit.app (U.obj (M, S.obj V)) ≫
      S.map (v.tensorS.delta.inv.app (M, V)) =
      U.map (Prod.mkHom (a.unit.app M) (𝟙 (S.obj V))) ≫
        mu.inv.app (L.obj M, V) at ht
    slice_rhs 1 2 => rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← U.map_comp]
    have hp : Prod.mkHom (a.unit.app M) (𝟙 (S.obj V)) ≫
        Prod.mkHom (b.counit.app M) (𝟙 (S.obj V)) = 𝟙 _ := by
      ext
      · exact hn M
      · simp
    rw [hp, U.map_id]
    exact hn _
  apply ((b.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change S.map (b.unit.app (T.obj (F, V))) ≫
      S.map (L.map (mu.hom.app (F, V))) ≫
        b.counit.app (U.obj (S.obj F, S.obj V)) =
    S.map (T.map (Prod.mkHom (b.unit.app F) (𝟙 V))) ≫
      S.map (v.tensorS.delta.hom.app (S.obj F, V)) ≫
        b.counit.app (U.obj (S.obj F, S.obj V))
  slice_lhs 2 3 => exact b.counit.naturality (mu.hom.app (F, V))
  slice_lhs 1 2 => exact b.left_triangle_components (T.obj (F, V))
  simp only [CategoryTheory.Functor.id_map]
  rw [hd]
  have hm := mu.hom.naturality (Prod.mkHom (b.unit.app F) (𝟙 V))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
    restrictionModel] at hm
  slice_rhs 1 2 => exact hm
  rw [Category.assoc, ← U.map_comp]
  have hp : Prod.mkHom (S.map (b.unit.app F)) (S.map (𝟙 V)) ≫
      Prod.mkHom (b.counit.app (S.obj F)) (𝟙 (S.obj V)) = 𝟙 _ := by
    ext
    · exact b.left_triangle_components F
    · simp
  rw [hp]
  dsimp only [CategoryTheory.Functor.id_obj] at *
  erw [U.map_id, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem composite_open {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (v : Data o s) :
(∀ (M : ProjectionRestriction.Der (restrictRing m s (restrictRing m d.j' d.S)))
      (N : ProjectionRestriction.Der d.S),
    v.tensorB.delta.hom.app (v.extensionS.ordinary.mapDerivedCategory.obj M, N) ≫
        o.opens.jShriek'.map (v.tensorS.delta.hom.app (M, o.opens.jStar'.obj N)) =
      v.deltaK.hom.app (M, N)) := by
  intro M N
  let aS := exactDerivedAdjunction v.extensionS.adjunction
  let aB := o.opens.adj'
  let S := (OpenTensorNormalization.restrict m s
    (restrictRing m d.j' d.S)).mapDerivedCategory
  let L := v.extensionS.ordinary.mapDerivedCategory
  let B := o.opens.jShriek'
  let T := o.tensorU'.functor
  let U := v.tensorA.functor
  have hi : B.map (v.tensorS.delta.inv.app (M, o.opens.jStar'.obj N)) ≫
      v.tensorB.delta.inv.app (L.obj M, N) = v.deltaK.inv.app (M, N) := by
    apply ((aS.comp aB).homEquiv _ _).injective
    erw [v.inverse_transposeK M N]
    rw [Adjunction.comp_homEquiv]
    change aS.homEquiv _ _ ((aB.homEquiv _ _)
      (B.map (v.tensorS.delta.inv.app (M, o.opens.jStar'.obj N)) ≫
        v.tensorB.delta.inv.app (L.obj M, N))) = _
    erw [aB.homEquiv_naturality_left, v.tensorB.inverse_transpose]
    erw [aS.homEquiv_naturality_right, v.tensorS.inverse_transpose]
    dsimp only [restrictionModel, Functor.comp_obj, Functor.prod_obj,
      Functor.id_obj] at *
    have hn := v.tensorS.tensorComparison.comparison.inv.naturality
      (Prod.mkHom (aB.unit.app (L.obj M)) (𝟙 (o.opens.jStar'.obj N)))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
      restrictionModel, Functor.id_obj] at hn
    rw [Functor.map_comp]
    simp only [Category.assoc]
    slice_lhs 2 3 => erw [← hn]
    simp only [← Category.assoc]
    rw [← U.map_comp]
    have hp :
        Prod.mkHom (aS.unit.app M) (𝟙 (S.obj (o.opens.jStar'.obj N))) ≫
          Prod.mkHom (S.map (aB.unit.app (L.obj M)))
            (S.map (𝟙 (o.opens.jStar'.obj N))) =
        Prod.mkHom ((aS.comp aB).unit.app M) (𝟙 _) := by
      ext
      · exact (Adjunction.comp_unit_app aS aB M).symm
      · simp
    rw [hp]
  let e := (v.tensorB.delta.app (L.obj M, N)) ≪≫
    B.mapIso (v.tensorS.delta.app (M, o.opens.jStar'.obj N))
  have he : e.symm = (v.deltaK.app (M, N)).symm := Iso.ext hi
  exact congrArg (fun e ↦ e.inv) he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem equations_of_factors {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s)
    (hcart : (∀ (H : ProjectionRestriction.Der (restrictRing m d.j d.R))
      (N : ProjectionRestriction.Der d.R),
    o.gPull.derived.map (a.gamma.hom.app (H, N)) ≫
        a.beta.hom.app (o.tensorU.functor.obj (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (v.tensorQ.comparison.hom.app (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (o.tensorU'.functor.map
          (Prod.mkHom (𝟙 _) (o.theta.inv.app N))) =
      v.tensorP.comparison.hom.app (o.opens.jShriek.obj H, N) ≫
        o.tensorX'.functor.map (Prod.mkHom (a.beta.hom.app H) (𝟙 _)) ≫
        v.tensorB.delta.hom.app (o.gUPull.derived.obj H, o.gPull.derived.obj N)))
    (hclopen : (∀ (F V : ProjectionRestriction.Der (restrictRing m d.j' d.S)),
    v.rho.app (o.tensorU'.functor.obj (F, V)) ≫
        v.extensionS.ordinary.mapDerivedCategory.map
          (v.tensorS.tensorComparison.comparison.hom.app (F, V)) =
      o.tensorU'.functor.map (Prod.mkHom (v.rho.app F) (𝟙 V)) ≫
        v.tensorS.delta.hom.app
          ((OpenTensorNormalization.restrict m s
            (restrictRing m d.j' d.S)).mapDerivedCategory.obj F, V)))
    (hcomp : (∀ (M : ProjectionRestriction.Der (restrictRing m s (restrictRing m d.j' d.S)))
      (N : ProjectionRestriction.Der d.S),
    v.tensorB.delta.hom.app (v.extensionS.ordinary.mapDerivedCategory.obj M, N) ≫
        o.opens.jShriek'.map (v.tensorS.delta.hom.app (M, o.opens.jStar'.obj N)) =
      v.deltaK.hom.app (M, N)))
    : Equations a v := by
  refine ⟨hcart, hclopen, hcomp, ?_⟩
  intro H N
  let F := o.gUPull.derived.obj H
  let V := o.gUPull.derived.obj (o.opens.jStar.obj N)
  let Y := o.gPull.derived.obj N
  let W := o.opens.jStar'.obj Y
  let L := v.extensionS.ordinary.mapDerivedCategory
  let S := (OpenTensorNormalization.restrict m s
    (restrictRing m d.j' d.S)).mapDerivedCategory
  let B := o.opens.jShriek'
  let T := o.tensorU'.functor
  let U := v.tensorA.functor
  have hn := v.rho.naturality
    (v.tensorQ.comparison.hom.app (H, o.opens.jStar.obj N))
  have hb := v.tensorB.delta.hom.naturality
    (Prod.mkHom (v.rho.app F) (𝟙 Y))
  have hs := v.tensorS.delta.hom.naturality
    (Prod.mkHom (𝟙 (S.obj F)) (o.theta.hom.app N))
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.prod_obj,
    Functor.comp_map, Functor.prod_map, Functor.id_map] at hn hb hs
  dsimp only [alpha]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← hn, Functor.map_comp]
  slice_lhs 4 5 => rw [← Functor.map_comp, hclopen, Functor.map_comp]
  have ht :
      Prod.mkHom (a.beta.hom.app H ≫ B.map (v.rho.app F)) (𝟙 Y) =
        Prod.mkHom (a.beta.hom.app H) (𝟙 Y) ≫
          Prod.mkHom (B.map (v.rho.app F)) (𝟙 Y) := by
    ext <;> simp
  rw [ht, Functor.map_comp, ← hcomp]
  simp only [Category.assoc]
  slice_rhs 3 4 => rw [hb]
  dsimp only [restrictionModel, Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at *
  slice_rhs 5 6 => rw [← Functor.map_comp, ← hs, Functor.map_comp]
  have hc := hcart H N
  have hc' := congrArg (fun f ↦ f ≫
    B.map (T.map (Prod.mkHom (v.rho.app F) (o.theta.hom.app N))) ≫
      B.map (v.tensorS.delta.hom.app (S.obj F, V))) hc
  simp only [Category.assoc] at hc'
  have hprod :
      Prod.mkHom (𝟙 F) (o.theta.inv.app N) ≫
          Prod.mkHom (v.rho.app F) (o.theta.hom.app N) =
        Prod.mkHom (v.rho.app F) (𝟙 V) := by
    ext <;> simp [F, V]
  have hprod' :
      Prod.mkHom (v.rho.app F) (𝟙 W) ≫
          Prod.mkHom (𝟙 (L.obj (S.obj F))) (o.theta.hom.app N) =
        Prod.mkHom (v.rho.app F) (o.theta.hom.app N) := by
    ext
    · exact Category.comp_id _
    · exact Category.id_comp _
  have hl := (OpenTensorNormalization.restrict m d.j' d.S).mapDerivedCategory.map_id Y
  have hl' := L.map_id (S.obj F)
  erw [hl, hl']
  dsimp only [B, T, F, V, Y, W, L, S] at *
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp,
    hprod, hprod', Category.assoc] using hc'

/-- The clopen tensor square, composite-open normalization and full square follow
from the Cartesian tensor square. Source: Stacks 07A4, 0GL1, 04TS.
(blueprint: lem-sf-clopen-comparison-tensor-square-equations).

Proof: localize the ordinary unit-counit normalization. Under the resulting reverse
adjunction, both sides of the clopen tensor square transpose to the restriction
tensor comparison, using its naturality and the triangle identity. Transpose the
inverses of the composite-open comparisons under the composite adjunction; tensor
naturality and the formula for its unit identify them. Finally expand alpha and
paste the Cartesian, clopen and composite-open identities, moving rho through the
tensor comparison by naturality. -/
theorem equations_for_data {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s) : Equations a v := by
  exact equations_of_factors a v (cartesian_tensor a v) (clopen_tensor v) (composite_open v)

end SheafOfModules.ClopenComparisonTensorSquare
