/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation

/-!
# Tower compact-support projection over an arbitrary standing field

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-integral-adjunction,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-tower-compact-support-projection-formula).

The section-site model, its tensor and all geometric operations are the recorded
SpTowerShriek operations. Constructibility is transported from the recorded full
subcategory of the ordinary derived category of coefficient towers. No normalization
or etale-origin witness is imposed. Index n always means positive exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Exact derived transport of the recorded sectionwise realization of towers.
Source: blueprint paragraph (3), ordinary tower category
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def realization (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T A ≌ D l E T :=
  letI := A.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

/-- The existing Dctf predicate transported through the sectionwise derived equivalence.
This retains both independent uniform intervals and every finite-level constructibility
condition, and adds no cartesian condition.
Source: blueprint paragraph (3), Dctf inputs
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def constructibleTor (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (C : D l E T) : Prop :=
  spConstructibleTorTowers l E T A ((realization l E b T A).inverse.obj C)

/-- The proper counit transpose, formed before any finite-level test or Tor hypothesis.
Source: blueprint paragraph (3), pi_p
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def properMap (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : D l E X) (B : D l E Y) :
    (tensor l E b Y).obj ((F l E b o c).obj C, B) ⟶
      (push l E b (o.geometry c.g)).obj
        ((tensor l E b c.Z).obj ((openD l E b (o.openOp c.i)).obj C,
          (pull l E b (o.geometry c.g)).obj B)) :=
  ((adjunction l E b (o.geometry c.g)).homEquiv _ _)
    (((o.geometry c.g).tensorPullback).hom.app ((F l E b o c).obj C, B) ≫
      (tensor l E b c.Z).map (Prod.mkHom
        ((adjunction l E b (o.geometry c.g)).counit.app
          ((openD l E b (o.openOp c.i)).obj C)) (𝟙 _)))

/-- The open-unit transpose pi_j, then Rp_*. The dependency's openTensor_mate fixes
its inverse direction as exactly that transpose, including the pullback/tensor comparison.
Source: blueprint paragraph (3), Rp_*(pi_j)
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def openMap (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : D l E X) (B : D l E Y) :=
  (push l E b (o.geometry c.g)).map
    ((o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).inv)

/-- The source of the proper projection arrow, as a functor of both inputs.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def source (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((F l E b o c).prod (𝟭 (D l E Y))) ⋙ tensor l E b Y

/-- The common target of the two arrows, as a functor of both inputs.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def middle (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((openD l E b (o.openOp c.i)).prod (pull l E b (o.geometry c.g))) ⋙
    tensor l E b c.Z ⋙ push l E b (o.geometry c.g)

/-- The source of the open projection arrow, using j^{-1}p^{-1}=f^{-1}.
The comparison to the single pullback is the recorded o.comp followed by c.comm.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def openSource (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((𝟭 (D l E X)).prod
    (pull l E b (o.geometry c.g) ⋙ pull l E b (o.geometry c.i))) ⋙
      tensor l E b X ⋙ F l E b o c

private theorem openTensorInv_natural (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    {C C' : D l E U} {L L' : D l E T} (a : C ⟶ C') (d : L ⟶ L') :
    (openD l E b (o.openOp j)).map
        ((tensor l E b U).map
          (Prod.mkHom a ((pull l E b (o.geometry j)).map d))) ≫
        (o.openTensor j C' L').inv =
      (o.openTensor j C L).inv ≫
        (tensor l E b T).map
          (Prod.mkHom ((openD l E b (o.openOp j)).map a) d) := by
  apply ((o.openOp j).derivedAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    o.openTensor_mate, o.openTensor_mate]
  have hunit := (o.openOp j).derivedAdjunction.unit.naturality a
  have hcomp :
      (tensor l E b U).map
          (Prod.mkHom a ((pull l E b (o.geometry j)).map d)) ≫
        (tensor l E b U).map
          (Prod.mkHom ((o.openOp j).derivedAdjunction.unit.app C') (𝟙 _)) =
      (tensor l E b U).map
          (Prod.mkHom ((o.openOp j).derivedAdjunction.unit.app C) (𝟙 _)) ≫
        (tensor l E b U).map
          (Prod.mkHom ((pull l E b (o.geometry j)).map
            ((openD l E b (o.openOp j)).map a))
            ((pull l E b (o.geometry j)).map d)) := by
    simp only [← Functor.map_comp]
    congr 1
    ext
    · exact hunit
    · simp
  rw [← Category.assoc, hcomp, Category.assoc]
  simpa [Category.assoc] using congrArg
    (fun h ↦ (tensor l E b U).map
      (Prod.mkHom ((o.openOp j).derivedAdjunction.unit.app C) (𝟙 _)) ≫ h)
    ((o.geometry j).tensorPullback.inv.naturality
      (Prod.mkHom ((openD l E b (o.openOp j)).map a) d))

/-- Both constructed arrows are natural in both inputs in the ambient unbounded categories.
Source: blueprint paragraph (3), simultaneous section-model maps
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: expand the proper counit transpose. Naturality of tensorPullback, the counit,
and the tensor bifunctor gives the first equation by the adjunction Hom equivalence.
For the second, apply Rp_* to the natural open-unit transpose. Its mate identity is
Operations.openTensor_mate; naturality of that unit and tensor gives the equation.
These are equations of actual tower maps, not equality detected by evaluations. -/
theorem maps_natural (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {C C' : D l E X} {B B' : D l E Y} (a : C ⟶ C') (d : B ⟶ B') :
    (source l E b o c).map (Prod.mkHom a d) ≫ properMap l E b o c C' B' =
      properMap l E b o c C B ≫ (middle l E b o c).map (Prod.mkHom a d) ∧
    (openSource l E b o c).map (Prod.mkHom a d) ≫ openMap l E b o c C' B' =
      openMap l E b o c C B ≫ (middle l E b o c).map (Prod.mkHom a d) := by
  constructor
  · let P := pull l E b (o.geometry c.g)
    let phi := Functor.curry.map (o.geometry c.g).tensorPullback.hom ≫
      (Functor.curryObjProdComp P P (tensor l E b c.Z)).hom
    have h := (Functor.uncurry.map
      ((adjunction l E b (o.geometry c.g)).rightAdjointProjectionMap
        (T_C := Functor.curry.obj (tensor l E b c.Z))
        (T_D := Functor.curry.obj (tensor l E b Y)) phi)).naturality
        (Prod.mkHom ((openD l E b (o.openOp c.i)).map a) d)
    simpa [source, middle, properMap, F, phi, P,
      Adjunction.rightAdjointProjectionMap, ← Functor.map_comp] using h
  · simpa only [openSource, middle, openMap, Functor.comp_map, Functor.prod_map,
      Functor.id_map, ← Functor.map_comp] using
      congrArg ((push l E b (o.geometry c.g)).map)
        (openTensorInv_natural l E b o c.i a
          ((pull l E b (o.geometry c.g)).map d))

/-- The finite-level tensor is the same recorded K-flat total tensor.
Source: blueprint paragraph (3), finite projection maps
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
abbrev levelTensor (b : Base l E) (T : Scheme.{u}) (n : ℕ) :=
  ((b.calculus T).levelClosed n).tensor

/-- The finite inverse-image/tensor comparison in the normalized evaluated coordinates.
Every factor is a specified comparison of the section model. Its representative map is
therefore the canonical pure-tensor pullback comparison by Geometry.tensorPullback_eq.
Source: blueprint paragraph (3), finite projection maps
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def levelPullTensor (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (n : ℕ) (N B : D l E Y) :=
  (proEtaleConstantRingDerivedPullback (R l E n) f).mapIso
      (((b.calculus Y).tensorEvaluation n).app (N, B)).symm ≪≫
    ((g.pullEvaluation n).app ((tensor l E b Y).obj (N, B))).symm ≪≫
    (Ev l E X n).mapIso (g.tensorPullback.app (N, B)) ≪≫
    ((b.calculus X).tensorEvaluation n).app
      ((pull l E b g).obj N, (pull l E b g).obj B) ≪≫
    (levelTensor l E b X n).mapIso
      (((g.pullEvaluation n).app N).prod ((g.pullEvaluation n).app B))

/-- The finite derived inverse-image/direct-image adjunction, with its canonical
ordinary normalization. Source: blueprint paragraph (3), finite proper projection
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
abbrev levelAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction

/-- The finite proper projection map: the finite counit transpose of the canonical
finite pullback/tensor comparison. Evaluation comparisons only change coordinates;
the arrow is constructed by the finite adjunction, independently of properMap.
Source: blueprint paragraph (3), finite proper projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def finiteProperMap (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (n : ℕ) (N : D l E X) (B : D l E Y) :=
  ((levelAdjunction l E f n).homEquiv _ _)
    ((proEtaleConstantRingDerivedPullback (R l E n) f).map
        ((levelTensor l E b Y n).map
          (Prod.mkHom ((g.pushEvaluation n).inv.app N) (𝟙 _))) ≫
      (levelPullTensor l E b g n ((push l E b g).obj N) B).hom ≫
      (levelTensor l E b X n).map (Prod.mkHom
        ((proEtaleConstantRingDerivedPullback (R l E n) f).map
            ((g.pushEvaluation n).hom.app N) ≫
          (levelAdjunction l E f n).counit.app ((Ev l E X n).obj N))
        (𝟙 _)))

/-- The finite exact open adjunction, obtained by termwise localization of the
specified finite ordinary adjunction. No adjunction is chosen independently.
Source: blueprint paragraph (3), finite open projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def levelOpenAdjunction (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) :
    sfIntrinsicDerivedOpen (R l E n) j ⊣
      proEtaleConstantRingDerivedPullback (R l E n) j :=
  ((finiteOpenAdjunction l E b j n).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    (proEtaleConstantRingPullback (R l E n) j).rightDerivedFunctorIsoMapDerivedCategory

/-- The finite open projection arrow is the finite unit transpose, using the same
normalized pullback/tensor comparison. It is constructed before comparing with the
open tower arrow. The occurrence of openEvaluation changes only the j_! coordinates.
Source: blueprint paragraph (3), finite open projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def finiteOpenMap (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (C : D l E U) (L : D l E T) :=
  ((levelOpenAdjunction l E b j n).homEquiv _ _).symm
    ((levelTensor l E b U n).map (Prod.mkHom
        ((levelOpenAdjunction l E b j n).unit.app ((Ev l E U n).obj C) ≫
          (proEtaleConstantRingDerivedPullback (R l E n) j).map
            ((openEvaluation l E b (o.openOp j) n).inv.app C)) (𝟙 _)) ≫
      (levelPullTensor l E b (o.geometry j) n
        ((openD l E b (o.openOp j)).obj C) L).inv ≫
      (proEtaleConstantRingDerivedPullback (R l E n) j).map
        ((levelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app C) (𝟙 _))))

section ProperEvaluation

attribute [local irreducible] realization constructibleTor properMap openMap source middle
  openSource levelPullTensor finiteProperMap finiteOpenMap

private theorem transpose_evaluation_aux
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (E₀ : A ⥤ A') (E₁ : B ⥤ B')
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (a : L ⋙ E₁ ≅ E₀ ⋙ L') (b : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (adj.unit.app M) ≫ b.hom.app (L.obj M) ≫
      R'.map (a.hom.app M) = adj'.unit.app (E₀.obj M))
    {P : A} {N : B} (h : L.obj P ⟶ N) :
    E₀.map ((adj.homEquiv _ _) h) ≫ b.hom.app N =
      (adj'.homEquiv _ _) (a.inv.app P ≫ E₁.map h) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hr := b.hom.naturality h
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  have hu' : E₀.map (adj.unit.app P) ≫ b.hom.app (L.obj P) =
      adj'.unit.app (E₀.obj P) ≫ R'.map (a.inv.app P) := by
    rw [← hu P]
    have hi := (R'.mapIso (a.app P)).hom_inv_id
    change R'.map (a.hom.app P) ≫ R'.map (a.inv.app P) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← Category.assoc, hu', Category.assoc]

private theorem projection_evaluation_aux
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (E₀ : A ⥤ A') (E₁ : B ⥤ B')
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (a : L ⋙ E₁ ≅ E₀ ⋙ L') (b : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (adj.unit.app M) ≫ b.hom.app (L.obj M) ≫
      R'.map (a.hom.app M) = adj'.unit.app (E₀.obj M))
    (hc : ∀ N, L'.map (b.hom.app N) ≫ adj'.counit.app (E₁.obj N) =
      a.inv.app (R.obj N) ≫ E₁.map (adj.counit.app N))
    (T₀ : A × A ⥤ A) (T₁ : B × B ⥤ B)
    (t₀ : A' × A' ⥤ A') (t₁ : B' × B' ⥤ B')
    (e₀ : T₀ ⋙ E₀ ≅ (E₀.prod E₀) ⋙ t₀)
    (e₁ : T₁ ⋙ E₁ ≅ (E₁.prod E₁) ⋙ t₁)
    (t : T₀ ⋙ L ≅ (L.prod L) ⋙ T₁)
    (N : B) (P : A) :
    E₀.map ((adj.homEquiv _ _)
        (t.hom.app (R.obj N, P) ≫ T₁.map (Prod.mkHom (adj.counit.app N) (𝟙 _)))) ≫
      b.hom.app (T₁.obj (N, L.obj P)) ≫
        R'.map (e₁.hom.app (N, L.obj P) ≫ t₁.map (Prod.mkHom (𝟙 _) (a.hom.app P))) =
    e₀.hom.app (R.obj N, P) ≫ t₀.map (Prod.mkHom (b.hom.app N) (𝟙 _)) ≫
      (adj'.homEquiv _ _)
        (L'.map (t₀.map (Prod.mkHom (b.inv.app N) (𝟙 _))) ≫
          ((L'.mapIso (e₀.app (R.obj N, P))).symm ≪≫
            (a.app (T₀.obj (R.obj N, P))).symm ≪≫
            E₁.mapIso (t.app (R.obj N, P)) ≪≫
            e₁.app (L.obj (R.obj N), L.obj P) ≪≫
            t₁.mapIso ((a.app (R.obj N)).prod (a.app P))).hom ≫
          t₁.map (Prod.mkHom (L'.map (b.hom.app N) ≫ adj'.counit.app (E₁.obj N))
            (𝟙 _))) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.prod_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Category.assoc]
  erw [transpose_evaluation_aux E₀ E₁ adj adj' a b hu]
  rw [← adj'.homEquiv_naturality_right]
  simp only [← Category.assoc]
  rw [← adj'.homEquiv_naturality_left]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  have hn := e₁.hom.naturality (Prod.mkHom (adj.counit.app N) (𝟙 (L.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [reassoc_of% hn]
  have he : E₁.map (adj.counit.app N) =
      a.hom.app (R.obj N) ≫ L'.map (b.hom.app N) ≫ adj'.counit.app (E₁.obj N) := by
    rw [hc]
    simp only [Iso.hom_inv_id_app_assoc]
  rw [he]
  simp only [CategoryTheory.Functor.map_id]
  simp only [← Functor.map_comp, CategoryTheory.prod_comp, Prod.mkHom, Category.id_comp,
    Category.comp_id]
  simp only [← Functor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.comp_id, Iso.hom_inv_id_app]
  simp only [← CategoryTheory.prod_id]
  erw [t₀.map_id]
  simp only [Category.id_comp]
  erw [Iso.hom_inv_id_app]
  erw [L'.map_id]
  simp only [Category.id_comp]

/-- Evaluation of the proper arrow is the finite counit projection map, with all
specified tensor, pullback and direct-image comparisons displayed.
Source: blueprint paragraph (3), levelwise finite projection
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: normalize the derived unit and counit with geometry_adjunction_evaluation.
Naturality of the direct-image comparison transports the adjoint transpose, and
naturality of tensorEvaluation transports the tensor of the counit. Expand the
specified levelPullTensor coordinate factors and cancel comparison/inverse pairs.
The result is precisely the finite counit transpose defining finiteProperMap. -/
theorem properMap_evaluation (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (n : ℕ) (C : D l E X) (B : D l E Y) :
    (Ev l E Y n).map (properMap l E b o c C B) ≫
        ((o.geometry c.g).pushEvaluation n).hom.app
          ((tensor l E b c.Z).obj ((openD l E b (o.openOp c.i)).obj C,
            (pull l E b (o.geometry c.g)).obj B)) ≫
        (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor.map
          (((b.calculus c.Z).tensorEvaluation n).hom.app
              ((openD l E b (o.openOp c.i)).obj C,
                (pull l E b (o.geometry c.g)).obj B) ≫
            (levelTensor l E b c.Z n).map (Prod.mkHom (𝟙 _)
              (((o.geometry c.g).pullEvaluation n).hom.app B))) =
      ((b.calculus Y).tensorEvaluation n).hom.app ((F l E b o c).obj C, B) ≫
        (levelTensor l E b Y n).map
          (Prod.mkHom (((o.geometry c.g).pushEvaluation n).hom.app
            ((openD l E b (o.openOp c.i)).obj C)) (𝟙 _)) ≫
        finiteProperMap l E b (o.geometry c.g) n
          ((openD l E b (o.openOp c.i)).obj C) B := by
  have h := geometry_adjunction_evaluation l E b (o.geometry c.g) n
  simpa only [properMap, finiteProperMap, levelPullTensor, F, Functor.mapIso_symm,
    Functor.comp_obj, Functor.id_obj] using
    projection_evaluation_aux (Ev l E Y n) (Ev l E c.Z n)
      (adjunction l E b (o.geometry c.g)) (levelAdjunction l E c.g n)
      ((o.geometry c.g).pullEvaluation n) ((o.geometry c.g).pushEvaluation n) h.1 h.2
      (tensor l E b Y) (tensor l E b c.Z)
      (levelTensor l E b Y n) (levelTensor l E b c.Z n)
      ((b.calculus Y).tensorEvaluation n) ((b.calculus c.Z).tensorEvaluation n)
      (o.geometry c.g).tensorPullback ((openD l E b (o.openOp c.i)).obj C) B

end ProperEvaluation

section OpenEvaluation

attribute [local irreducible] realization constructibleTor properMap openMap source middle
  openSource levelPullTensor finiteProperMap finiteOpenMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem open_projection_evaluation_aux
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (E₀ : A ⥤ A') (E₁ : B ⥤ B')
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (a : L ⋙ E₁ ≅ E₀ ⋙ L') (b : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (adj.unit.app M) ≫ b.hom.app (L.obj M) ≫
      R'.map (a.hom.app M) = adj'.unit.app (E₀.obj M))
    (T₀ : A × A ⥤ A) (T₁ : B × B ⥤ B)
    (t₀ : A' × A' ⥤ A') (t₁ : B' × B' ⥤ B')
    (e₀ : T₀ ⋙ E₀ ≅ (E₀.prod E₀) ⋙ t₀)
    (e₁ : T₁ ⋙ E₁ ≅ (E₁.prod E₁) ⋙ t₁)
    (t : T₁ ⋙ R ≅ (R.prod R) ⋙ T₀)
    (N : A) (P : B)
    (h : L.obj (T₀.obj (N, R.obj P)) ⟶ T₁.obj (L.obj N, P))
    (hm : (adj.homEquiv _ _) h =
      T₀.map (Prod.mkHom (adj.unit.app N) (𝟙 _)) ≫ t.inv.app (L.obj N, P)) :
    E₁.map h ≫ e₁.hom.app (L.obj N, P) ≫
        t₁.map (Prod.mkHom (a.hom.app N) (𝟙 _)) =
      a.hom.app (T₀.obj (N, R.obj P)) ≫
        L'.map (e₀.hom.app (N, R.obj P) ≫
          t₀.map (Prod.mkHom (𝟙 _) (b.hom.app P))) ≫
        (adj'.homEquiv _ _).symm
          (t₀.map (Prod.mkHom
              (adj'.unit.app (E₀.obj N) ≫ R'.map (a.inv.app N)) (𝟙 _)) ≫
            ((R'.mapIso (e₁.app (L.obj N, P))).symm ≪≫
              (b.app (T₁.obj (L.obj N, P))).symm ≪≫
              E₀.mapIso (t.app (L.obj N, P)) ≪≫
              e₀.app (R.obj (L.obj N), R.obj P) ≪≫
              t₀.mapIso ((b.app (L.obj N)).prod (b.app P))).inv ≫
            R'.map (t₁.map (Prod.mkHom (a.hom.app N) (𝟙 _)))) := by
  apply (cancel_epi (a.inv.app (T₀.obj (N, R.obj P)))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (adj'.homEquiv _ _).injective
  rw [adj'.homEquiv_naturality_right, adj'.homEquiv_naturality_right,
    ← transpose_evaluation_aux E₀ E₁ adj adj' a b hu, hm,
    adj'.homEquiv_naturality_left, Equiv.apply_symm_apply]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.prod_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  have he := e₀.hom.naturality (Prod.mkHom (adj.unit.app N) (𝟙 (R.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at he
  simp only [CategoryTheory.Functor.map_id] at he
  have hu' : E₀.map (adj.unit.app N) ≫ b.hom.app (L.obj N) =
      adj'.unit.app (E₀.obj N) ≫ R'.map (a.inv.app N) := by
    rw [← hu N]
    have hi := (R'.mapIso (a.app N)).hom_inv_id
    change R'.map (a.hom.app N) ≫ R'.map (a.inv.app N) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← hu']
  simp only [← t₀.map_comp_assoc, CategoryTheory.prod_comp,
    Prod.mkHom, Category.id_comp, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id, ← reassoc_of% he, Iso.hom_inv_id_app_assoc]

/-- Evaluation of the open arrow is exactly the finite unit projection map.
Applying the proper direct-image evaluation comparison identifies evaluation of
openMap with Rp_* of this same finite map.
Source: blueprint paragraph (3), levelwise finite projection
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: use Operations.openTensor_mate and the termwise localization of the open
unit. Evaluate this transpose using the ordinary unit_evaluation equation of Open,
its unit_termwise identity, tensorEvaluation, and the normalized pullEvaluation.
The finite exact adjunction is levelOpenAdjunction. Its Hom equivalence identifies
the evaluated arrow with finiteOpenMap. Naturality of pushEvaluation then applies
Rp_* to the equation, giving precisely the evaluation of openMap. -/
theorem openMap_evaluation (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (C : D l E U) (L : D l E T) :
    (Ev l E T n).map ((o.openTensor j C L).inv) ≫
        ((b.calculus T).tensorEvaluation n).hom.app
          ((openD l E b (o.openOp j)).obj C, L) ≫
        (levelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app C) (𝟙 _)) =
      (openEvaluation l E b (o.openOp j) n).hom.app
          ((tensor l E b U).obj (C, (pull l E b (o.geometry j)).obj L)) ≫
        (sfIntrinsicDerivedOpen (R l E n) j).map
          (((b.calculus U).tensorEvaluation n).hom.app
              (C, (pull l E b (o.geometry j)).obj L) ≫
            (levelTensor l E b U n).map (Prod.mkHom (𝟙 _)
              (((o.geometry j).pullEvaluation n).hom.app L))) ≫
        finiteOpenMap l E b o j n C L := by
  have hu := open_adjunction_unit_evaluation l E b (o.openOp j) n
  simpa only [finiteOpenMap, levelPullTensor, levelOpenAdjunction,
    Functor.mapIso_symm, Functor.comp_obj, Functor.id_obj] using
    open_projection_evaluation_aux (Ev l E U n) (Ev l E T n)
      (o.openOp j).derivedAdjunction (levelOpenAdjunction l E b j n)
      (openEvaluation l E b (o.openOp j) n) ((o.geometry j).pullEvaluation n) hu
      (tensor l E b U) (tensor l E b T)
      (levelTensor l E b U n) (levelTensor l E b T n)
      ((b.calculus U).tensorEvaluation n) ((b.calculus T).tensorEvaluation n)
      (o.geometry j).tensorPullback C L (o.openTensor j C L).inv
      (o.openTensor_mate j C L)

end OpenEvaluation

end AlgebraicGeometry.ProEtale.SpTowerProjection
