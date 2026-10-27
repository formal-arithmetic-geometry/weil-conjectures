/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedData

/-! # Objectwise normalized descent along a connected abelian tower

Source: Bhatt--Scholze, Lemmas 4.2.12 and 5.1.2
(blueprint: lem-sfb-connected-abelian-tower-descent-object).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.ProEtale

variable {U : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]

/-- The action on the entire profinite label space, with its given topology.
Source: definition of a continuous action
(blueprint: lem-sfb-connected-abelian-tower-descent-object). -/
def abelianTowerActionLabels (T : ConnectedAbelianCoverTower U I)
    (A : ContAction FintypeCat.{u} T.groupCone.pt) :
    Profinite.of (T.groupCone.pt × A.obj.V) ⟶ FintypeCat.toProfinite.obj A.obj.V :=
  ConcreteCategory.ofHom ⟨fun p ↦ ConcreteCategory.hom (A.obj.ρ p.1) p.2, A.property.1⟩

/-- The second base point and the unchanged finite label on the whole overlap.
Source: the two projections of the torsor comparison
(blueprint: lem-sfb-connected-abelian-tower-descent-object). -/
def abelianTowerDescentLabel (T : ConnectedAbelianCoverTower U I) (A : FintypeCat.{u}) :
    (abelianTowerLabels T.cone.pt).obj (Profinite.of (T.groupCone.pt × A)) ⟶
      (abelianTowerLabels T.cone.pt).obj (FintypeCat.toProfinite.obj A) := by
  let p₁ : Profinite.of (T.groupCone.pt × A) ⟶
      (forget₂ ProfiniteGrp Profinite).obj T.groupCone.pt :=
    ConcreteCategory.ofHom ⟨Prod.fst, continuous_fst⟩
  let p₂ : Profinite.of (T.groupCone.pt × A) ⟶ FintypeCat.toProfinite.obj A :=
    ConcreteCategory.ofHom ⟨Prod.snd, continuous_snd⟩
  let a := ((abelianTowerLabels T.cone.pt).map p₂).left ≫ pullback.fst _ _
  let b := ((abelianTowerLabels T.cone.pt).map p₁).left ≫
      T.comparison.hom ≫ pullback.snd _ _
  let l := pullback.lift a b
    ((comp_toSpecZ a).trans (comp_toSpecZ b).symm)
  refine MorphismProperty.Over.homMk l ?_
  change l ≫ (pullback.snd _ _ ≫ T.cone.pt.hom) = _
  dsimp only [l, b]
  rw [pullback.lift_snd_assoc]
  calc
    (((abelianTowerLabels T.cone.pt).map p₁).left ≫ T.comparison.hom ≫
        pullback.snd T.cone.pt.hom T.cone.pt.hom) ≫ T.cone.pt.hom =
        ((abelianTowerLabels T.cone.pt).map p₁).left ≫ T.comparison.hom ≫
          (pullback.snd T.cone.pt.hom T.cone.pt.hom ≫ T.cone.pt.hom) := by
            simp only [Category.assoc]
    _ = ((abelianTowerLabels T.cone.pt).map p₁).left ≫ T.comparison.hom ≫
          (pullback.fst T.cone.pt.hom T.cone.pt.hom ≫ T.cone.pt.hom) :=
      congrArg (fun f ↦ ((abelianTowerLabels T.cone.pt).map p₁).left ≫
        T.comparison.hom ≫ f) (pullback.condition (f := T.cone.pt.hom)
          (g := T.cone.pt.hom)).symm
    _ = ((abelianTowerLabels T.cone.pt).map p₁).left ≫
          (Scheme.UniversalCover.profiniteProductBase _ _ ≫ T.cone.pt.hom) :=
      congrArg (fun f ↦ ((abelianTowerLabels T.cone.pt).map p₁).left ≫ f)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f ↦ f ≫ T.cone.pt.hom) T.comparison_fst))
    _ = _ := ((abelianTowerLabels T.cone.pt).map p₁).w

/-- The base projection of the constructed overlap map.
Source: pullback universal property
(blueprint: lem-sfb-connected-abelian-tower-descent-object). -/
@[simp]
theorem abelianTowerDescentLabel_base (T : ConnectedAbelianCoverTower U I)
    (A : FintypeCat.{u}) :
    (abelianTowerDescentLabel T A).left ≫
      Scheme.UniversalCover.profiniteProductBase _ _ =
      ((abelianTowerLabels T.cone.pt).map
        (ConcreteCategory.ofHom ⟨Prod.fst, continuous_fst⟩)).left ≫
          T.comparison.hom ≫ pullback.snd _ _ := by
  dsimp only [abelianTowerDescentLabel]
  change pullback.lift _ _ _ ≫
    pullback.snd (toSpecZ (profiniteToProEt.obj (FintypeCat.toProfinite.obj A)).left)
      (toSpecZ T.cone.pt.left) = _
  exact pullback.lift_snd _ _ _

/-- The label projection of the constructed overlap map.
Source: pullback universal property
(blueprint: lem-sfb-connected-abelian-tower-descent-object). -/
@[simp]
theorem abelianTowerDescentLabel_label (T : ConnectedAbelianCoverTower U I)
    (A : FintypeCat.{u}) :
    (abelianTowerDescentLabel T A).left ≫ pullback.fst _ _ =
      ((abelianTowerLabels T.cone.pt).map
        (ConcreteCategory.ofHom ⟨Prod.snd, continuous_snd⟩)).left ≫ pullback.fst _ _ := by
  dsimp only [abelianTowerDescentLabel]
  change pullback.lift _ _ _ ≫
    pullback.fst (toSpecZ (profiniteToProEt.obj (FintypeCat.toProfinite.obj A)).left)
      (toSpecZ T.cone.pt.left) = _
  exact pullback.lift_fst _ _ _

/-- A normalized splitting and its monodromy for one finite-level sheaf.
This records only the object calculation; it asserts neither a functor nor descent of maps.
Source: Bhatt--Scholze, Lemmas 4.2.12 and 5.1.2
(blueprint: lem-sfb-connected-abelian-tower-descent-object). -/
structure AbelianTowerDescentObject (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ T.cone.pt.left)
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) where
  action : ContAction FintypeCat.{u} T.groupCone.pt
  fibre : ULift.{u + 1, u} action.obj.V ≃
    Scheme.proEtaleGeometricSetStalk (z ≫ T.cone.pt.hom) F
  section_ : F.obj.obj (op ((abelianTowerLabels T.cone.pt).obj
    (FintypeCat.toProfinite.obj action.obj.V)))
  normalized : IsAbelianTowerNormalizedSection T.cone.pt (Over.homMk z)
    F action.obj.V fibre section_
  unique : ∀ s, IsAbelianTowerNormalizedSection T.cone.pt (Over.homMk z)
    F action.obj.V fibre s → s = section_
  finiteLevel : ∀ (i : Iᵒᵖ), abelianTowerConstantAt F (T.levels.obj i) →
    ∃ (s : F.obj.obj (op ((abelianTowerLabels (T.levels.obj i)).obj
        (FintypeCat.toProfinite.obj action.obj.V))))
      (ρ : T.groups.obj i →* End action.obj.V),
      IsAbelianTowerNormalizedSection (T.levels.obj i)
        (Over.homMk z ≫ (Scheme.ProEt.forget U).map (T.cone.π.app i))
        F action.obj.V fibre s ∧
      F.obj.map (abelianTowerLabelTransport (T.cone.π.app i)
        (FintypeCat.toProfinite.obj action.obj.V)).op s = section_ ∧
      (∀ g : T.groupCone.pt, action.obj.ρ g = ρ (T.groupCone.π.app i g)) ∧
      ∀ (g : T.groups.obj i) (q : action.obj.V),
        abelianTowerLabelGerm (T.levels.obj i)
          (Over.homMk z ≫ (Scheme.ProEt.forget U).map (T.cone.π.app i) ≫
            (Scheme.ProEt.forget U).map (T.action i g)) F action.obj.V s q =
          fibre (ULift.up (ConcreteCategory.hom (ρ g) q))
  descent : F.obj.map
      ((abelianTowerLabels T.cone.pt).map (abelianTowerActionLabels T action)).op section_ =
    F.obj.map (abelianTowerDescentLabel T action.obj.V).op section_

/-- Objectwise finite-torsor descent, normalized by the actual geometric stalk.
Source: Bhatt--Scholze, Lemmas 4.2.12 and 5.1.2, finite connected torsor calculation
(blueprint: lem-sfb-connected-abelian-tower-descent-object).

Proof: Restriction along a site object is sectionwise restriction, by the object
inverse-image comparison and weakly etale localization. Represent finite constants
by finite labelled coproducts. On a connected scheme a map between finite constants
is a single map of label sets, because its clopen label partitions are constant.
The stalk of a constant finite sheaf is its label set: a locally constant label
becomes constant on the pointed open containing the geometric point. This also
proves that a map between such constants is determined by its stalk map.

Choose a finite-level trivialization of F. Its finite label set and inverse stalk
bijection give the labels and fibre equivalence. Relabel its inverse splitting so
that its labelled germs are exactly this equivalence. The ratio of two normalized
splittings has identity fibre map, hence is identity by the preceding connectedness
argument. This proves uniqueness at that level and, after pullback, at the limit.

The canonical overlap comparison, on the g-component of the finite torsor, is a
unique permutation rho(g) of the labels. Its diagonal value is identity. On the
triple (x,gx,hgx), the restriction cocycle gives rho(hg)=rho(g)rho(h). The groups
are abelian, so rho is a left action. Pull it back along the group-limit projection;
this is continuous because the quotient group and the label set are finite discrete.
Under the stipulated compatible torsor comparison the whole overlap map is the
constant permutation rho(a) on the clopen cylinder g_i=a. These finitely many
cylinders cover the overlap; separatedness gives the stated equation on its entire
profinite parameter scheme. At another trivializing level take a common later
level. Uniqueness identifies the two normalized splittings, and restriction of the
same overlap comparison identifies their actions. This proves all finite-level
clauses, including the germ at the acted point. No special nonempty-fibre assumption
is used: the empty constant sheaf has its unique automorphism and empty stalk. -/
theorem nonempty_abelianTowerDescentObject (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ T.cone.pt.left)
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (hF : T.finiteLevel F) :
    Nonempty (AbelianTowerDescentObject T z F) := by sorry

end AlgebraicGeometry.ProEtale
