/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Sheaf.SixFunctors.SemilinearProperOpenEvaluationSupport
import Mathlib.Logic.Function.Basic

/-! # The constant-coefficient evaluation ring square

Source: Stacks Project, Tags 03D6, 03D7, 09A5, 00WH and 0H7J; the coefficient-square
calculation in `SemilinearProperOpenMatePasting`, lines 1685--1790
(blueprint: lem-sf-semilinear-evaluation-ring-square).

The coefficient identification and level direct image below are the recorded constructions,
with the level ring map expressed as the right transpose of the specified structure map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory Opposite AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The specified identity coefficient identification on the vertical slice, after forgetting
commutativity. Source: Zheng, Construction 4.1; Stacks 03D6
(blueprint: lem-sf-semilinear-evaluation-ring-square). -/
abbrev evaluationCoefficientIdentification (X : Scheme.{u}) (n : ℕ) :=
  eqToHom (SemilinearSections.evaluation_ring.{u + 1, u, u + 1}
    (ProEt.topology X) (coefficients C X) (transition C τ X) n).symm

/-- The level structural ring map is the right-adjoint transpose of the canonical
constant-ring inverse-image map. Source: Stacks 09A5 and 0H7J
(blueprint: lem-sf-semilinear-evaluation-ring-square). -/
def evaluationCoefficientDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    coefficients C Y n ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (coefficients C X n) :=
  (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv
    (coefficients C Y n) (coefficients C X n)
    (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (C n))

attribute [local irreducible] constantSheaf

private theorem evaluationCoefficientDirectImage_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    evaluationCoefficientDirectImage C f n =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C n) := by
  exact ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

private theorem evaluation_coefficientMap_app {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) (U : Y.ProEt) :
    (coefficientMap C τ f).hom.app (op (n, U)) =
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C n)).hom.app (op U) := by
  exact eq_of_heq ((coefficientMap_existsUnique C τ f).choose_spec.1 n U)

attribute [local irreducible] coefficientMap proEtaleConstantDirectImageMap
  evaluationCoefficientDirectImage proEtaleRingDirectImageMap

/-- Evaluation commutes with the specified constant-coefficient ring map and yields the
unique identity-on-sections direct-image comparison, compatible with every coefficient
transition after restriction of scalars. No finiteness or flatness is assumed.

Source: Stacks 03D6, 03D7, 09A5, 00WH and 0H7J; the evaluation calculation in
`SemilinearProperOpenMatePasting`, lines 1685--1790
(blueprint: lem-sf-semilinear-evaluation-ring-square).

Proof: (1) Write rho for the constant-section map. The canonical inverse-image structure
map is its left transpose, so its right transpose phi equals rho by cancellation of the
ring-sheaf adjunction hom equivalence. (2) Evaluation of the sequence ring at (n,H) is B_n(H),
and the specified coefficient identification is the identity there. Both base-change/slice
composites send H to (n,H times_Y X), also on arrows. The system coefficient map at that
object is rho_n, so the ring square follows from (1) section by section.
(3) Both module composites have section group M_n(H times_Y X). Their actions are restriction
along the two equal ring maps from (2). The identity is therefore linear in both directions;
no coefficient lift is chosen. (4) Restrictions along H' to H and maps M to N are the same on
both sides, so the identity maps define a natural isomorphism. Sectionwise extensionality
proves uniqueness. (5) For m >= n, both coefficient composites extend the constant map
c to tau_{m,n}(c), hence agree by the sheafification universal property. After restricting
scalars, both comparison/transition paths apply the actual horizontal restriction of M.
The inverse has the same formula. Equality indices and composite transitions are included.
The dependencies are the recorded inverse-image adjunction, constant-ring operations,
semilinear evaluation and transitions, module direct image, restriction of scalars and
sheafification, exactly as in the five DAG proof steps. -/
theorem semilinearEvaluationRingSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ n : ℕ,
      evaluationCoefficientIdentification C τ Y n ≫
        ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology Y))).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (coefficientMap C τ f)) =
      (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (evaluationCoefficientDirectImage C f n) ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).map
          (evaluationCoefficientIdentification C τ X n)) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      evaluationCoefficientDirectImage C f m ≫
          (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
            (SemilinearSections.coefficientMap (ProEt.topology X)
              (coefficients C X) (transition C τ X) h) =
        SemilinearSections.coefficientMap (ProEt.topology Y)
            (coefficients C Y) (transition C τ Y) h ≫
          evaluationCoefficientDirectImage C f n) := by
  constructor
  · intro n
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have ha : (evaluationCoefficientIdentification C τ Y n).hom.app U = 𝟙 _ := by
      dsimp only [evaluationCoefficientIdentification]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hb : (evaluationCoefficientIdentification C τ X n).hom.app
        ((proEtaleBaseChange f).op.obj U) = 𝟙 _ := by
      dsimp only [evaluationCoefficientIdentification]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change (evaluationCoefficientIdentification C τ Y n).hom.app U ≫
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((coefficientMap C τ f).hom.app (op (n, U.unop))) =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((evaluationCoefficientDirectImage C f n).hom.app U) ≫
      (evaluationCoefficientIdentification C τ X n).hom.app
        ((proEtaleBaseChange f).op.obj U)
    rw [ha, hb]
    erw [Category.id_comp, Category.comp_id]
    rw [evaluationCoefficientDirectImage_eq]
    exact congrArg (fun a ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map a)
      (evaluation_coefficientMap_app C τ f n U.unop)
  · intro m n h
    rw [evaluationCoefficientDirectImage_eq, evaluationCoefficientDirectImage_eq]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have e := (coefficientMap C τ f).hom.naturality
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
    dsimp only [Functor.sheafPushforwardContinuous_obj_obj_map,
      ringSystem, systemRing, ringPresheaf, Functor.comp_map,
      Functor.uncurry_obj_map, prodOpEquiv, siteMap, Functor.prod_map,
      Functor.id_map, Functor.op_map, Functor.op_obj, sheafToPresheaf] at e
    change (((rings (ProEt.topology Y) (coefficients C Y) (transition C τ Y)).map
      (homOfLE h).op).hom.app U ≫ (coefficients C Y n).obj.map (𝟙 U)) ≫ _ =
      _ ≫ (((rings (ProEt.topology X) (coefficients C X) (transition C τ X)).map
        (homOfLE h).op).hom.app ((proEtaleBaseChange f).op.obj U) ≫
        (coefficients C X n).obj.map ((proEtaleBaseChange f).op.map (𝟙 U))) at e
    erw [(coefficients C Y n).obj.map_id,
      (proEtaleBaseChange f).op.map_id, (coefficients C X n).obj.map_id,
      Category.comp_id, Category.comp_id] at e
    rw [evaluation_coefficientMap_app C τ f n U.unop,
      evaluation_coefficientMap_app C τ f m U.unop] at e
    change (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C m) ≫
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
        (SemilinearSections.coefficientMap (ProEt.topology X)
          (coefficients C X) (transition C τ X) h)).hom.app U =
      (SemilinearSections.coefficientMap (ProEt.topology Y)
          (coefficients C Y) (transition C τ Y) h ≫
        proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C n)).hom.app U
    exact e.symm


set_option maxHeartbeats 400000 in
-- Sectionwise uniqueness compares the carriers of two composite pushforward functors.
/-- The level comparison is uniquely the identity in both directions on all section groups.
Source: Stacks 03D6 and 03D7
(blueprint: lem-sf-semilinear-evaluation-ring-square).
Proof: use the ring square to identify the scalar actions. Identity maps are linear,
commute with restrictions and system morphisms, and are inverse. Any other normalized
comparison has the same components, so sectionwise extensionality proves uniqueness. -/
theorem evaluationPush_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : push C τ f ⋙ SemilinearSections.evaluation (ProEt.topology Y)
      (coefficients C Y) (transition C τ Y) n ≅
    SemilinearSections.evaluation (ProEt.topology X)
      (coefficients C X) (transition C τ X) n ⋙ StrictTower.moduleDirectImage (C n) f,
      (∀ (M : Modules C τ X) (H : Y.ProEt),
        HEq (fun x ↦ (d.hom.app M).val.app (op H) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj H)) ↦ x)) ∧
      (∀ (M : Modules C τ X) (H : Y.ProEt),
        HEq (fun x ↦ (d.inv.app M).val.app (op H) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj H)) ↦ x)) := by
  obtain ⟨d, hd, hi⟩ := level_push_evaluation_normalized C τ n f (push C τ f)
    (push_eq C τ f)
  refine ⟨d, ⟨hd, hi⟩, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext U x
  exact congrFun (eq_of_heq ((hd'.1 M U.unop).trans (hd M U.unop).symm)) x


/-- The unique section-normalized comparison, selected from its determining property.
Source: Stacks 03D6 and 03D7
(blueprint: lem-sf-semilinear-evaluation-ring-square). -/
def evaluationPush {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    push C τ f ⋙ SemilinearSections.evaluation (ProEt.topology Y)
      (coefficients C Y) (transition C τ Y) n ≅
    SemilinearSections.evaluation (ProEt.topology X)
      (coefficients C X) (transition C τ X) n ⋙ StrictTower.moduleDirectImage (C n) f :=
  (evaluationPush_existsUnique C τ f n).exists.choose

attribute [local irreducible] evaluationPush push StrictTower.constantRingIso
  proEtaleConstantInverseImageMap

private theorem normalized_apply
    {A B D E : Type u} (hA : A = D) (hB : B = E)
    {f : A → B} {g : D → E} (hf : HEq f g)
    {x : A} {y : D} (hx : HEq x y) : HEq (f x) (g y) := by
  subst D E
  rw [eq_of_heq hf, eq_of_heq hx]

set_option maxHeartbeats 400000 in
-- Comparing the section carriers of both pushforward composites needs additional reduction.
/-- Both directions of the normalized comparison commute with every horizontal transition
on underlying groups, after the scalar restriction in the preceding ring square.
Source: Stacks 03D6, 00WH and 0H7J
(blueprint: lem-sf-semilinear-evaluation-ring-square).
Proof: each comparison is identity on sections. Both paths are therefore the same actual
horizontal restriction of M. At the source index the comparison is identity by its
defining normalization.
The coefficient ring square identifies the restricted scalar
actions, including equality indices and composites, with no chosen lifts. -/
theorem evaluationPush_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m n : ℕ) (h : n ≤ m) (M : Modules C τ X) (H : Y.ProEt) :
    HEq
      (fun x ↦ ((evaluationPush C τ f n).hom.app M).val.app (op H)
        (((push C τ f).obj M).val.map (Prod.mkHom (homOfLE h) (𝟙 H)).op x))
      (fun x : M.val.obj (op (m, (proEtaleBaseChange f).obj H)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 ((proEtaleBaseChange f).obj H))).op x) ∧
    HEq
      (fun x ↦ ((evaluationPush C τ f n).inv.app M).val.app (op H)
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 ((proEtaleBaseChange f).obj H))).op x))
      (fun x : ((push C τ f).obj M).val.obj (op (m, H)) ↦
        ((push C τ f).obj M).val.map (Prod.mkHom (homOfLE h) (𝟙 H)).op x) := by
  have hd : HEq (fun x ↦ ((evaluationPush C τ f n).hom.app M).val.app (op H) x)
      (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj H)) ↦ x) := by
    unfold evaluationPush
    exact (evaluationPush_existsUnique C τ f n).exists.choose_spec.1 M H
  have hi : HEq (fun x ↦ ((evaluationPush C τ f n).inv.app M).val.app (op H) x)
      (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj H)) ↦ x) := by
    unfold evaluationPush
    exact (evaluationPush_existsUnique C τ f n).exists.choose_spec.2 M H
  have hm : (((push C τ f).obj M).val.obj (op (m, H)) : Type (u + 1)) =
      (M.val.obj (op (m, (proEtaleBaseChange f).obj H)) : Type (u + 1)) := by
    unfold push
    rfl
  let F := push C τ f ⋙ SemilinearSections.evaluation (ProEt.topology Y)
    (coefficients C Y) (transition C τ Y) n
  let G := SemilinearSections.evaluation (ProEt.topology X)
    (coefficients C X) (transition C τ X) n ⋙ StrictTower.moduleDirectImage (C n) f
  have hFn : ((F.obj M).val.obj (op H) : Type (u + 1)) =
      (M.val.obj (op (n, (proEtaleBaseChange f).obj H)) : Type (u + 1)) := by
    dsimp only [F]
    unfold push
    rfl
  have hGn : ((G.obj M).val.obj (op H) : Type (u + 1)) =
      (M.val.obj (op (n, (proEtaleBaseChange f).obj H)) : Type (u + 1)) := by
    rfl
  have hp : HEq
      (fun x ↦ ((push C τ f).obj M).val.map
        (Prod.mkHom (homOfLE h) (𝟙 H)).op x)
      (fun x ↦ M.val.map (Prod.mkHom (homOfLE h)
        (𝟙 ((proEtaleBaseChange f).obj H))).op x) := by
    unfold push
    change HEq (fun x ↦ M.val.presheaf.map ((siteMap f).map
      (Prod.mkHom (homOfLE h) (𝟙 H))).op x)
      (fun x ↦ M.val.presheaf.map (Prod.mkHom (homOfLE h)
        (𝟙 ((proEtaleBaseChange f).obj H))).op x)
    simp only [siteMap, Functor.prod_map, Functor.id_map,
      CategoryTheory.Functor.map_id]
    rfl
  have hn : (((push C τ f).obj M).val.obj (op (n, H)) : Type (u + 1)) =
      (M.val.obj (op (n, (proEtaleBaseChange f).obj H)) : Type (u + 1)) := by
    unfold push
    rfl
  constructor
  · apply Function.hfunext hm
    intro x y hxy
    have hq := normalized_apply hm hn hp hxy
    exact normalized_apply hFn hGn hd hq
  · apply Function.hfunext hm.symm
    intro x y hxy
    have hq := normalized_apply hm.symm hn.symm hp.symm hxy
    have hr := normalized_apply hGn hFn hi
      (HEq.refl (M.val.presheaf.map (Prod.mkHom (homOfLE h)
        (𝟙 ((proEtaleBaseChange f).obj H))).op x))
    exact hr.trans hq

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
