/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import Sheaf.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Sheaf.CategoryTheory.InternalSectionTensorComparison

/-! # Ordinary diagonal tensor on condensed internal actions

Source: main-20261015 direct-images proof (sk-thm-sf-ctf-stability-direct-images.proof.md),
paragraph (3), agent-formulated formal restriction and cup-product infrastructure;
exact reference wanted
(blueprint: def-sfb-condensed-action-tensor).

## Main definitions

* `ActionTensorData`, `actionTensor`: the relative internal-module tensor on actions of an
  arbitrary topological group, with diagonal action on generalized pure tensors, the strong
  forgetful comparison, ordinary symmetry, closed structure and flat resolutions.
* `TrivialTensorData`, `trivialTensor`: the strong tensor comparison of trivial inflation,
  identity on underlying module tensors and on the regular unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar
namespace CategoryTheory.CondensedDerivedRestriction
variable {A A' : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The pure-tensor section of the actual relative internal-module tensor product.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
def tensorSection {A : CondensedBar.Ring.{u}} (M N : Modules A) (S : Profinite.{u})
    (x : sections A M S) (y : sections A N S) : sections A (M ⊗ N) S :=
  (Mod.tensorObjπ M N).hom.app (op S)
    ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) M.X N.X).app
        (op S) (TensorProduct.tmul ℤ x y))


/-- The ordinary diagonal tensor on actions, specified by its underlying relative tensor
and its action on every generalized pure tensor. The strong forgetful comparison also
fixes associators and unitors; it is not a freely chosen tensor structure.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
structure ActionTensorData (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  monoidal : MonoidalCategory (Equivariant A G)
  forgetCore : @Functor.CoreMonoidal (Equivariant A G) _ monoidal
    (Modules A) _ _ (CondensedBar.forgetAction (A := A) (G := G))
  diagonal : ∀ (M N : Equivariant A G) (S : Profinite.{u}) (g : C(S, G))
    (x : sections A M.module S) (y : sections A N.module S),
    (monoidal.tensorObj M N).act S g
      (((forgetCore.μIso M N).hom).hom.hom.app (op S)
        (tensorSection (A := A) M.module N.module S x y)) =
    ((forgetCore.μIso M N).hom).hom.hom.app (op S)
      (tensorSection (A := A) M.module N.module S (M.act S g x) (N.act S g y))
  symmetric : @SymmetricCategory (Equivariant A G) _ monoidal
  symmetry : ∀ M N : Equivariant A G,
    (forgetCore.μIso M N).hom ≫
        (@BraidedCategory.braiding (Equivariant A G) _ monoidal
          symmetric.toBraidedCategory M N).hom.val =
      (β_ M.module N.module).hom ≫ (forgetCore.μIso N M).hom
  closed : @MonoidalClosed (Equivariant A G) _ monoidal
  additive : @MonoidalPreadditive (Equivariant A G) _ _ monoidal
  flat : @Abelian.HasFunctorialFlatResolution (Equivariant A G) _ monoidal

private theorem action_trivial_of_pure
    (M N T : Equivariant A G) (e : M.module ⊗ N.module ≅ T.module)
    (h : ∀ (S : Profinite.{u}) (g : C(S, G))
      (x : sections A M.module S) (y : sections A N.module S),
      T.act S g ((e.hom.hom.hom.app (op S)) (tensorSection M.module N.module S x y)) =
        (e.hom.hom.hom.app (op S)) (tensorSection M.module N.module S x y)) :
    ∀ (S : Profinite.{u}) (g : C(S, G)) (z : sections A T.module S), T.act S g z = z := by
  let E := sectionsFunctor A
  obtain ⟨i, hi⟩ := InternalAbelianSheafModule.exists_sectionTensorIso
    (coherentTopology Profinite.{u}) A.X M.module N.module
  let P := ((E.obj M.module).val ⊗ (E.obj N.module).val).presheaf
  let q : P ⟶ T.module.X.obj := toSheafify (coherentTopology Profinite.{u}) P ≫
    (PresheafOfModules.toPresheaf _).map (i.inv ≫ E.map e.hom).val
  let k := (SheafOfModules.toSheaf _).mapIso (i.symm ≪≫ E.mapIso e)
  have hq : Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) q := by
    change Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (toSheafify (coherentTopology Profinite.{u}) P ≫ k.hom.hom)
    have : IsIso k.hom.hom := inferInstance
    exact Presheaf.isLocallySurjective_comp _ _ _
  have ht (S : Profinite.{u}) (x : sections A M.module S)
      (y : sections A N.module S) :
      q.app (op S) (TensorProduct.tmul (((InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) A.X).obj ⋙ forget₂ CommRingCat RingCat).obj (op S)) x y) =
        (e.hom.hom.hom.app (op S)) (tensorSection M.module N.module S x y) := by
    have hh := hi (op S) x y
    have he := congrArg (fun f ↦ f.val.app (op S)
      (tensorSection M.module N.module S x y)) i.hom_inv_id
    change i.inv.val.app (op S) (i.hom.val.app (op S)
      (tensorSection M.module N.module S x y)) = _ at he
    erw [hh] at he
    exact congrArg ((e.hom.hom.hom.app (op S)).hom) he
  intro S g z
  let W : (coherentTopology Profinite.{u}).Cover S :=
    ⟨Presheaf.imageSieve q z, Presheaf.imageSieve_mem (coherentTopology Profinite.{u}) q z⟩
  let B := (sheafCompose (coherentTopology Profinite.{u})
    (forget AddCommGrpCat.{u + 1})).obj T.module.X
  have he : (↾fun _ : PUnit ↦ T.act S g z) = (↾fun _ : PUnit ↦ z) :=
    B.property.hom_ext W _ _ (fun I ↦ by
      ext t
      change (T.module.X.obj.map I.f.op).hom (T.act S g z) =
        (T.module.X.obj.map I.f.op).hom z
      rw [T.naturality]
      obtain ⟨w, hw⟩ := I.hf
      change q.app _ w = (T.module.X.obj.map I.f.op).hom z at hw
      rw [← hw]
      clear hw
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul x y => erw [ht]; exact h _ _ x y)
  exact ConcreteCategory.congr_hom he PUnit.unit

private theorem trivial_core (d : ActionTensorData A G) :
    letI : MonoidalCategory (Equivariant A G) := d.monoidal
    ∃ c : (trivial (R := A.toMon) (P := G)).CoreMonoidal,
      (∀ M N, (c.μIso M N).hom.val = (d.forgetCore.μIso
        ((trivial (R := A.toMon) (P := G)).obj M)
        ((trivial (R := A.toMon) (P := G)).obj N)).inv) ∧
      c.εIso.hom.val = d.forgetCore.εIso.inv := by
  let : MonoidalCategory (Equivariant A G) := d.monoidal
  let U := CondensedBar.forgetAction (A := A) (G := G)
  let F := trivial (R := A.toMon) (P := G)
  let : U.Monoidal := d.forgetCore.toMonoidal
  have hμ (M N : Equivariant A G) :
      Functor.LaxMonoidal.μ U M N = (d.forgetCore.μIso M N).hom := rfl
  have hδ (M N : Equivariant A G) :
      Functor.OplaxMonoidal.δ U M N = (d.forgetCore.μIso M N).inv := rfl
  have hη : Functor.OplaxMonoidal.η U = d.forgetCore.εIso.inv := rfl
  have hUF {M N : Modules A} (f : M ⟶ N) : U.map (F.map f) = f := rfl
  have ht (M N : Modules A) : ∀ (S : Profinite.{u}) (g : C(S, G))
      (z : sections A ((F.obj M) ⊗ (F.obj N)).module S),
      ((F.obj M) ⊗ (F.obj N)).act S g z = z := by
    apply action_trivial_of_pure (A := A) (G := G) (F.obj M) (F.obj N)
      (d.monoidal.tensorObj (F.obj M) (F.obj N))
      (d.forgetCore.μIso (F.obj M) (F.obj N))
    intro S g x y
    exact d.diagonal (F.obj M) (F.obj N) S g x y
  have hu : ∀ (S : Profinite.{u}) (g : C(S, G))
      (z : sections A (𝟙_ (Equivariant A G)).module S),
      (𝟙_ (Equivariant A G)).act S g z = z := by
    intro S g z
    let L : Equivariant A G := 𝟙_ (Equivariant A G)
    let X := F.obj (𝟙_ (Modules A))
    let e := d.forgetCore.μIso L X
    have h := ((λ_ X).hom.property S g
      ((e.hom.hom.hom.app (op S)) (tensorSection L.module X.module S z (1 : sectionRing A S))))
    rw [d.diagonal] at h
    have hi : Function.Injective
        (fun t : sections A (L.module ⊗ X.module) S ↦
          (((λ_ X).hom.val.hom.hom.app (op S)).hom)
            (((e.hom.hom.hom.app (op S)).hom) t)) := by
      let k := e ≪≫ U.mapIso (λ_ X)
      have : IsIso ((k.hom.hom.hom.app (op S))) := inferInstance
      exact (ConcreteCategory.bijective_of_isIso (k.hom.hom.hom.app (op S))).injective
    have he := hi h
    have hh := congrArg
      (fun t ↦ (((ρ_ L.module).hom.hom.hom.app (op S)).hom) t) he
    change (((ρ_ L.module).hom.hom.hom.app (op S)).hom)
        (tensorSection L.module (𝟙_ (Modules A)) S (L.act S g z) (1 : sectionRing A S)) =
      (((ρ_ L.module).hom.hom.hom.app (op S)).hom)
        (tensorSection L.module (𝟙_ (Modules A)) S z (1 : sectionRing A S)) at hh
    have hr (t : sections A L.module S) :
        (((ρ_ L.module).hom.hom.hom.app (op S)).hom)
          (tensorSection L.module (𝟙_ (Modules A)) S t (1 : sectionRing A S)) = t := by
      have hr := InternalAbelianSheafModule.comparison_internalTmul_rightUnitor
        (coherentTopology Profinite.{u}) A.X L.module (op S) t (1 : sectionRing A S)
      simp only [one_smul] at hr
      exact hr
    rw [hr, hr] at hh
    exact hh
  let liftIso (M N : Equivariant A G) (e : M.module ≅ N.module)
      (hM : ∀ S g z, M.act S g z = z) (hN : ∀ S g z, N.act S g z = z) : M ≅ N :=
    { hom := ⟨e.hom, by intro S g z; change _ = N.act S g _; rw [hM, hN]⟩
      inv := ⟨e.inv, by intro S g z; change _ = M.act S g _; rw [hM, hN]⟩
      hom_inv_id := Subtype.ext e.hom_inv_id
      inv_hom_id := Subtype.ext e.inv_hom_id }
  have hLift (M N : Equivariant A G) (e : M.module ≅ N.module)
      (hM : ∀ S g z, M.act S g z = z) (hN : ∀ S g z, N.act S g z = z) :
      U.map (liftIso M N e hM hN).hom = e.hom := rfl
  let c : F.CoreMonoidal :=
    { εIso := liftIso _ _ d.forgetCore.εIso.symm hu (fun _ _ _ ↦ rfl)
      μIso M N := liftIso _ _ (d.forgetCore.μIso (F.obj M) (F.obj N)).symm
        (ht M N) (fun _ _ _ ↦ rfl)
      μIso_hom_natural_left := by
        intro M M' f N
        apply Subtype.ext
        change U.map ((F.map f) ▷ F.obj N) ≫
          (d.forgetCore.μIso (F.obj M') (F.obj N)).inv =
            (d.forgetCore.μIso (F.obj M) (F.obj N)).inv ≫ (f ▷ N)
        simp only [Functor.Monoidal.map_whiskerRight, hμ, hδ, hUF, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
        rfl
      μIso_hom_natural_right := by
        intro N N' M f
        apply Subtype.ext
        change U.map (F.obj M ◁ F.map f) ≫
          (d.forgetCore.μIso (F.obj M) (F.obj N')).inv =
            (d.forgetCore.μIso (F.obj M) (F.obj N)).inv ≫ (M ◁ f)
        simp only [Functor.Monoidal.map_whiskerLeft, hμ, hδ, hUF, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
        rfl
      associativity := by
        intro M N P
        apply Subtype.ext
        change U.map (_ ▷ _) ≫
          (d.forgetCore.μIso (F.obj (M ⊗ N)) (F.obj P)).inv ≫ (α_ M N P).hom =
            U.map (α_ (F.obj M) (F.obj N) (F.obj P)).hom ≫
              U.map (_ ◁ _) ≫ (d.forgetCore.μIso (F.obj M) (F.obj (N ⊗ P))).inv
        simp only [Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_whiskerLeft,
          Functor.Monoidal.map_associator, hμ, hδ, hLift, Iso.symm_hom, Category.assoc,
          Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
        simp only [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
          MonoidalCategory.whiskerLeft_id]
        rfl
      left_unitality := by
        intro M
        apply Subtype.ext
        change U.map (λ_ (F.obj M)).hom = U.map (_ ▷ _) ≫
          (d.forgetCore.μIso (F.obj (𝟙_ (Modules A))) (F.obj M)).inv ≫ (λ_ M).hom
        simp only [Functor.Monoidal.map_leftUnitor, Functor.Monoidal.map_whiskerRight,
          hμ, hδ, hη, hLift, Iso.symm_hom, Category.assoc,
          Iso.hom_inv_id_assoc]
        rfl
      right_unitality := by
        intro M
        apply Subtype.ext
        change U.map (ρ_ (F.obj M)).hom = U.map (_ ◁ _) ≫
          (d.forgetCore.μIso (F.obj M) (F.obj (𝟙_ (Modules A)))).inv ≫ (ρ_ M).hom
        simp only [Functor.Monoidal.map_rightUnitor, Functor.Monoidal.map_whiskerLeft,
          hμ, hδ, hη, hLift, Iso.symm_hom, Category.assoc,
          Iso.hom_inv_id_assoc]
        rfl }
  exact ⟨c, fun _ _ ↦ rfl, rfl⟩

/-- Existence of the usual diagonal tensor, closed structure, and functorial flat
resolutions on the action site. The tensor is determined up to the unique bilinear
comparison by the displayed pure-tensor and unit normalizations.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor).
Proof: tensor the underlying modules and give it the diagonal action; the universal
balanced bilinear map induces the action and its coherence. Internal Hom carries the
conjugation action and satisfies the tensor-Hom adjunction. On the action site sums of
free modules represented by test objects surject functorially and are flat; use these
for functorial flat resolutions. The signed total tensor and K-flat localization then
give the ordinary derived tensor, rather than a tensor on continuous cochains. -/
theorem actionTensorExist : Nonempty (ActionTensorData A G) := by
  sorry

/-- Choose the diagonal tensor with its displayed universal-property comparisons.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
def actionTensor (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ActionTensorData A G :=
  Classical.choice (actionTensorExist (A := A) (G := G))

/-- The diagonal action tensor, with its ordinary internal-module tensor underneath.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionMonoidal : MonoidalCategory (Equivariant A G) := (actionTensor A G).monoidal

/-- Closedness is the ordinary internal Hom with conjugation action.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionClosed : MonoidalClosed (Equivariant A G) := (actionTensor A G).closed

/-- Symmetry is the ordinary interchange of the two module factors.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionSymmetric : SymmetricCategory (Equivariant A G) := (actionTensor A G).symmetric

/-- The tensor is additive on the original action-category morphisms.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionTensorAdditive : MonoidalPreadditive (Equivariant A G) :=
  (actionTensor A G).additive

/-- Flat resolutions on the action site for the specified tensor.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionFlat : Abelian.HasFunctorialFlatResolution (Equivariant A G) :=
  (actionTensor A G).flat


/-- Ordinary trivial action with its strong diagonal-tensor comparison. The comparison
is identity on the underlying module tensor and on the regular module.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
structure TrivialTensorData (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  core : (trivial (R := A.toMon) (P := G)).CoreMonoidal
  tensor : ∀ M N, (core.μIso M N).hom.val =
      ((actionTensor A G).forgetCore.μIso
        ((trivial (R := A.toMon) (P := G)).obj M)
        ((trivial (R := A.toMon) (P := G)).obj N)).inv
  unit : core.εIso.hom.val = (actionTensor A G).forgetCore.εIso.inv

/-- The strong monoidal comparison for trivial action is fixed by its underlying tensor.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor).
Proof: both sides have trivial action on the ordinary tensor; the balanced bilinear
identity gives the tensor comparison, the regular-module identity gives the unit.
Coherence follows after forgetting the action, which is faithful. -/
theorem trivialTensorExist : Nonempty (TrivialTensorData A G) := by
  obtain ⟨c, ht, hu⟩ := trivial_core (actionTensor A G)
  exact ⟨⟨c, ht, hu⟩⟩

/-- Ordinary tensor comparison for trivial inflation, with identity underlying maps.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
def trivialTensor (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : TrivialTensorData A G :=
  Classical.choice (trivialTensorExist (A := A) (G := G))

/-- The usual strong monoidal trivial inflation.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance trivialMonoidal : (trivial (R := A.toMon) (P := G)).Monoidal :=
  (trivialTensor A G).core.toMonoidal

/-- Trivial action preserves colimits, computed on the underlying modules.
Source: paragraph (3), action-site presentation
(blueprint: def-sfb-condensed-action-tensor).
Proof: the action on the colimit of a diagram of trivial actions is trivial, and the
underlying colimit universal property is the equivariant universal property. -/
@[instance] theorem trivialColimitsAll :
    PreservesColimitsOfSize.{u + 1, u + 1} (trivial (R := A.toMon) (P := G)) := by
  exact (invariants A G).adjunction.leftAdjoint_preservesColimits

/-- The small colimits used by total tensor comparisons are preserved by trivial action.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor).
Proof: shrink the underlying module colimit; the trivial-action colimit universal
property is the same equivariant universal property. -/
@[instance] theorem trivialSmallColimits :
    PreservesColimitsOfSize.{0, 0} (trivial (R := A.toMon) (P := G)) := by
  exact preservesSmallestColimits_of_preservesColimits
    (trivial (R := A.toMon) (P := G))


/-- Small colimits for the ordinary total tensor sums.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance moduleSmallColimits : HasColimitsOfSize.{0, 0} (Modules A) :=
  hasColimitsOfSizeShrink _

/-- Small colimits for the ordinary total tensor sums.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionSmallColimits : HasColimitsOfSize.{0, 0} (Equivariant A G) :=
  hasColimitsOfSizeShrink _

end CategoryTheory.CondensedDerivedRestriction
