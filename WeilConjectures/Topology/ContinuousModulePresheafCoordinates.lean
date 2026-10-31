/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Continuous-module presheaf actions and finite coordinates

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, first two sentences
(blueprint: lem-sfb-continuous-module-presheaf-coordinates).

The coefficient presheaf is the existing continuous-map ring presheaf. Sectionwise
modules and their linear natural maps are Mathlib's `PresheafOfModules`. Tensor products
of abelian presheaves are the existing objectwise integer tensor, not sheaf tensors.

## Main statements

- `Profinite.continuousModulePresheaf_coordinates`: continuous sections, their action,
  additive postcomposition functor, coordinate products, and regular normalization.
- `Profinite.continuousModulePresheaf_action_iff`: the equivalent tensor-action description.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj Opposite

namespace Profinite

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private noncomputable def sectionAction
    {C : Type*} [Category C] {B : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (Q : PresheafOfModules.{u + 1} B) :
    (B ⋙ forget₂ RingCat Ab) ⊗ Q.presheaf ⟶ Q.presheaf where
  app S := AddCommGrpCat.ofHom (TensorProduct.liftAddHom
    (smulAddHom (B.obj S) (Q.obj S)) (by
      intro n a h
      simp only [map_zsmul]
      rfl))
  naturality S T q := by
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a h
    exact (Q.map_smul q a h).symm

private lemma sectionAction_tmul
    {C : Type*} [Category C] {B : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (Q : PresheafOfModules.{u + 1} B) (S : Cᵒᵖ) (a : B.obj S) (h : Q.obj S) :
    (sectionAction Q).app S (TensorProduct.tmul ℤ a h) = a • h := rfl

private lemma sectionAction_one
    {C : Type*} [Category C] {B : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (Q : PresheafOfModules.{u + 1} B) :
    (η[B ⋙ forget₂ RingCat Ab] ▷ Q.presheaf) ≫ sectionAction Q =
      (λ_ Q.presheaf).hom := by
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro n h
  change (n.down : B.obj S) • h = n.down • h
  exact Int.cast_smul_eq_zsmul (B.obj S) n.down h

private lemma sectionAction_mul
    {C : Type*} [Category C] {B : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (Q : PresheafOfModules.{u + 1} B) :
    (μ[B ⋙ forget₂ RingCat Ab] ▷ Q.presheaf) ≫ sectionAction Q =
      (α_ (B ⋙ forget₂ RingCat Ab) (B ⋙ forget₂ RingCat Ab) Q.presheaf).hom ≫
        ((B ⋙ forget₂ RingCat Ab) ◁ sectionAction Q) ≫ sectionAction Q := by
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext_threefold (M := B.obj S) (N := B.obj S) (P := Q.obj S)
  intro a b h
  change ((a : B.obj S) * (b : B.obj S)) • (h : Q.obj S) =
    (a : B.obj S) • (b : B.obj S) • (h : Q.obj S)
  exact mul_smul (a : B.obj S) (b : B.obj S) (h : Q.obj S)

private lemma sectionAction_unique
    {C : Type*} [Category C] {B : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (Q : PresheafOfModules.{u + 1} B)
    (g : (B ⋙ forget₂ RingCat Ab) ⊗ Q.presheaf ⟶ Q.presheaf)
    (hg : ∀ S (a : B.obj S) (h : Q.obj S),
      g.app S (TensorProduct.tmul ℤ a h) = a • h) : g = sectionAction Q := by
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  exact hg S

private lemma sectionAction_natural
    {C : Type*} [Category C] {B : Cᵒᵖ ⥤ RingCat.{u + 1}}
    {Q Q' : PresheafOfModules.{u + 1} B} (f : Q ⟶ Q') :
    sectionAction Q ≫ (PresheafOfModules.toPresheaf B).map f =
      ((B ⋙ forget₂ RingCat Ab) ◁ (PresheafOfModules.toPresheaf B).map f) ≫
        sectionAction Q' := by
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a h
  exact (f.app S).hom.map_smul a h

@[instance_reducible]
private noncomputable def sectionsModule (M : TopModuleCat.{u} R) (S : Profinite.{u}ᵒᵖ) :
    Module ((continuousMapRingPresheafOfUniverse.{u, u} R).obj S)
      (ULift.{u + 1} C(S.unop, M)) :=
  Module.compHom _ ULift.ringEquiv.toRingHom

attribute [local instance] sectionsModule

private noncomputable def sections (M : TopModuleCat.{u} R) :
    PresheafOfModules.{u + 1} (continuousMapRingPresheafOfUniverse.{u, u} R) := by
  letI (S : Profinite.{u}ᵒᵖ) := sectionsModule R M S
  exact {
  obj S := ModuleCat.of _ (ULift.{u + 1} C(S.unop, M))
  map {S T} q := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars
      ((continuousMapRingPresheafOfUniverse.{u, u} R).map q).hom).obj
        (ModuleCat.of _ (ULift.{u + 1} C(T.unop, M))))
    { toFun := fun h ↦ ULift.up (h.down.comp q.unop.hom.hom)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionsFunctor : TopModuleCat.{u} R ⥤
    PresheafOfModules.{u + 1} (continuousMapRingPresheafOfUniverse.{u, u} R) where
  obj M := sections R M
  map f :=
    { app S := ModuleCat.ofHom
        { toFun := fun h ↦ ULift.up ((show C(_, _) from ⟨f.hom, f.hom.cont⟩).comp h.down)
          map_add' := by intro h k; ext s; exact f.hom.map_add _ _
          map_smul' := by intro a h; ext s; exact f.hom.map_smul _ _ }
      naturality _ := by ext; rfl }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private instance : (sectionsFunctor R).Additive where
  map_add := by intros; ext S h; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionsCoordinates (I : Type u) (M : I → TopModuleCat.{u} R)
    (S : Profinite.{u}) :
    (sections R (TopModuleCat.of R (∀ i, M i))).obj (op S) ≃ₗ[
      (continuousMapRingPresheafOfUniverse.{u, u} R).obj (op S)]
        (∀ i, (sections R (M i)).obj (op S)) where
  toFun h i := ULift.up ((ContinuousMap.eval i).comp h.down)
  invFun h := ULift.up (ContinuousMap.pi (fun i ↦ (h i).down))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionsFanLimit (I : Type u) (M : I → TopModuleCat.{u} R) :
    IsLimit (Fan.mk ((sectionsFunctor R).obj (TopModuleCat.of R (∀ i, M i)))
      (fun i ↦ (sectionsFunctor R).map (TopModuleCat.ofHom (ContinuousLinearMap.proj i)))) := by
  letI (S : Profinite.{u}ᵒᵖ) := sectionsModule R (TopModuleCat.of R (∀ i, M i)) S
  exact Fan.IsLimit.mk _
    (fun c ↦
      { app S := ModuleCat.ofHom
          { toFun := fun h ↦ (sectionsCoordinates R I M S.unop).symm
              (fun i ↦ (c.proj i).app S h)
            map_add' := by
              intro h k
              simp only [map_add]
              rfl
            map_smul' := by
              intro a h
              simp only [map_smul]
              rfl }
        naturality q := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro h
          apply ULift.ext
          apply ContinuousMap.ext
          intro s
          funext i
          exact congrArg (fun h ↦ h.down s)
            (PresheafOfModules.naturality_apply (c.proj i) q h) })
    (by intro c i; ext; rfl)
    (by
      intro c f hf
      apply PresheafOfModules.hom_ext
      intro S
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro h
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      funext i
      exact congrArg (fun f ↦ ((f.app S h).down s)) (hf i))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionsRegular :
    sections R (TopModuleCat.of R R) ≅
      PresheafOfModules.unit (continuousMapRingPresheafOfUniverse.{u, u} R) := by
  letI (S : Profinite.{u}ᵒᵖ) := sectionsModule R (TopModuleCat.of R R) S
  exact PresheafOfModules.isoMk (fun S ↦
    { hom := ModuleCat.ofHom
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      inv := ModuleCat.ofHom
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl })
    (by intro S T q; ext; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Continuous sections form sectionwise modules, with the natural integer-tensor action
and the indicated finite-coordinate products.
Source: blueprint main-20261015 `lem-sfb-subfield-flat.proof.md`, first two sentences
(blueprint: lem-sfb-continuous-module-presheaf-coordinates).

Proof: steps 1--2 of the node compose the continuous addition, negation and action with
pairs of continuous functions. Evaluation proves the module axioms and compatibility
with precomposition. Steps 3--4 use `def-weil-pbc-module-tensor-product`: extend the
biadditive pairing to the integer tensor. Its naturality follows on pure tensors, which
generate. Steps 5--6 identify the integer unit and the pointwise multiplication and
verify the unit and associativity diagrams on pure and iterated pure tensors.
Step 7 recovers the sectionwise action by evaluation on pure tensors; tensor uniqueness
proves the two descriptions inverse (also stated separately below).
Step 8 postcomposes with continuous linear maps; evaluation proves linearity,
naturality, identities, composition, sums and the tensor-action square.
Steps 9--10 use the product-topology criterion: a map into a product is continuous
exactly when every coordinate is. The forward coordinate map and assembly map are
inverse, linear, and commute with restrictions. Step 11 assembles any cone coordinate
by coordinate, proving its factorization unique in `PresheafOfModules` itself.
Step 12 treats the empty family (all section groups are zero) and the regular module:
its sections and restrictions are those of B, and its tensor action is multiplication
by uniqueness of the integer tensor extension. No separation assumption on M is used.
-/
theorem continuousModulePresheaf_coordinates :
    ∃ (F : TopModuleCat.{u} R ⥤
      PresheafOfModules.{u + 1} (continuousMapRingPresheafOfUniverse.{u, u} R)),
    ∃ (e : ∀ (M : TopModuleCat.{u} R) (S : Profinite.{u}),
      (F.obj M).obj (op S) ≃+ C(S, M)),
    ∃ (β : ∀ (M : TopModuleCat.{u} R),
      (continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) ⊗
        (F.obj M).presheaf ⟶ (F.obj M).presheaf),
      F.Additive ∧
      (∀ (M : TopModuleCat.{u} R) (S T : Profinite.{u}) (q : T ⟶ S)
        (h : (F.obj M).obj (op S)),
        e M T ((F.obj M).map q.op h) = (e M S h).comp q.hom.hom) ∧
      (∀ (M : TopModuleCat.{u} R) (S : Profinite.{u})
        (a : C(S, R)) (h : (F.obj M).obj (op S)) (s : S),
        e M S ((ULift.up a : (continuousMapRingPresheafOfUniverse R).obj (op S)) • h) s =
          a s • e M S h s) ∧
      (∀ (M : TopModuleCat.{u} R) (S : Profinite.{u})
        (a : (continuousMapRingPresheafOfUniverse R).obj (op S))
        (h : (F.obj M).obj (op S)),
        (β M).app (op S) (TensorProduct.tmul ℤ a h) = a • h) ∧
      (∀ (M : TopModuleCat.{u} R)
        (g : (continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) ⊗
          (F.obj M).presheaf ⟶ (F.obj M).presheaf),
        (∀ (S : Profinite.{u}) (a : (continuousMapRingPresheafOfUniverse R).obj (op S))
          (h : (F.obj M).obj (op S)),
          g.app (op S) (TensorProduct.tmul ℤ a h) = a • h) → g = β M) ∧
      (∀ (M : TopModuleCat.{u} R),
        (η[continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab] ▷
          (F.obj M).presheaf) ≫ β M = (λ_ (F.obj M).presheaf).hom) ∧
      (∀ (M : TopModuleCat.{u} R),
        (μ[continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab] ▷
          (F.obj M).presheaf) ≫ β M =
        (α_ (continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab)
          (continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab)
          (F.obj M).presheaf).hom ≫
          ((continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) ◁ β M) ≫ β M) ∧
      (∀ (M N : TopModuleCat.{u} R) (f : M ⟶ N) (S : Profinite.{u})
        (h : (F.obj M).obj (op S)) (s : S),
        e N S ((F.map f).app (op S) h) s = f.hom (e M S h s)) ∧
      (∀ (M N : TopModuleCat.{u} R) (f : M ⟶ N),
        β M ≫ (PresheafOfModules.toPresheaf (continuousMapRingPresheafOfUniverse R)).map
          (F.map f) =
        ((continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) ◁
          (PresheafOfModules.toPresheaf (continuousMapRingPresheafOfUniverse R)).map
            (F.map f)) ≫ β N) ∧
      (∀ (I : Type u) [Finite I] (M : I → TopModuleCat.{u} R),
        ∃ (c : ∀ (S : Profinite.{u}),
          (F.obj (TopModuleCat.of R (∀ i, M i))).obj (op S) ≃ₗ[
            (continuousMapRingPresheafOfUniverse R).obj (op S)]
              (∀ i, (F.obj (M i)).obj (op S))),
          (∀ (S : Profinite.{u})
            (h : (F.obj (TopModuleCat.of R (∀ i, M i))).obj (op S)) (i : I) (s : S),
            e (M i) S (c S h i) s = e (TopModuleCat.of R (∀ i, M i)) S h s i) ∧
          (∀ (S : Profinite.{u}) (h : ∀ i, (F.obj (M i)).obj (op S)) (s : S) (i : I),
            e (TopModuleCat.of R (∀ i, M i)) S ((c S).symm h) s i = e (M i) S (h i) s) ∧
          (∀ (S T : Profinite.{u}) (q : T ⟶ S)
            (h : (F.obj (TopModuleCat.of R (∀ i, M i))).obj (op S)) (i : I),
            c T ((F.obj (TopModuleCat.of R (∀ i, M i))).map q.op h) i =
              (F.obj (M i)).map q.op (c S h i)) ∧
          (∀ (i : I) (S : Profinite.{u})
            (h : (F.obj (TopModuleCat.of R (∀ i, M i))).obj (op S)),
            (F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i))).app (op S) h =
              c S h i) ∧
          Nonempty (IsLimit (Fan.mk (F.obj (TopModuleCat.of R (∀ i, M i)))
            (fun i ↦ F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i)))))) ∧
      (∀ (I : Type u) [IsEmpty I] (M : I → TopModuleCat.{u} R),
        IsZero (F.obj (TopModuleCat.of R (∀ i, M i)))) ∧
      (∃ (r : F.obj (TopModuleCat.of R R) ≅
        PresheafOfModules.unit (continuousMapRingPresheafOfUniverse R)),
        (∀ (S : Profinite.{u}) (h : (F.obj (TopModuleCat.of R R)).obj (op S)),
          ((r.hom.app (op S)) h).down = e (TopModuleCat.of R R) S h) ∧
        β (TopModuleCat.of R R) ≫
          (PresheafOfModules.toPresheaf (continuousMapRingPresheafOfUniverse R)).map r.hom =
        ((continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) ◁
          (PresheafOfModules.toPresheaf (continuousMapRingPresheafOfUniverse R)).map r.hom) ≫
          μ[continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab]) := by
  refine ⟨sectionsFunctor R, fun M S ↦ AddEquiv.ulift,
    fun M ↦ sectionAction (sections R M), inferInstance, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro M g hg
    apply sectionAction_unique
    intro S
    exact hg S.unop
  · intro M; exact sectionAction_one _
  · intro M; exact sectionAction_mul _
  · intros; rfl
  · intros; exact sectionAction_natural _
  · intro I _ M
    refine ⟨sectionsCoordinates R I M, ?_, ?_, ?_, ?_, ⟨sectionsFanLimit R I M⟩⟩
    all_goals intros; rfl
  · intro I _ M
    apply (IsZero.iff_id_eq_zero _).mpr
    apply PresheafOfModules.hom_ext
    intro S
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    funext i
    exact isEmptyElim i
  · refine ⟨sectionsRegular R, ?_, ?_⟩
    · intros; rfl
    · apply NatTrans.ext
      funext S
      apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext'
      intro a h
      rfl

/-- Sectionwise module structures are equivalently natural tensor actions satisfying
unit and associativity: the equivalence uses exactly evaluation on pure tensors.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, continuous scalar action, expanded
in step 7 of the node (blueprint: lem-sfb-continuous-module-presheaf-coordinates).

Proof: from a module realization, biadditivity extends its action uniquely by
`def-weil-pbc-module-tensor-product`; evaluate on pure tensors to check both diagrams.
Conversely put a • x = β(a ⊗ x). Biadditivity gives both distributivities. The unit
diagram at 1 gives one_smul, and the associativity diagram gives mul_smul. Naturality
of β gives semilinearity of restrictions. These are precisely the fields of a
`PresheafOfModules` with underlying presheaf P. The two constructions recover the
action on pure tensors and hence recover β by tensor generation.
-/
theorem continuousModulePresheaf_action_iff
    (P : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
    (β : (continuousMapRingPresheafOfUniverse.{u, u} R ⋙ forget₂ RingCat Ab) ⊗ P ⟶ P) :
    ((η[continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab] ▷ P) ≫ β =
      (λ_ P).hom ∧
      (μ[continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab] ▷ P) ≫ β =
        (α_ (continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab)
          (continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) P).hom ≫
          ((continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) ◁ β) ≫ β) ↔
    ∃ (Q : PresheafOfModules.{u + 1} (continuousMapRingPresheafOfUniverse R))
      (e : Q.presheaf ≅ P),
      ∀ (S : Profinite.{u}) (a : (continuousMapRingPresheafOfUniverse R).obj (op S))
        (h : Q.obj (op S)),
        e.hom.app (op S) (a • h) = β.app (op S)
          (TensorProduct.tmul ℤ a (e.hom.app (op S) h)) := by
  constructor
  · rintro ⟨hunit, hassoc⟩
    let B := continuousMapRingPresheafOfUniverse R
    let (S : Profinite.{u}ᵒᵖ) : Module (B.obj S) (P.obj S) :=
      { smul := fun a h ↦ β.app S (TensorProduct.tmul ℤ a h)
        one_smul := by
          intro h
          have hh := ConcreteCategory.congr_hom (congr_app hunit S)
            (TensorProduct.tmul ℤ (ULift.up (1 : ℤ)) h)
          change β.app S (TensorProduct.tmul ℤ ((1 : ℤ) : B.obj S) h) = (1 : ℤ) • h
            at hh
          change β.app S (TensorProduct.tmul ℤ (1 : B.obj S) h) = h
          simpa only [Int.cast_one, one_smul] using hh
        mul_smul := by
          intro a b h
          exact ConcreteCategory.congr_hom (congr_app hassoc S)
            (TensorProduct.tmul ℤ (TensorProduct.tmul ℤ a b) h)
        smul_zero := by
          intro a
          change β.app S (TensorProduct.tmul ℤ a 0) = 0
          simp
        smul_add := by
          intro a h k
          change β.app S (TensorProduct.tmul ℤ a (h + k)) =
            β.app S (TensorProduct.tmul ℤ a h) + β.app S (TensorProduct.tmul ℤ a k)
          rw [TensorProduct.tmul_add, map_add]
        zero_smul := by
          intro h
          change β.app S (TensorProduct.tmul ℤ 0 h) = 0
          simp
        add_smul := by
          intro a b h
          change β.app S (TensorProduct.tmul ℤ (a + b) h) =
            β.app S (TensorProduct.tmul ℤ a h) + β.app S (TensorProduct.tmul ℤ b h)
          rw [TensorProduct.add_tmul, map_add] }
    let Q : PresheafOfModules.{u + 1} B := PresheafOfModules.ofPresheaf P (by
      intro S T q a h
      exact (ConcreteCategory.congr_hom (β.naturality q)
        (TensorProduct.tmul ℤ a h)).symm)
    exact ⟨Q, Iso.refl _, fun _ _ _ ↦ rfl⟩
  · rintro ⟨Q, e, he⟩
    have he' (S : Profinite.{u}ᵒᵖ)
        (a : (continuousMapRingPresheafOfUniverse R).obj S) (h : Q.obj S) :
        β.app S (TensorProduct.tmul ℤ a (e.hom.app S h)) = e.hom.app S (a • h) :=
      (he S.unop a h).symm
    constructor
    · apply NatTrans.ext
      funext S
      apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext'
      intro n h
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app S)).2 h
      change β.app S (TensorProduct.tmul ℤ (n.down :
        (continuousMapRingPresheafOfUniverse R).obj S) (e.hom.app S x)) =
          n.down • e.hom.app S x
      rw [he', Int.cast_smul_eq_zsmul, map_zsmul]
    · apply NatTrans.ext
      funext S
      apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext_threefold
        (M := (continuousMapRingPresheafOfUniverse R).obj S)
        (N := (continuousMapRingPresheafOfUniverse R).obj S) (P := P.obj S)
      intro a b h
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app S)).2 h
      change β.app S (TensorProduct.tmul ℤ ((a : (continuousMapRingPresheafOfUniverse R).obj S) *
        (b : (continuousMapRingPresheafOfUniverse R).obj S))
        (e.hom.app S x)) =
        β.app S (TensorProduct.tmul ℤ a
          (β.app S (TensorProduct.tmul ℤ b (e.hom.app S x))))
      rw [he', he', he', mul_smul]

end Profinite
