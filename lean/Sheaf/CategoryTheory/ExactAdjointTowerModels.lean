/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.ExactProductsRoosComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-! # Simultaneous exact-adjoint tower models

Source: Stacks Project, Cohomology on Sites, Tag 0A07, first proof; Tags 0941,
079P, 08BJ, 0BK6, 070K and 070Y
(blueprint: lem-weil-pbc-exact-adjoint-tower-models).

The structures package the choices and assertions of the statement. In particular,
they do not choose any replacement or any derived functor from a bare existence axiom.
The positive tower level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u vA vB uA uB w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Functor Opposite

namespace CategoryTheory.ExactAdjointTowerModels

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Applying a functor levelwise to a strict tower complex.
Source: Stacks Tag 0A07, tower-topos square
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
abbrev tower (G : A ⥤ B) [G.Additive] :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- A total right derived functor with its universal unit, computed on K-injectives.
This only bundles the conclusion of the recorded K-injective total-derivation lemma.
Source: Stacks Tags 070K and 070Y
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure DerivedModel (H : CochainComplex A ℤ ⥤ CochainComplex B ℤ) where
  functor : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B
  unit : H ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  on_injectives : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)

variable [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- The negative-difference fibre coordinates, ordered as (y,x).
Source: Stacks Tag 0941 and the explicit sign calculation in the node
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
def negativeCoordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (ExactProductsRoos.fibre.obj X).X (p + 1) ≅
      (roosP X).X p ⊞ (roosP X).X (p + 1) :=
  (CochainComplex.mappingCone (-roosU X)).shiftFunctorObjXIso
      (-1) (p + 1) p (add_neg_cancel_right p 1).symm ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod (-roosU X) p (p + 1) rfl ≪≫
      biprod.braiding _ _

/-- The signed, unit-normalized Roos conclusions for one of the two categories.
The sign isomorphism and both comparisons are natural on all strict tower complexes.
The final fields transport the rotated cone triangle along the actual map j.
Source: Stacks Tag 0941, including the sign convention of the strict Roos model
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure NormalizedRoos (L : DerivedModel (roosLimitFunctor (A := A))) where
  sign : ExactProductsRoos.fibre (B := A) ≅ roosF
  sign_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (sign.hom.app X).f (p + 1) ≫ (roosχ X p).hom =
      (negativeCoordinates X p).hom ≫ biprod.map (-𝟙 _) (𝟙 _)
  negative : ExactProductsRoos.fibre ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.functor
  ordinary : ExactProductsRoos.ordinary (B := A) ≅ roosLimitFunctor
  ordinary_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) (p : ℤ),
    ((ordinary.hom.app X) ≫ limit.π X.asFunctor (op n)).f p =
      limit.π (X.X p) (op n)
  inclusion_sign : ExactProductsRoos.comparison ≫ sign.hom =
    ordinary.hom ≫ roosInclusion
  negative_normalization :
    Functor.whiskerRight ExactProductsRoos.comparison DerivedCategory.Q ≫ negative.hom =
      Functor.whiskerRight ordinary.hom DerivedCategory.Q ≫ L.unit
  comparison : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.functor
  comparison_sign : comparison =
    isoWhiskerRight sign.symm DerivedCategory.Q ≪≫ negative
  normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    DerivedCategory.Q.map (roosι X) ≫ comparison.hom.app X = L.unit.app X
  quasiIso : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) → QuasiIso (roosι I)
  triangle : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) →
    ∃ e : DerivedCategory.Q.obj (limit I.asFunctor) ≅
        DerivedCategory.Q.obj (roosF.obj I),
      e.hom = DerivedCategory.Q.map (roosι I) ∧
      Triangle.mk
        (DerivedCategory.Q.map (roosι I ≫ roosProj I))
        (DerivedCategory.Q.map (roosU I))
        (DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU I)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ≫
          e.inv⟦(1 : ℤ)⟧') ∈ distTriang (DerivedCategory.{w} A)
  unit_triangle : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) →
    Triangle.mk
      ((comparison.inv.app I) ≫ DerivedCategory.Q.map (roosProj I))
      (DerivedCategory.Q.map (roosU I))
      (DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU I)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ≫
        (comparison.hom.app I)⟦(1 : ℤ)⟧') ∈ distTriang (DerivedCategory.{w} A)

variable [HasLimitsOfShape ℕᵒᵖ B] [HasCountableProducts B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- All simultaneous models and their canonical normalizations. The derived models
are choices with universal units; c and beta are fixed by their projection equations.
No exact-product assumption is used except in the last field.
Source: Stacks Tag 0A07, first proof, and Tags 0BK6 and 0941
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure Models (G : A ⥤ B) [G.Additive] where
  direct : DerivedModel (G.mapHomologicalComplex (.up ℤ))
  towerDirect : DerivedModel (tower G)
  sourceLimit : DerivedModel (roosLimitFunctor (A := A))
  targetLimit : DerivedModel (roosLimitFunctor (A := B))
  resolution : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I),
      QuasiIso q ∧ I.IsKInjective ∧ ∀ r : ℤ, Injective (I.X r)
  kInjective : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      ((tower G).obj I).IsKInjective ∧
      (∀ r : ℤ, Injective (((tower G).obj I).X r)) ∧
      (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n)) ∧
        CochainComplex.IsKInjective
          ((G.mapHomologicalComplex (.up ℤ)).obj (I.asFunctor.obj (op n)))) ∧
      CochainComplex.IsKInjective (limit I.asFunctor) ∧
      CochainComplex.IsKInjective (limit ((tower G).obj I).asFunctor) ∧
      (roosP I).IsKInjective ∧ (roosP ((tower G).obj I)).IsKInjective ∧
      CochainComplex.IsKInjective
        ((G.mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor)) ∧
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj (roosP I))
  computes : ∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I),
    QuasiIso q → I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      (∃ e : DerivedCategory.Q.obj ((tower G).obj I) ≅
          towerDirect.functor.obj (DerivedCategory.Q.obj X),
        e.hom ≫ towerDirect.functor.map (DerivedCategory.Q.map q) =
          towerDirect.unit.app I) ∧
      (∃ e : DerivedCategory.Q.obj (limit I.asFunctor) ≅
          sourceLimit.functor.obj (DerivedCategory.Q.obj X),
        e.hom ≫ sourceLimit.functor.map (DerivedCategory.Q.map q) =
          sourceLimit.unit.app I) ∧
      (∃ e : DerivedCategory.Q.obj (limit ((tower G).obj I).asFunctor) ≅
          targetLimit.functor.obj (towerDirect.functor.obj (DerivedCategory.Q.obj X)),
        e.hom ≫ targetLimit.functor.map (towerDirect.functor.map (DerivedCategory.Q.map q)) =
          targetLimit.unit.app ((tower G).obj I) ≫
            targetLimit.functor.map (towerDirect.unit.app I)) ∧
      (∃ e : DerivedCategory.Q.obj
            ((G.mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor)) ≅
          direct.functor.obj (sourceLimit.functor.obj (DerivedCategory.Q.obj X)),
        e.hom ≫ direct.functor.map (sourceLimit.functor.map (DerivedCategory.Q.map q)) =
          direct.unit.app (limit I.asFunctor) ≫
            direct.functor.map (sourceLimit.unit.app I))
  products : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (limit.cone (Discrete.functor
          (fun n : ℕ ↦ ((tower G).obj I).asFunctor.obj (op n))))))
  c : ExactProductsRoos.product ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    tower G ⋙ ExactProductsRoos.product
  beta : roosLimitFunctor ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    tower G ⋙ roosLimitFunctor
  c_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    c.hom.app X ≫ Pi.π (fun k : ℕ ↦ ((tower G).obj X).asFunctor.obj (op k)) n =
      (G.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n)
  beta_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    beta.hom.app X ≫ limit.π ((tower G).obj X).asFunctor (op n) =
      (G.mapHomologicalComplex (.up ℤ)).map (limit.π X.asFunctor (op n))
  shift_commutes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (G.mapHomologicalComplex (.up ℤ)).map
        (towerProductShift (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
        c.hom.app X =
      c.hom.app X ≫ towerProductShift
        (fun n : ℕ ↦ ((tower G).obj X).asFunctor.map (homOfLE (Nat.le_succ n)).op)
  difference_commutes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (G.mapHomologicalComplex (.up ℤ)).map (roosU X) ≫ c.hom.app X =
      c.hom.app X ≫ roosU ((tower G).obj X)
  derived_product_components : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) → ∀ n : ℕ,
      DerivedCategory.Q.map (c.hom.app I) ≫
          DerivedCategory.Q.map
            (Pi.π (fun k : ℕ ↦ ((tower G).obj I).asFunctor.obj (op k)) n) ≫
          direct.unit.app (I.asFunctor.obj (op n)) =
        direct.unit.app (roosP I) ≫ direct.functor.map
          (DerivedCategory.Q.map (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n))
  localized_maps : ∀ (I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
    I.IsKInjective → I'.IsKInjective →
    (∀ a : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I',
      ∃ f : I ⟶ I', DerivedCategory.Q.map f = a) ∧
    (∀ (f g : I ⟶ I'), DerivedCategory.Q.map f = DerivedCategory.Q.map g →
      DerivedCategory.Q.map (roosPmap f) = DerivedCategory.Q.map (roosPmap g) ∧
      DerivedCategory.Q.map (roosLimitFunctor.map f) =
        DerivedCategory.Q.map (roosLimitFunctor.map g) ∧
      DerivedCategory.Q.map ((ExactProductsRoos.product ⋙
        G.mapHomologicalComplex (.up ℤ)).map f) =
        DerivedCategory.Q.map ((ExactProductsRoos.product ⋙
          G.mapHomologicalComplex (.up ℤ)).map g) ∧
      DerivedCategory.Q.map ((tower G ⋙ ExactProductsRoos.product).map f) =
        DerivedCategory.Q.map ((tower G ⋙ ExactProductsRoos.product).map g) ∧
      DerivedCategory.Q.map ((roosLimitFunctor ⋙
        G.mapHomologicalComplex (.up ℤ)).map f) =
        DerivedCategory.Q.map ((roosLimitFunctor ⋙
          G.mapHomologicalComplex (.up ℤ)).map g) ∧
      DerivedCategory.Q.map ((tower G ⋙ roosLimitFunctor).map f) =
        DerivedCategory.Q.map ((tower G ⋙ roosLimitFunctor).map g))
  exact_products : HasExactLimitsOfShape (Discrete ℕ) A →
    HasExactLimitsOfShape (Discrete ℕ) B →
      Nonempty (NormalizedRoos sourceLimit) ∧ Nonempty (NormalizedRoos targetLimit)

omit [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasLimitsOfShape ℕᵒᵖ B]
  [HasCountableProducts B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)] in
private theorem derived_exists [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ B) [G.Additive] :
    Nonempty (DerivedModel (G.mapHomologicalComplex (.up ℤ))) := by
  let H := G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w}
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives H := by
    intro X Y f hf
    have : X.obj.IsKInjective := X.property
    have : Y.obj.IsKInjective := Y.property
    have : QuasiIso f.hom := hf
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp inferInstance
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f.hom) := by
      rw [← he]
      exact (G.mapHomotopyEquiv e).quasiIso_hom
    change IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f.hom))
    infer_instance
  have := h.hasPointwiseRightDerivedFunctor
  refine ⟨⟨H.totalRightDerived DerivedCategory.Q W,
    H.totalRightDerivedUnit DerivedCategory.Q W, inferInstance, ?_⟩⟩
  intro I hI
  exact h.isIso_of_isRightDerivedFunctor _ (CochainComplex.KInjectives.mk I)

private def ordinaryIso :
    ExactProductsRoos.ordinary (B := A) ≅ roosLimitFunctor :=
  (NatIso.ofComponents (fun X ↦
    limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩) (by
    intro X Y f
    apply (HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor).hom_ext
    intro n
    ext p
    have hπ (Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩).hom.f p ≫
            limit.π (Z.X p) n = (limit.π Z.asFunctor n).f p := by
      simpa only [HomologicalComplex.comp_f,
        HomologicalComplex.coneOfHasLimitEval_π_app_f, HomologicalComplex.asFunctor,
        HomologicalComplex.eval, Functor.comp] using
        congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
          (limit.isoLimitCone_hom_π
            ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
    have hm := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n)
    dsimp at hπ hm ⊢
    simp only [HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp] at hπ hm ⊢
    calc
      _ = (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).f p ≫
          (limit.π Y.asFunctor n).f p := by
        rw [Category.assoc, hπ Y]
        rfl
      _ = (limit.π X.asFunctor n).f p ≫ (f.f p).app n := hm
      _ = _ := by
        rw [Category.assoc]
        change _ = _ ≫ limMap (f.f p) ≫ limit.π (Y.X p) n
        rw [limMap_π, ← Category.assoc, hπ X]
        rfl)).symm

omit [HasDerivedCategory A] [HasCountableProducts A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem ordinaryIso_components (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (n : ℕᵒᵖ) (p : ℤ) :
    (ordinaryIso.hom.app X ≫ limit.π X.asFunctor n).f p =
      limit.π (X.X p) n := by
  have h := congrArg (fun f ↦ f.f p)
    (limit.isoLimitCone_inv_π
      ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
        HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩ n)
  exact h

private theorem limit_derived_exists [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] :
    Nonempty (DerivedModel (roosLimitFunctor (A := A))) := by
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨L⟩ := derived_exists (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  let η := Functor.whiskerRight ordinaryIso.inv DerivedCategory.Q ≫ L.unit
  refine ⟨⟨L.functor, η, ?_, ?_⟩⟩
  · have := L.universal
    apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).2
    apply (Functor.isLeftKanExtension_iff_of_iso₂ η L.unit
      (isoWhiskerRight ordinaryIso.symm DerivedCategory.Q)
      (Iso.refl L.functor) (by simp [η])).2
    exact (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).1 L.universal
  · intro I hI
    have := L.on_injectives I hI
    dsimp [η]
    infer_instance

private def productIso (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) (G.mapHomologicalComplex (.up ℤ))] :
    ExactProductsRoos.product ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      tower G ⋙ ExactProductsRoos.product :=
  NatIso.ofComponents (fun X ↦
    asIso (piComparison (G.mapHomologicalComplex (.up ℤ))
      (fun n : ℕ ↦ X.asFunctor.obj (op n)))) (by
    intro X Y f
    let H := G.mapHomologicalComplex (.up ℤ)
    change H.map (Limits.Pi.map
        (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
          (op n))) ≫ piComparison H (fun n : ℕ ↦ Y.asFunctor.obj (op n)) =
      piComparison H (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫
        Limits.Pi.map (f := fun n : ℕ ↦ H.obj (X.asFunctor.obj (op n)))
          (g := fun n : ℕ ↦ H.obj (Y.asFunctor.obj (op n)))
          (fun n : ℕ ↦ H.map
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)))
    apply Pi.hom_ext
    intro n
    dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
      piComparison_comp_π_assoc, ← H.map_comp])

private def limitIso (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape ℕᵒᵖ (G.mapHomologicalComplex (.up ℤ))] :
    roosLimitFunctor ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      tower G ⋙ roosLimitFunctor :=
  NatIso.ofComponents (fun X ↦
    preservesLimitIso (G.mapHomologicalComplex (.up ℤ)) X.asFunctor) (by
    intro X Y f
    exact (preservesLimitNatIso (G.mapHomologicalComplex (.up ℤ))).hom.naturality
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f))

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)] in
private theorem productIso_shift (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) (G.mapHomologicalComplex (.up ℤ))]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (towerProductShift (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
        (productIso G).hom.app X =
      (productIso G).hom.app X ≫ towerProductShift
        (fun n : ℕ ↦ ((tower G).obj X).asFunctor.map (homOfLE (Nat.le_succ n)).op) := by
  let H := G.mapHomologicalComplex (.up ℤ)
  change H.map (towerProductShift
      (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
      piComparison H (fun n : ℕ ↦ X.asFunctor.obj (op n)) =
    piComparison H (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫
      towerProductShift (K := fun n : ℕ ↦ H.obj (X.asFunctor.obj (op n)))
        (fun n : ℕ ↦ H.map (X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π, towerProductShift, Pi.lift_π,
    piComparison_comp_π_assoc, ← H.map_comp]

omit [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasLimitsOfShape ℕᵒᵖ B]
  [HasCountableProducts B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)] in
private theorem computes_one
    {H : CochainComplex A ℤ ⥤ CochainComplex B ℤ}
    (M : DerivedModel H) {X I : CochainComplex A ℤ} (q : X ⟶ I)
    [QuasiIso q] [I.IsKInjective] :
    ∃ e : DerivedCategory.Q.obj (H.obj I) ≅ M.functor.obj (DerivedCategory.Q.obj X),
      e.hom ≫ M.functor.map (DerivedCategory.Q.map q) = M.unit.app I := by
  have := M.on_injectives I inferInstance
  exact ⟨asIso (M.unit.app I) ≪≫ (M.functor.mapIso (asIso (DerivedCategory.Q.map q))).symm,
    by simp⟩

omit [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem products_compute (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] :
    (roosP I).IsKInjective ∧
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) := by
  have (n : ℕ) : CochainComplex.IsKInjective (I.asFunctor.obj (op n)) :=
    tower_evaluation_isKInjective A I (op n)
  obtain ⟨hK, ⟨hD⟩⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit
    (fun n : ℕ ↦ I.asFunctor.obj (op n))
  let e := limit.isoLimitCone
    ⟨HomologicalComplex.coneOfHasLimitEval
      (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n))),
        HomologicalComplex.isLimitConeOfHasLimitEval _⟩
  refine ⟨?_, ⟨?_⟩⟩
  · have := hK
    exact CochainComplex.isKInjective_of_iso e.symm
  · exact hD.ofIsoLimit ((Cone.functoriality _ DerivedCategory.Q).mapIso
      (Cone.ext e.symm (by intro n; simp [e])))

private def signCone (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex.mappingCone (-roosU X) ≅ CochainComplex.mappingCone (roosU X) where
  hom := CochainComplex.mappingCone.map _ _ (𝟙 _) (-𝟙 _) (by simp)
  inv := CochainComplex.mappingCone.map _ _ (𝟙 _) (-𝟙 _) (by simp)
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    exact CochainComplex.mappingCone.map_id _
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    exact CochainComplex.mappingCone.map_id _

omit [HasDerivedCategory A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem sign_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (((shiftFunctor _ (-1 : ℤ)).mapIso (signCone X)).hom).f (p + 1) ≫
        (roosχ X p).hom =
      (negativeCoordinates X p).hom ≫ biprod.map (-𝟙 _) (𝟙 _) := by
  dsimp only [Functor.mapIso_hom, roosχ, negativeCoordinates, Iso.trans_hom, signCone]
  rw [CochainComplex.shiftFunctor_map_f']
  simp only [Category.assoc, CochainComplex.shiftFunctorObjXIso]
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality]
  simp only [Category.assoc]
  congr 1
  apply CochainComplex.mappingCone.ext_from (-roosU X) (p + 1) p rfl
  · change (CochainComplex.mappingCone.inl (-roosU X)).v (p + 1) p (by omega) ≫
        (CochainComplex.mappingCone.map (-roosU X) (roosU X)
          (𝟙 _) (-𝟙 _) (by simp)).f p ≫ _ = _
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
    simp only [CochainComplex.mappingCone.inl,
      CochainComplex.HomComplex.Cochain.mk_v, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    apply biprod.hom_ext <;> simp
  · rw [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc]
    simp only [HomologicalComplex.comp_f, CochainComplex.mappingCone.inr, Category.assoc]
    apply biprod.hom_ext <;> simp

omit [HasDerivedCategory A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasCountableProducts A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem arrowMap_eq_coneMap {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (α : Arrow.mk f ⟶ Arrow.mk g) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α =
      CochainComplex.mappingCone.map f g α.left α.right α.w.symm := by
  ext n : 1
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n + 1) n rfl
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inlX_desc_f,
      Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero]
    change _ = (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _
        (n + 1) (n + 1) n (by omega) (by omega)]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ (n + 1) n rfl]
    simp only [CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v]
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrX_desc_f]
    change _ = (CochainComplex.mappingCone.inr f).f n ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl

private def signIso : ExactProductsRoos.fibre (B := A) ≅ roosF :=
  NatIso.ofComponents (fun X ↦ (shiftFunctor _ (-1 : ℤ)).mapIso (signCone X)) (by
    intro X Y f
    change (shiftFunctor _ (-1 : ℤ)).map _ ≫
        (shiftFunctor _ (-1 : ℤ)).map (signCone Y).hom =
      (shiftFunctor _ (-1 : ℤ)).map (signCone X).hom ≫
        (shiftFunctor _ (-1 : ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [arrowMap_eq_coneMap]
    dsimp only [signCone, ExactProductsRoos.arrowMap, roosConeFunctor]
    rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
    simp only [Category.comp_id, Category.id_comp,
      Preadditive.comp_neg, Preadditive.neg_comp])

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem inclusion_sign : ExactProductsRoos.comparison ≫ signIso.hom =
    ordinaryIso.hom ≫ roosInclusion (A := A) := by
  apply NatTrans.ext
  funext X
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change ((ExactProductsRoos.comparison ≫ signIso.hom).app X).f (p + 1) =
    ((ordinaryIso.hom ≫ roosInclusion).app X).f (p + 1)
  apply (cancel_mono (roosχ X p).hom).1
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    Category.assoc, roosInclusion, signIso, NatIso.ofComponents_hom_app, sign_coordinates]
  change (ExactProductsRoos.comparisonApp X).f (p + 1) ≫
      (negativeCoordinates X p).hom ≫ biprod.map (-𝟙 _) (𝟙 _) = _
  have hc : (ExactProductsRoos.comparisonApp X).f (p + 1) ≫
      (negativeCoordinates X p).hom =
      biprod.lift 0 ((ExactProductsRoos.inclusion.app X).f (p + 1)) := by
    apply biprod.hom_ext
    · have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
          HomologicalComplex.homotopyCofiber.sndX (-roosU X) r =
            (HomologicalComplex.homotopyCofiber.XIsoBiprod (-roosU X) r q hq).hom ≫
              biprod.snd := by
        obtain rfl := (ComplexShape.up ℤ).next_eq' hq
        dsimp only [HomologicalComplex.homotopyCofiber.sndX]
        rw [dif_pos hq]
      have h := CochainComplex.mappingCocone.lift_f_snd_v (-roosU X)
        (ExactProductsRoos.inclusion.app X) 0
        (ExactProductsRoos.comparison_condition X) (p + 1) p (by omega)
      simpa [ExactProductsRoos.comparisonApp, negativeCoordinates,
        CochainComplex.mappingCocone.snd, CochainComplex.HomComplex.Cochain.leftShift_v,
        Category.assoc, show Int.negOnePow 2 = 1 by rfl,
        CochainComplex.mappingCone.snd, hs p (p + 1) rfl] using h
    · simp only [Category.assoc, biprod.lift_snd]
      have hp : (CochainComplex.mappingCocone.fst (-roosU X)).f (p + 1) =
          (negativeCoordinates X p).hom ≫ biprod.snd := by
        simp [negativeCoordinates, CochainComplex.mappingCocone.fst,
          CochainComplex.HomComplex.Cocycle.homOf,
          CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.fst,
          HomologicalComplex.homotopyCofiber.fstX]
      rw [← hp]
      exact CochainComplex.mappingCocone.lift_f_fst_f _ _ _ _ _
  rw [← Category.assoc, hc, roosι_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.map_snd, Category.comp_id,
      biprod.lift_snd]
    change (ExactProductsRoos.inclusion.app X).f (p + 1) =
      (ordinaryIso.hom.app X).f (p + 1) ≫
        (Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)
    have hprod := isLimitFanMkObjOfIsLimit
      (HomologicalComplex.eval A (.up ℤ) (p + 1))
      (fun n : ℕ ↦ X.asFunctor.obj (op n))
      (Pi.π _) (productIsProduct _)
    apply hprod.hom_ext
    intro ⟨n⟩
    change (ExactProductsRoos.inclusion.app X).f (p + 1) ≫
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1) =
      ((ordinaryIso.hom.app X).f (p + 1) ≫
        (Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) ≫
          (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)
    rw [← HomologicalComplex.comp_f, Pi.lift_π]
    rw [Category.assoc, ← HomologicalComplex.comp_f, Pi.lift_π,
      ← HomologicalComplex.comp_f, ordinaryIso_components]
    rfl

private theorem normalized_exists
    [IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A)]
    [HasExactLimitsOfShape (Discrete ℕ) A]
    (L : DerivedModel (roosLimitFunctor (A := A))) : Nonempty (NormalizedRoos L) := by
  let η := Functor.whiskerRight ordinaryIso.hom DerivedCategory.Q ≫ L.unit
  have hη (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
      IsIso (η.app I) := by
    have := L.on_injectives I hI
    dsimp [η]
    infer_instance
  obtain ⟨negative, hn⟩ := ExactProductsRoos.comparisonIso L.functor η hη
  let κ := isoWhiskerRight signIso.symm DerivedCategory.Q ≪≫ negative
  have hnκ : Functor.whiskerRight roosInclusion DerivedCategory.Q ≫ κ.hom = L.unit := by
    apply (cancel_epi (Functor.whiskerRight ordinaryIso.hom DerivedCategory.Q)).1
    rw [← Category.assoc, ← Functor.whiskerRight_comp, ← inclusion_sign]
    dsimp only [κ, Iso.trans_hom, isoWhiskerRight_hom, Iso.symm_hom]
    rw [Functor.whiskerRight_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (Functor.whiskerRight signIso.hom DerivedCategory.Q),
      ← Functor.whiskerRight_comp, signIso.hom_inv_id]
    simpa only [Functor.whiskerRight_id', Category.id_comp] using hn
  have hnorm (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (roosι X) ≫ κ.hom.app X = L.unit.app X :=
    NatTrans.congr_app hnκ X
  have hq (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
      QuasiIso (roosι I) := by
    have := L.on_injectives I hI
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).1
    have : IsIso (DerivedCategory.Q.map (roosι I) ≫ κ.hom.app I) := by
      rw [hnorm]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (κ.hom.app I)
  refine ⟨{ sign := signIso
            sign_coordinates := sign_coordinates
            negative := negative
            ordinary := ordinaryIso
            ordinary_components := fun X n p ↦ ordinaryIso_components X (op n) p
            inclusion_sign := inclusion_sign
            negative_normalization := hn
            comparison := κ
            comparison_sign := rfl
            normalization := hnorm
            quasiIso := fun I hI _ ↦ hq I hI
            triangle := ?_
            unit_triangle := ?_ }⟩
  · intro I hI _
    have := hq I hI
    let e := asIso (DerivedCategory.Q.map (roosι I))
    refine ⟨e, rfl, ?_⟩
    apply isomorphic_distinguished _
      (DerivedCategory.mappingCocone_triangle_distinguished (roosU I))
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · change DerivedCategory.Q.map (roosι I ≫ roosProj I) ≫ 𝟙 _ =
        e.hom ≫ DerivedCategory.Q.map (CochainComplex.mappingCocone.fst (roosU I))
      simp only [Category.comp_id, Functor.map_comp]
      rfl
    · change DerivedCategory.Q.map (roosU I) ≫ 𝟙 _ = 𝟙 _ ≫
        DerivedCategory.Q.map (roosU I)
      simp only [Category.comp_id, Category.id_comp]
    · change (_ ≫ _ ≫ e.inv⟦(1 : ℤ)⟧') ≫ e.hom⟦(1 : ℤ)⟧' = 𝟙 _ ≫ _
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id, Category.comp_id, Category.id_comp]
      rfl
  · intro I _ _
    apply isomorphic_distinguished _
      (DerivedCategory.mappingCocone_triangle_distinguished (roosU I))
    refine Triangle.isoMk _ _ (κ.app I).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · change (κ.inv.app I ≫ DerivedCategory.Q.map (roosProj I)) ≫ 𝟙 _ =
        κ.inv.app I ≫ DerivedCategory.Q.map (CochainComplex.mappingCocone.fst (roosU I))
      rw [Category.comp_id]
      rfl
    · change DerivedCategory.Q.map (roosU I) ≫ 𝟙 _ = 𝟙 _ ≫
        DerivedCategory.Q.map (roosU I)
      simp only [Category.comp_id, Category.id_comp]
    · change (_ ≫ _ ≫ κ.hom.app I⟦(1 : ℤ)⟧') ≫ κ.inv.app I⟦(1 : ℤ)⟧' = 𝟙 _ ≫ _
      simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
        Functor.map_id, Category.comp_id, Category.id_comp]
      rfl

omit [HasDerivedCategory A] [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A] in
private theorem q_surjective (I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I'.IsKInjective] (a : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I') :
    ∃ f : I ⟶ I', DerivedCategory.Q.map f = a := by
  let π := HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ A)
  obtain ⟨b, hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (π.obj I) I').surjective
    (e.hom.app I ≫ a ≫ e.inv.app I')
  obtain ⟨f, rfl⟩ := π.map_surjective b
  refine ⟨f, ?_⟩
  apply (cancel_epi (e.hom.app I)).1
  rw [← e.hom.naturality]
  change DerivedCategory.Qh.map (π.map f) ≫ e.hom.app I' = _
  rw [hb]
  simp

private def homotopy_of_q_eq {I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    [I'.IsKInjective] {f g : I ⟶ I'} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Homotopy f g := by
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ I').injective
  let e := DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ A)
  apply (cancel_mono (e.hom.app I')).1
  change (HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).map f ≫ e.hom.app I' =
    (HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).map g ≫ e.hom.app I'
  rw [e.hom.naturality, e.hom.naturality, h]

private def product_homotopy {I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : I ⟶ I'} (h : Homotopy f g) : Homotopy (roosPmap f) (roosPmap g) := by
  apply HomotopyCategory.homotopyOfFan (productIsProduct _)
  intro n
  change Homotopy
    (roosPmap f ≫ Pi.π (fun k : ℕ ↦ I'.asFunctor.obj (op k)) n)
    (roosPmap g ≫ Pi.π (fun k : ℕ ↦ I'.asFunctor.obj (op k)) n)
  simp only [roosPmap, Pi.map_π]
  change Homotopy
    (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n ≫
      (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).map f)
    (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n ≫
      (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).map g)
  exact
    (((evaluation ℕᵒᵖ A).obj (op n)).mapHomotopy h).compLeft
      (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n)

private def limit_homotopy {I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : I ⟶ I'} (h : Homotopy f g) :
    Homotopy (roosLimitFunctor.map f) (roosLimitFunctor.map g) := by
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hn (k : I ⟶ I') :
      ordinaryIso.inv.app I ≫ ExactProductsRoos.ordinary.map k ≫ ordinaryIso.hom.app I' =
        roosLimitFunctor.map k := by
    rw [ordinaryIso.hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [← hn f, ← hn g]
  simpa only [Category.assoc] using
    (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopy h).compLeft
      (ordinaryIso.inv.app I)).compRight (ordinaryIso.hom.app I')

/-- The simultaneous tower, product and inverse-limit models for an exact adjoint pair.
Source: Stacks Project, Tag 0A07, first proof via the tower-topos square;
Tags 079P, 08BJ, 0BK6, 070K, 070Y and 0941
(blueprint: lem-weil-pbc-exact-adjoint-tower-models).

Proof plan:
1. Module sheaves and their small diagram categories are Grothendieck abelian
   (lem-weil-pbc-ring-sheaves-grothendieck,
   lem-weil-pbc-small-module-diagrams-grothendieck). Apply
   lem-pur-kinjective-degreewise-existence to get degreewise-injective resolutions.
2. Products and ordinary limits exist sectionwise; compatible families glue
   componentwise. Differentials are induced by their universal properties.
3. The pointwise adjunction has exact left adjoint by
   lem-weil-tower-category-levelwise-abelian. Apply
   lem-weil-pbc-right-adjoint-preserves-kinjective and
   lem-sp-right-adjoint-preserves-injectives to its right adjoint.
4. Evaluation preserves K-injectives (lem-weil-tower-evaluation-kinjective).
   The exact constant-tower left adjoint makes limit preserve K-injectives.
   Apply the same exact-adjoint criterion to G after taking limits.
5. Apply lem-pc-ringed-space-product-kinjective to both level families. It also
   supplies the localized product universal properties. Apply G once more.
6. Use the K-injective derivability structure for G, its tower functor and both
   limits. Additive functors send homotopy equivalences to homotopy equivalences,
   so the localizer criterion supplies total derived functors with universal units.
   Their units are invertible on K-injectives; naturality along q gives all four
   displayed computation isomorphisms.
7. Right adjoints preserve products and limits
   (lem-weil-pbc-right-adjoint-preserves-limits). Projection uniqueness gives
   c, beta, their chain-map equations and naturality on every tower complex.
8. Naturality of the universal unit identifies the components of Q(c) with
   RG of each projection. Projectionwise, both shift composites have component
   G(t_n)G(pi_(n+1)); additivity gives the difference equation.
9. Additive functors preserve chain homotopies. The Hom bijection of
   lem-weil-pbc-kinjective-hom-derived supplies all localized morphisms and
   independence of chain representatives, hence localized naturality.
10. Apply lem-weil-pbc-exact-products-roos-comparison. The chain sign map
    (y,x)↦(-y,x) from the negative-difference fibre carries its inclusion to j.
    Compose its inverse with that normalized comparison to obtain kappa;
    thus Q(j) followed by kappa is precisely the universal limit unit. On a
    K-injective complex this unit is invertible, hence j is a quasi-isomorphism.
11. The inverse rotation of the cone triangle has arrows r,1-s,b. Localize
    and transport its first object along Q(j). Its first arrow is Q(lambda)
    and its last is the localized b followed by the inverse shifted Q(j).
    The unit identity identifies this with the unit-normalized Roos triangle. -/
theorem exists_models
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (τ : GrothendieckTopology C) (σ : GrothendieckTopology D)
    (R : Sheaf τ RingCat.{u}) (S : Sheaf σ RingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
    (F : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S)
    [F.Additive] [G.Additive] (adj : F ⊣ G)
    (hF : ∀ E : ShortComplex (ringedSiteModules.{u} S),
      E.ShortExact → (E.map F).ShortExact) :
    Nonempty (Models G) := by
  classical
  let A := ringedSiteModules.{u} R
  let B := ringedSiteModules.{u} S
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian R
  have : IsGrothendieckAbelian.{u} B := SheafOfModules.isGrothendieckAbelian S
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A) := by
    have := smallModuleDiagrams_isGrothendieckAbelian τ R
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ B) := by
    have := smallModuleDiagrams_isGrothendieckAbelian σ S
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have : F.PreservesHomology := ((F.exact_tfae).out 0 2).1 hF
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have : G.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  let Ft := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let Gt := (Functor.whiskeringRight ℕᵒᵖ A B).obj G
  have : PreservesFiniteLimits Ft := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits Ft := ⟨fun _ _ _ ↦ inferInstance⟩
  have : Gt.PreservesKInjectiveComplexes :=
    (adj.whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes
  have : Gt.PreservesInjectiveObjects :=
    (adj.whiskerRight ℕᵒᵖ).preservesInjectiveObjects_of_preservesFiniteLimits
  have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{0, 0} (G.mapHomologicalComplex (.up ℤ)) :=
    (adj.mapHomologicalComplex (.up ℤ)).rightAdjoint_preservesLimits
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have lim_ki {E : Type _} [Category E] [Abelian E] [HasLimitsOfShape ℕᵒᵖ E]
      [(lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive] :
      (lim : (ℕᵒᵖ ⥤ E) ⥤ E).PreservesKInjectiveComplexes := by
    have : (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact Adjunction.preservesKInjectiveComplexes
      (constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ (ℕᵒᵖ ⥤ E)) ⊣ lim)
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes := lim_ki
  have : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).PreservesKInjectiveComplexes := lim_ki
  have hki (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective)
      (hinj : ∀ r : ℤ, Injective (I.X r)) :
      ((tower G).obj I).IsKInjective ∧
      (∀ r : ℤ, Injective (((tower G).obj I).X r)) ∧
      (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n)) ∧
        CochainComplex.IsKInjective
          ((G.mapHomologicalComplex (.up ℤ)).obj (I.asFunctor.obj (op n)))) ∧
      CochainComplex.IsKInjective (limit I.asFunctor) ∧
      CochainComplex.IsKInjective (limit ((tower G).obj I).asFunctor) ∧
      (roosP I).IsKInjective ∧ (roosP ((tower G).obj I)).IsKInjective ∧
      CochainComplex.IsKInjective
        ((G.mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor)) ∧
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj (roosP I)) := by
    have hJ : ((tower G).obj I).IsKInjective := inferInstance
    have hL : CochainComplex.IsKInjective (limit I.asFunctor) :=
      CochainComplex.isKInjective_of_iso (ordinaryIso.app I)
    have hLJ : CochainComplex.IsKInjective (limit ((tower G).obj I).asFunctor) :=
      CochainComplex.isKInjective_of_iso (ordinaryIso.app ((tower G).obj I))
    have hP := (products_compute I).1
    have hPJ := (products_compute ((tower G).obj I)).1
    refine ⟨hJ, ?_, ?_, hL, hLJ, hP, hPJ, inferInstance, inferInstance⟩
    · intro r
      exact Functor.injective_obj Gt (I.X r)
    · intro n
      have := tower_evaluation_isKInjective A I (op n)
      exact ⟨inferInstance, inferInstance⟩
  obtain ⟨direct⟩ := derived_exists G
  obtain ⟨towerDirect⟩ := derived_exists Gt
  obtain ⟨sourceLimit⟩ := limit_derived_exists (A := A)
  obtain ⟨targetLimit⟩ := limit_derived_exists (A := B)
  refine ⟨{ direct := direct
            towerDirect := towerDirect
            sourceLimit := sourceLimit
            targetLimit := targetLimit
            resolution := ?_
            kInjective := hki
            computes := ?_
            products := ?_
            c := productIso G
            beta := limitIso G
            c_components := ?_
            beta_components := ?_
            shift_commutes := productIso_shift G
            difference_commutes := ?_
            derived_product_components := ?_
            localized_maps := ?_
            exact_products := ?_ }⟩
  · intro X
    refine ⟨(CochainComplex.kInjectiveResolutionFunctor.{u} (ℕᵒᵖ ⥤ A)).obj X,
      (CochainComplex.toKInjectiveResolution.{u} (ℕᵒᵖ ⥤ A)).app X,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2,
      inferInstance, fun r ↦ inferInstance⟩
  · intro X I q hq hI hinj
    have := hki I hI hinj
    have hJ := this.1
    have hL := this.2.2.2.1
    have ht := towerDirect.on_injectives I hI
    have hs := sourceLimit.on_injectives I hI
    have htl := targetLimit.on_injectives ((tower G).obj I) hJ
    have hdl := direct.on_injectives (limit I.asFunctor) hL
    refine ⟨computes_one towerDirect q, computes_one sourceLimit q, ?_, ?_⟩
    · let e := asIso (targetLimit.unit.app ((tower G).obj I)) ≪≫
        targetLimit.functor.mapIso (asIso (towerDirect.unit.app I)) ≪≫
        (targetLimit.functor.mapIso
          (towerDirect.functor.mapIso (asIso (DerivedCategory.Q.map q)))).symm
      exact ⟨e, by simp [e]⟩
    · let e := asIso (direct.unit.app (limit I.asFunctor)) ≪≫
        direct.functor.mapIso (asIso (sourceLimit.unit.app I)) ≪≫
        (direct.functor.mapIso
          (sourceLimit.functor.mapIso (asIso (DerivedCategory.Q.map q)))).symm
      exact ⟨e, by simp [e]⟩
  · intro I hI hinj
    have := (hki I hI hinj).1
    exact ⟨(products_compute I).2, (products_compute ((tower G).obj I)).2⟩
  · intro X n
    exact piComparison_comp_π _ _ _
  · intro X n
    exact preservesLimitIso_hom_π _ _ _
  · intro X
    change (G.mapHomologicalComplex (.up ℤ)).map (𝟙 _ - _) ≫ _ = _ ≫ (𝟙 _ - _)
    simp only [Functor.map_sub, Functor.map_id, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.id_comp, productIso_shift]
    erw [Category.comp_id]
  · intro I _ _ n
    have hc : (productIso G).hom.app I ≫
        Pi.π (fun k : ℕ ↦ ((tower G).obj I).asFunctor.obj (op k)) n =
        (G.mapHomologicalComplex (.up ℤ)).map
          (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n) :=
      piComparison_comp_π _ _ _
    rw [← DerivedCategory.Q.map_comp_assoc, hc]
    exact direct.unit.naturality (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n)
  · intro I I' _ hI'
    refine ⟨q_surjective I I', ?_⟩
    intro f g h
    let h := homotopy_of_q_eq h
    let hp := product_homotopy h
    let hl := limit_homotopy h
    exact ⟨DerivedCategory.Q_map_eq_of_homotopy _ hp,
      DerivedCategory.Q_map_eq_of_homotopy _ hl,
      DerivedCategory.Q_map_eq_of_homotopy _ (G.mapHomotopy hp),
      DerivedCategory.Q_map_eq_of_homotopy _ (product_homotopy (Gt.mapHomotopy h)),
      DerivedCategory.Q_map_eq_of_homotopy _ (G.mapHomotopy hl),
      DerivedCategory.Q_map_eq_of_homotopy _ (limit_homotopy (Gt.mapHomotopy h))⟩
  · intro hA hB
    exact ⟨normalized_exists sourceLimit, normalized_exists targetLimit⟩

end CategoryTheory.ExactAdjointTowerModels
