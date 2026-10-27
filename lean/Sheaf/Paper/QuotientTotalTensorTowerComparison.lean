/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.NormalizedFiniteTensorComparison
import all Sheaf.Paper.IntegralTensorTransitionCompatibility

/-! # The strict balancing comparison for quotient total tensors

Source: Stacks Project, sites-cohomology.tex, Tag 07A4; proetale.tex, Tag 099M.
(blueprint: lem-sf-quotient-total-tensor-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.ConstantCompletion
attribute [local irreducible] CategoryTheory.ConstantCompletion.completed
  CategoryTheory.ConstantCompletion.quotientPresentation HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.ConstantCompletion.rlim

namespace CategoryTheory.AmbientCompletedTensor
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] (I : Ideal A)

private def tensorTerm (n : ℕ) : Cx (completed J A I) × Cx (completed J A I) ⥤
    Cx (completed J A I) :=
  ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
      ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
    coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
      (res (projection J A I n)).mapHomologicalComplex (.up ℤ)

private def tensorGenerator (n : ℕ) (P Q : Cx (completed J A I))
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (a b : (finite J A I n).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((tensorTerm J A I n).obj (P, Q)).X k).val.obj U :=
  coefficientTensorGenerator.{u, u, u} J (finite J A I n)
    (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
    (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
    p q k h U (tensorSection (projection J A I n) (P.X p) U a x)
      (tensorSection (projection J A I n) (Q.X q) U b y)

private instance reduction_additive (n : ℕ) : (reduction J A I true n).Additive := by
  dsimp only [reduction]
  infer_instance

private theorem reductionStep_tensorSection (n : ℕ) (M : Mod (completed J A I))
    (U : Cᵒᵖ) (s : (finite J A I (n + 1)).obj.obj U) (x : M.val.obj U) :
    ((reductionStep J A I true n).app M).val.app U
        (tensorSection (projection J A I (n + 1)) M U s x) =
      tensorSection (projection J A I n) M U ((transition J A I n).hom.app U s) x :=
  (reductionStep_existsUnique J A I true n).exists.choose_spec M U s x

private theorem finiteTensorComparison_exists (n : ℕ) :
    ∃ e : coefficientTotalTensor.{u, u, u} J (completed J A I) ⋙
        (reduction J A I true n).mapHomologicalComplex (.up ℤ) ≅ tensorTerm J A I n,
      ∀ (P Q : Cx (completed J A I)) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (a b : (finite J A I n).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((e.hom.app (P, Q)).f k).val.app U
          (tensorSection (projection J A I n)
            (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k)
            U (a * b) (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y)) =
          tensorGenerator J A I n P Q p q k h U a b x y := by
  exact normalizedFiniteTensorComparison J A I n

/-- Strict balancing comparison of the quotient tensor towers, retaining the
complex presentation V and its comparison b. One may take V to be the reduction
complex and b its identity; retaining b avoids reducing its section maps downstream.
Source: Stacks 07A4, 06YM and 099M.
(blueprint: lem-sf-quotient-total-tensor-tower-comparison).
Proof: on each bidegree send c tensor (x tensor y) to
(1 tensor x) tensor (c tensor y). The inverse multiplies the two scalar factors.
Balancing gives inverse module maps; sheafify and sum over the total degrees.
Each signed differential summand commutes with these maps. The two transition
composites send c to its quotient and fix x and y. Pure tensors locally generate
the sheafified summands, and their coproduct injections determine maps from the
total degree. Thus the comparisons form a strict tower isomorphism. No flatness,
boundedness, or Noetherian hypothesis is needed; zero and unit ideals are included. -/
theorem quotientTotalTensorTowerComparison
    (τ : ∀ n : ℕ, (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I (n + 1)) ⋙
        (res (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)) ⟶
      (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
        (res (projection J A I n)).mapHomologicalComplex (.up ℤ)))
    (hτ : ∀ (n : ℕ) (P Q : Cx (completed J A I))
      (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
      (a b : (finite J A I (n + 1)).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (((τ n).app (P, Q)).f k).val.app U
        (coefficientTensorGenerator.{u, u, u} J (finite J A I (n + 1))
          (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I (n + 1)) (P.X p) U a x)
            (tensorSection (projection J A I (n + 1)) (Q.X q) U b y)) =
        coefficientTensorGenerator.{u, u, u} J (finite J A I n)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I n) (P.X p) U ((transition J A I n).hom.app U a) x)
            (tensorSection (projection J A I n) (Q.X q) U ((transition J A I n).hom.app U b) y))
    (P Q : Cx (completed J A I)) :
    ∃ (V : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ)
      (b : reductionComplex J A I true
        ((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)) ≅ V)
      (κ : V.asFunctor ≅
      (Functor.ofOpSequence (X := fun n : ℕ ↦
        (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
        (res (projection J A I n)).mapHomologicalComplex (.up ℤ))) τ).flip.obj (P, Q)),
      ∀ (n : ℕ) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (c : (finite J A I n).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (op n)).f k).val.app U
          (((b.hom.f k).app (op n)).val.app U
            (tensorSection (projection J A I n)
            (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k) U c
            (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y))) =
          coefficientTensorGenerator.{u, u, u} J (finite J A I n)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I n) (P.X p) U 1 x)
            (tensorSection (projection J A I n) (Q.X q) U c y) := by
  classical
  let H := (coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)
  let e n := (finiteTensorComparison_exists J A I n).choose
  have he (n : ℕ) := (finiteTensorComparison_exists J A I n).choose_spec
  have hstep (n : ℕ) :
      (NatTrans.mapHomologicalComplex (reductionStep J A I true n) (.up ℤ)).app H ≫
          (e n).hom.app (P, Q) =
        (e (n + 1)).hom.app (P, Q) ≫ (τ n).app (P, Q) := by
    apply HomologicalComplex.hom_ext
    intro k
    let F := change (projection J A I (n + 1))
    let : PreservesColimitsOfSize.{0, 0} F :=
      WeilConjectures.extension_preserves_small_colimits.{u, u, u} (projection J A I (n + 1)) F
        (fun _ ↦ rfl)
        (fun _ ↦ by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    apply WeilConjectures.total_extension_hom_ext.{u, u, u}
      (projection J A I (n + 1)) F (fun _ ↦ rfl)
        (fun _ ↦ by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl) P Q k
    intro p q h U c x y
    have he₀ := he n P Q p q k h U 1 ((transition J A I n).hom.app U c) x y
    have he₁ := he (n + 1) P Q p q k h U 1 c x y
    simp only [one_mul] at he₀ he₁
    change (((e n).hom.app (P, Q)).f k).val.app U
        (((reductionStep J A I true n).app (H.X k)).val.app U
          (tensorSection (projection J A I (n + 1)) (H.X k) U c
            (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y))) =
      (((τ n).app (P, Q)).f k).val.app U
        ((((e (n + 1)).hom.app (P, Q)).f k).val.app U
          (tensorSection (projection J A I (n + 1)) (H.X k) U c
            (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y)))
    rw [reductionStep_tensorSection, he₀, he₁]
    simpa only [tensorGenerator, map_one] using (hτ n P Q p q k h U 1 c x y).symm
  let κ := NatTrans.ofOpSequence
    (F := (reductionComplex J A I true H).asFunctor)
    (G := (Functor.ofOpSequence (X := fun n ↦ tensorTerm J A I n) τ).flip.obj (P, Q))
    (fun n ↦ (e n).hom.app (P, Q)) (fun n ↦ by
      apply HomologicalComplex.hom_ext
      intro k
      change ((reductionTower J A I true).obj (H.X k)).map
          (homOfLE (n.le_add_right 1)).op ≫ ((e n).hom.app (P, Q)).f k =
        ((e (n + 1)).hom.app (P, Q)).f k ≫
          (((Functor.ofOpSequence (X := fun m ↦ tensorTerm J A I m) τ).map
            (homOfLE (n.le_add_right 1)).op).app (P, Q)).f k
      simpa only [reductionTower, Functor.flip_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ, HomologicalComplex.comp_f,
        NatTrans.mapHomologicalComplex_app_f] using
        congrArg (fun f ↦ f.f k) (hstep n))
  have hκ (n : ℕᵒᵖ) : IsIso (κ.app n) := by
    change IsIso ((e n.unop).hom.app (P, Q))
    infer_instance
  have : IsIso κ := NatIso.isIso_of_isIso_app κ
  refine ⟨reductionComplex J A I true H, Iso.refl _, asIso κ, ?_⟩
  intro n p q k h U c x y
  change (((e n).hom.app (P, Q)).f k).val.app U
      (tensorSection (projection J A I n) (H.X k) U c
        (coefficientTensorGenerator.{u, u, u} J (completed J A I)
          P Q p q k h U x y)) =
    tensorGenerator J A I n P Q p q k h U 1 c x y
  simpa only [one_mul] using he n P Q p q k h U 1 c x y

end CategoryTheory.AmbientCompletedTensor
