/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralFiniteScalarTensorIso

/-! # The scalar restriction comparison of strict pulled finite quotient towers

Source: blueprint `det-lem-int-tensor-pullback.proof.md`, comparison paragraph.
(blueprint: lem-sfb-restricted-pulled-quotient-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.IntegralTensorPullback

namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback

private def tensorRestrictionNat (X : Scheme.{u}) (n : ℕ) :
    restriction l E X ⋙ tensorRight (constantFinite l E X n) ⟶
      tensorRight (AdicCompletion.finiteModule l E X n) ⋙ restriction l E X := by
  letI := Mod.comapLaxMonoidal ((upperStarFromPoint X).map (constantToIntegral l E))
  exact
    { app := fun M ↦ Mod.comapTensorHom
        ((upperStarFromPoint X).map (constantToIntegral l E)) M
        (AdicCompletion.finiteModule l E X n)
      naturality := by
        intro M N f
        exact Functor.LaxMonoidal.μ_natural_left
          (restriction l E X) f (AdicCompletion.finiteModule l E X n) }

private def tensorRestrictionComplex (X : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (constantLevel l E X n).obj
        (((restriction l E X).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((restriction l E X).mapHomologicalComplex (.up ℤ)).obj
        ((AdicCompletion.level l E X n).obj P) :=
  (NatTrans.mapHomologicalComplex (tensorRestrictionNat l E X n) (.up ℤ)).app P

private def towerRestriction (X : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    constantTower l E X (((restriction l E X).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      tower l E X P ⋙ (restriction l E X).mapHomologicalComplex (.up ℤ) :=
  NatTrans.ofOpSequence (fun n ↦ tensorRestrictionComplex l E X n P) (by
    intro n
    apply HomologicalComplex.hom_ext
    intro i
    simp only [constantTower, tower, Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f]
    let := Mod.comapLaxMonoidal ((upperStarFromPoint X).map (constantToIntegral l E))
    change ((restriction l E X).obj (P.X i) ◁
        (restriction l E X).map
          ((DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n))) ≫
        Functor.LaxMonoidal.μ (restriction l E X) (P.X i)
          (AdicCompletion.finiteModule l E X n) = _
    exact Functor.LaxMonoidal.μ_natural_right (restriction l E X) (P.X i) _)

private theorem tensorRestriction_unit (X : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    constantLevelUnit l E X
        (((restriction l E X).mapHomologicalComplex (.up ℤ)).obj P) n ≫
      tensorRestrictionComplex l E X n P =
    ((restriction l E X).mapHomologicalComplex (.up ℤ)).map
      (AdicCompletion.levelUnit l E X P n) := by
  apply HomologicalComplex.hom_ext
  intro i
  let := Mod.comapLaxMonoidal ((upperStarFromPoint X).map (constantToIntegral l E))
  change (ρ_ ((restriction l E X).obj (P.X i))).inv ≫
      ((restriction l E X).obj (P.X i) ◁
        (Functor.LaxMonoidal.ε (restriction l E X) ≫
          (restriction l E X).map (AdicCompletion.finiteUnit l E X n))) ≫
        Functor.LaxMonoidal.μ (restriction l E X) (P.X i)
          (AdicCompletion.finiteModule l E X n) =
    (restriction l E X).map ((ρ_ (P.X i)).inv ≫
      (P.X i ◁ AdicCompletion.finiteUnit l E X n))
  rw [whiskerLeft_comp, Category.assoc, Functor.LaxMonoidal.μ_natural_right,
    CategoryTheory.Functor.map_comp]
  exact Functor.LaxMonoidal.right_unitality_inv_assoc (restriction l E X) (P.X i) _

private def pulledTensorRestriction {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    constantPulledTower l E g
        (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      pulledTower l E g P ⋙ (restriction l E X).mapHomologicalComplex (.up ℤ) :=
  NatTrans.ofOpSequence (fun n ↦
    ((CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)).map
        (tensorRestrictionComplex l E Y n P) ≫
      (restrictionPullbackComplex l E g ((AdicCompletion.level l E Y n).obj P)).inv) (by
    intro n
    let G := (CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)
    have ht : constantStep l E Y
        (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P) n ≫
          tensorRestrictionComplex l E Y n P =
        tensorRestrictionComplex l E Y (n + 1) P ≫
          ((restriction l E Y).mapHomologicalComplex (.up ℤ)).map
            (AdicCompletion.levelStep l E Y P n) := by
      simpa only [towerRestriction, NatTrans.ofOpSequence_app, Functor.comp_map,
        tower, constantTower, Functor.ofOpSequence_map_homOfLE_succ] using
        (towerRestriction l E Y P).naturality (homOfLE (Nat.le_succ n)).op
    have ha := (NatIso.mapHomologicalComplex (restrictionPullback l E g) (.up ℤ)).inv.naturality
      (AdicCompletion.levelStep l E Y P n)
    simp only [constantPulledTower, pulledTower, Functor.comp_map, tower, constantTower,
      Functor.ofOpSequence_map_homOfLE_succ]
    change G.map _ ≫ (G.map _ ≫ _) = (G.map _ ≫ _) ≫ _
    rw [← Category.assoc, ← G.map_comp, ht, G.map_comp]
    simp only [Category.assoc]
    exact congrArg (G.map (tensorRestrictionComplex l E Y (n + 1) P) ≫ ·) ha)

/-- Scalar restriction identifies the strict pulled finite quotient towers and
intertwines their augmentation legs through the fixed restriction/pullback comparison.
This statement concerns finite quotients and tower maps only; it involves no product
or Roos construction.

Source: blueprint `det-lem-int-tensor-pullback.proof.md`, comparison paragraph,
restriction commutes with inverse image and reduction; Stacks Tags 099I and 099N(5).
(blueprint: lem-sfb-restricted-pulled-quotient-tower).

Proof: let C be the constant integral coefficient and R the continuous coefficient.
The quotient R_n at positive exponent n+1 is the constant finite quotient C_n:
continuous maps to that finite discrete ring are locally constant. The resulting
comparison C_n to Res(R_n) is compatible with the quotient units and all reductions.
Extending C_n from C to R gives R_n, since both are the quotient by the same
uniformizer power. The balanced tensor associator and this identification give
Res(M tensor_R R_n) isomorphic to Res(M) tensor_C Res(R_n) for every R-module M.
Use the same construction in each degree of P; naturality in M makes it a chain
isomorphism, and naturality in R_n makes the transition squares commute. Apply
constant inverse image to these level maps and combine them with restrictionPullback
on each reduced complex. Their composite is the required tower isomorphism e.
For the displayed square, first use naturality of restrictionPullback on the
quotient unit of P. The remaining tensor comparison sends the quotient generator
m tensor 1 to the same generator on the constant side. This follows from the
coefficient-unit compatibility and the unitor identities for balanced tensor
products. These generators jointly generate, so the augmentation legs agree.
The construction works for every P, including zero complexes, empty schemes,
identity morphisms, and the first positive quotient; it uses no K-flatness. -/
theorem restricted_pulled_tower_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    let F := (CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
      (.up ℤ)
    let G := (CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)
    let Q := ((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P
    let γ : (Functor.const ℕᵒᵖ).obj (F.obj P) ⟶ pulledTower l E g P :=
      (Functor.constComp ℕᵒᵖ P F).inv ≫ Functor.whiskerRight (towerUnit l E Y P) F
    let δ : (Functor.const ℕᵒᵖ).obj (G.obj Q) ⟶ constantPulledTower l E g Q :=
      (Functor.constComp ℕᵒᵖ Q G).inv ≫ Functor.whiskerRight (constantTowerUnit l E Y Q) G
    ∃ e : pulledTower l E g P ⋙ (restriction l E X).mapHomologicalComplex (.up ℤ) ≅
        constantPulledTower l E g Q,
      ∀ n : ℕ, ((restriction l E X).mapHomologicalComplex (.up ℤ)).map
          (γ.app (op n)) ≫ e.hom.app (op n) =
        (restrictionPullbackComplex l E g P).hom ≫ δ.app (op n) := by
  dsimp only
  let τ := pulledTensorRestriction l E g P
  have ht (n : ℕ) : IsIso (τ.app (op n)) := by
    have hc : IsIso (tensorRestrictionComplex l E Y n P) := by
      let (i : ℤ) : IsIso ((tensorRestrictionComplex l E Y n P).f i) := by
        change IsIso (Mod.comapTensorHom
          ((upperStarFromPoint Y).map (constantToIntegral l E)) (P.X i)
            (AdicCompletion.finiteModule l E Y n))
        exact finite_scalar_tensor_isIso l E Y n (P.X i)
      exact HomologicalComplex.Hom.isIso_of_components _
    change IsIso (_ ≫ (restrictionPullbackComplex l E g
      ((AdicCompletion.level l E Y n).obj P)).inv)
    infer_instance
  let (n : ℕᵒᵖ) : IsIso (τ.app n) := ht n.unop
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine ⟨(asIso τ).symm, ?_⟩
  intro n
  change _ ≫ (asIso τ).inv.app (op n) = _
  have hinv : (asIso τ).inv.app (op n) ≫ τ.app (op n) = 𝟙 _ :=
    (asIso τ).inv_hom_id_app (op n)
  apply (cancel_mono (τ.app (op n))).mp
  simp only [Category.assoc, hinv, Category.comp_id]
  dsimp only [τ, pulledTensorRestriction, NatTrans.ofOpSequence_app]
  simp only [NatTrans.comp_app, Functor.constComp_inv_app,
    Functor.whiskerRight_app, Category.id_comp]
  simp only [towerUnit, constantTowerUnit, NatTrans.ofOpSequence_app]
  apply (cancel_mono (restrictionPullbackComplex l E g
    ((AdicCompletion.level l E Y n).obj P)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← CategoryTheory.Functor.map_comp, tensorRestriction_unit]
  exact (NatIso.mapHomologicalComplex (restrictionPullback l E g) (.up ℤ)).hom.naturality
    (AdicCompletion.levelUnit l E Y P n)

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
