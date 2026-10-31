/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData

/-! # Finite components of whole-system unit multiplication

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemmas 6.5.9 and 6.8.2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.PrimitiveCounit.ringMap
namespace WeilConjectures.CompletedUnitPullback
attribute [local irreducible] calculus systemUnit systemObject systemMap systemMultiplication
  finiteMultiplication rationalObject integralObject rationalSource modelScalar modelUnit
  PrimitiveCounit.inverseEvaluation coefficientSequenceEvaluation
  Scheme.coefficientProEtaleModulePullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem evaluate_transpose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (b : F' ⊣ G') (U : C ⥤ C') (V : D ⥤ D')
    (k : G ⋙ U ≅ V ⋙ G') (e : F ⋙ V ≅ U ⋙ F')
    (he : ∀ M, U.map (a.unit.app M) ≫ k.hom.app (F.obj M) ≫
      G'.map (e.hom.app M) = b.unit.app (U.obj M))
    {M : C} {N : D} (t : M ⟶ G.obj N) :
    b.homEquiv _ _ (e.inv.app M ≫ V.map ((a.homEquiv M N).symm t)) =
      U.map t ≫ k.hom.app N := by
  rw [Adjunction.homEquiv_unit, ← he M]
  simp only [G'.map_comp, Category.assoc]
  rw [← G'.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [G'.map_id, Category.id_comp]
  have hn := k.hom.naturality ((a.homEquiv M N).symm t)
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  rw [← U.map_comp_assoc]
  have ht := (a.homEquiv M N).apply_symm_apply t
  rw [a.homEquiv_unit] at ht
  exact congrArg (fun z ↦ U.map z ≫ k.hom.app N) ht

private theorem eqToHom_section
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (h : M = N) (V : Cᵒᵖ) (x : M.val.obj V) :
    HEq ((eqToHom h).val.app V x) x := by
  subst N
  rfl

private theorem transport_ring_apply {A A' B B' : CommRingCat.{u + 1}}
    (hA : A = A') (hB : B' = B) (φ : A' ⟶ B')
    (x : A) (y : A') (hy : HEq y x) :
    HEq ((eqToHom hA ≫ φ ≫ eqToHom hB).hom x) (φ.hom y) := by
  subst A'
  subst B
  cases hy
  rfl

/-- Evaluation of the adjoint whole-system ring map is its finite adjoint.

Source: Bhatt--Scholze, Lemma 6.5.9(4)-(5); Stacks 03D3, 0941; step 4 of
lem-pur-completed-unit-pullback-tower.
(blueprint: lem-pur-completed-unit-multiplication-components).

Proof: transpose the required equation under the finite pullback/direct-image
adjunction. The unit formula defining inverseEvaluation turns the transpose
of the left side into the evaluation of the whole-system ring map. On sections
the finite-unit identifications are identities, by finite_sections; after these
identifications ringComponent is precisely the finite constant-section ring
map. This is the transpose of finiteMultiplication by its definition. Thus the
two transposes agree on every section. Sheaf hom extensionality followed by
injectivity of the finite adjunction's Hom equivalence gives the equation.
This proves the equation for the actual whole-system arrow, without a lift
of a family of derived arrows. Identity morphisms and the zero ring obey the
same transpose calculation. -/
theorem completedUnitMultiplicationComponents {X Y : Scheme.{u}} (f : X ⟶ Y)
    (rX : Reduction l E X (calculus l E X))
    (rY : Reduction l E Y (calculus l E Y)) (n : ℕ) :
    (coefficientSequenceEvaluation l E X n).map (systemMultiplication l E f) ≫
        (rX.finite n).hom =
      (PrimitiveCounit.inverseEvaluation l E f n).hom.app (systemUnit l E Y) ≫
        (integralOperationsLevelPullback l E f n).map (rY.finite n).hom ≫
          finiteMultiplication l E f n := by
  let a := Adjunction.ofIsRightAdjoint (PrimitiveCounit.direct l E f)
  let b := Scheme.coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let U := coefficientSequenceEvaluation l E Y n
  let V := coefficientSequenceEvaluation l E X n
  let k := eqToIso (PrimitiveCounit.directEvaluation_eq l E f n)
  let e := PrimitiveCounit.inverseEvaluation l E f n
  have he : ∀ M, U.map (a.unit.app M) ≫
      k.hom.app ((PrimitiveCounit.inverse l E f).obj M) ≫
      (Scheme.coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).map (e.hom.app M) =
      b.unit.app (U.obj M) := by
    dsimp only [e]
    unfold PrimitiveCounit.inverseEvaluation
    dsimp only [U, a, k, b]
    exact (PrimitiveCounit.inverseEvaluation_existsUnique l E f n).choose_spec.1
  apply (cancel_epi (e.inv.app (systemUnit l E Y))).1
  dsimp only [e]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  change (e.inv.app (systemUnit l E Y) ≫ V.map (systemMultiplication l E f)) ≫
      (rX.finite n).hom = _
  apply (b.homEquiv (U.obj (systemUnit l E Y))
    (SheafOfModules.unit (integralCoefficientSheaf l E X n))).injective
  change b.homEquiv _ _
      (((PrimitiveCounit.inverseEvaluation l E f n).inv.app (systemUnit l E Y) ≫
        V.map (systemMultiplication l E f)) ≫ (rX.finite n).hom) = _
  rw [b.homEquiv_naturality_right]
  let t : systemUnit l E Y ⟶ (PrimitiveCounit.direct l E f).obj (systemUnit l E X) := by
    unfold PrimitiveCounit.direct systemUnit
    exact SheafOfModules.unitToPushforwardObjUnit _
  have he' : ∀ M, U.map (a.unit.app M) ≫
      k.hom.app ((PrimitiveCounit.direct l E f).leftAdjoint.obj M) ≫
      (Scheme.coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).map (e.hom.app M) =
      b.unit.app (U.obj M) := by
    exact he
  have ht := evaluate_transpose a b U V k e he' t
  have hs : systemMultiplication l E f = (a.homEquiv _ _).symm t := by
    unfold systemMultiplication
    rfl
  rw [hs]
  change b.homEquiv _ _ (e.inv.app _ ≫ V.map ((a.homEquiv _ _).symm t)) ≫ _ = _
  rw [ht]
  erw [b.homEquiv_naturality_left]
  change U.map _ ≫ k.hom.app (systemUnit l E X) ≫
      (Scheme.coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).map
      (rX.finite n).hom = (rY.finite n).hom ≫ _
  let tf : SheafOfModules.unit (integralCoefficientSheaf l E Y n) ⟶
      (Scheme.coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)) := by
    unfold Scheme.coefficientProEtaleModuleDirectImage
    exact SheafOfModules.unitToPushforwardObjUnit _
  have hf := (b.homEquiv (SheafOfModules.unit (integralCoefficientSheaf l E Y n))
    (SheafOfModules.unit (integralCoefficientSheaf l E X n))).apply_symm_apply tf
  have hfs : finiteMultiplication l E f n = (b.homEquiv _ _).symm tf := by
    unfold finiteMultiplication
    rfl
  rw [← hfs] at hf
  rw [hf]
  ext T x
  have hk : HEq (((k.hom.app (systemUnit l E X)).val.app T)
      ((U.map t).val.app T x)) ((U.map t).val.app T x) := by
    dsimp only [k, eqToIso]
    erw [eqToHom_app]
    exact eqToHom_section _ T _
  have hx := rX.finite_sections n ((Scheme.proEtaleBaseChange f).op.obj T)
    (show ((coefficientSequenceEvaluation l E X n).obj (systemUnit l E X)).val.obj
      ((Scheme.proEtaleBaseChange f).op.obj T) from
      ((k.hom.app (systemUnit l E X)).val.app T) ((U.map t).val.app T x))
  have hy := rY.finite_sections n T x
  let y := (rY.finite n).hom.val.app T x
  change HEq y x at hy
  apply eq_of_heq
  apply (hx.trans hk).trans
  dsimp only [U] at x ⊢
  unfold coefficientSequenceEvaluation systemUnit at x ⊢
  dsimp only [t, tf]
  unfold PrimitiveCounit.ringMap
  change HEq
    ((PrimitiveCounit.ringComponent l E f (op (n, T.unop))).hom x)
    (((Scheme.coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).hom.app T).hom
      y)
  unfold PrimitiveCounit.ringComponent
  dsimp only [U] at hy
  unfold coefficientSequenceEvaluation systemUnit at hy
  exact transport_ring_apply _ _ _ _ _ hy

end WeilConjectures.CompletedUnitPullback
