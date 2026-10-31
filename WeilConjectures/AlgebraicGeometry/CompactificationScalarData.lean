/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimitSupport
import WeilConjectures.AlgebraicGeometry.CompactificationScalarSquares
import WeilConjectures.AlgebraicGeometry.CompactificationOrdinaryScalarAssembly
import WeilConjectures.AlgebraicGeometry.CompactificationDerivedScalarComparison
import WeilConjectures.AlgebraicGeometry.CompactificationLimitPresentation
import WeilConjectures.AlgebraicGeometry.CompactificationScalarTransitionAcyclicity

/-! # Normalized scalar data for strict compactification systems
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-scalar-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem evaluation_sections (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.obj U)
      (((spCoefficientEvaluation l E T D.equivalence n).obj M).val.obj U) := by
  dsimp [SpTowerShriek.ev, SemilinearSections.evaluation, SheafOfModules.pushforward,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj,
    spCoefficientEvaluation, systemEvaluation]
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app, eqToHom_refl]
  exact (b.sections T M n U).trans (D.sections M n U).symm

private theorem hom_function_heq {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {g : M' ⟶ N'} (hfg : HEq f g) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  cases hM
  cases hN
  cases hfg
  rfl

set_option maxHeartbeats 2000000 in
-- Comparing the two concrete ring-presheaf presentations requires unfolding their objects.
private theorem evaluation_restrictions (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.map f x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).obj M).val.map f x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.obj M).val.map
      (Prod.mkHom (𝟙 n) f.unop).op x)
    (fun x ↦ ((D.equivalence.functor.obj M).level n).val.map f x)
  have hB := b.restrictions T M (Prod.mkHom (𝟙 n) f.unop).op
  have hD := D.restrictions M n f
  refine hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm)) ?_
    (hB.trans hD.symm)
  have hmap :
      ((SemilinearSections.ring (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj.map
            (Prod.mkHom (𝟙 n) f.unop).op).hom =
      ((spCoefficientRing l E T n).obj.map f).hom := by
    change ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((((SemilinearSections.rings (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (𝟙 (op n))).hom.app U) ≫
          (SpTowerShriek.B l E T n).obj.map f)).hom =
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((SpTowerShriek.B l E T n).obj.map f)).hom
    erw [CategoryTheory.Functor.map_id]
    simp
  rw [hmap]
  exact congrArg (ModuleCat.restrictScalars
    (((spCoefficientRing l E T n).obj).map f).hom).obj
    (eq_of_heq ((b.sections T M n V).trans (D.sections M n V).symm))

set_option maxHeartbeats 2000000 in
-- Evaluation changes scalar actions but leaves these underlying section functions intact.
private theorem evaluation_maps (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    {M N : spCoefficientTowers l E T} (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).map ((b.realization T).functor.map f)).val.app U x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.map f).val.app (op (n, U.unop)) x)
    (fun x ↦ ((D.equivalence.functor.map f).app n).val.app U x)
  exact hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm))
    (eq_of_heq ((b.sections T N n U).trans (D.sections N n U).symm))
    ((b.morphisms T f (op (n, U.unop))).trans (D.morphisms f n U).symm)

private theorem transport_restriction {A B : Type*} [Ring A] [Ring B]
    (q : A →+* B) {M M' : ModuleCat A} {N N' : ModuleCat B}
    (hM : M = M') (hN : N = N')
    (f : M ⟶ (ModuleCat.restrictScalars q).obj N)
    (g : M' ⟶ (ModuleCat.restrictScalars q).obj N')
    (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ (ModuleCat.restrictScalars q).map (eqToHom hN) = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private theorem transport_morphism {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ eqToHom hN = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private theorem transport_section {R : Type*} [Ring R]
    {M N : ModuleCat R} (h : M = N) (x : M) : HEq (eqToHom h x) x := by
  cases h
  rfl

private def evaluation_object (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) :
    (SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M) ≅
      (spCoefficientEvaluation l E T D.equivalence n).obj M where
  hom := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U))
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D M n V)) _ _
      (evaluation_restrictions l E b T D M n f) }⟩
  inv := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U)).symm
      (eq_of_heq (evaluation_sections l E b T D M n V)).symm _ _
      (evaluation_restrictions l E b T D M n f).symm }⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]

private def evaluation_data (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) : Evaluation l E b T D where
  ordinary n := NatIso.ofComponents (fun M ↦ evaluation_object l E b T D M n) (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change ((SpTowerShriek.ev l E T n).map
        ((b.realization T).functor.map f)).val.app U ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D N n U)) =
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
        ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U
    exact transport_morphism
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D N n U)) _ _
      (evaluation_maps l E b T D f n U))
  sections n M U x := by
    change HEq ((eqToHom (eq_of_heq (evaluation_sections l E b T D M n U))) x) x
    exact transport_section (eq_of_heq (evaluation_sections l E b T D M n U)) x

/-- The coefficient presentations and the ordinary and derived scalar squares.

Proof. Use the completed coefficient projections and their pullback compatibility to
obtain the scalar change squares. Transport the reduction/limit adjunction of
SequenceProjection.pushforwardLimitProjections through the recorded exact coefficient
section equivalences. Its tensor generators and counit identify the finite evaluations
and fix the unit-projection equation. The two recorded section presentations have the
identity comparison on their underlying modules, giving the evaluation isomorphisms.
For open extension, the scalar comparison is the identity on each extension summand;
semilinear transitions commute with this identity before exact localization. For direct
image, apply diagramRingRestrictionPushforward to the coefficient projections and
transport its unique comparison through the same section equivalences. Its ordinary
comparison is the identity on sections, hence has the stated finite normalization.
Invert its derived comparison: its universal composition-unit identity becomes precisely
IsPushScalarNormalized. These constructions take place on strict systems and complexes,
so they preserve all quotient transitions, before taking any inverse limit.
Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-direct-image.proof.md, paragraph (2);
parent node proof steps 1 and 2; Stacks 03DI, 03D7, 0D6E.
(blueprint: lem-sp-compactification-scalar-data). -/
theorem compactificationScalarData
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    (r : ∀ T : Scheme.{u}, SpReductionTower l E T (D T)) :
    ∃ (h : ScalarSquares l E)
      (a : ∀ T : Scheme.{u}, LimitPresentation l E T (D T) (r T))
      (v : ∀ T : Scheme.{u}, Evaluation l E b T (D T)),
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f)
      (_ : CompactSpace X) (_ : QuasiSeparatedSpace X)
      (_ : CompactSpace c.Z) (_ : QuasiSeparatedSpace c.Z)
      (_ : CompactSpace Y) (_ : QuasiSeparatedSpace Y)
      (_ : ∀ x : X, IsUnit (l : X.residueField x))
      (_ : ∀ x : c.Z, IsUnit (l : c.Z.residueField x))
      (_ : ∀ x : Y, IsUnit (l : Y.residueField x)) (_ : QuasiCompact c.i),
    ∃ (openOrdinary : forgetting l E X (D X) ⋙ fixedOpenOrd l E c.i ≅
    ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z (D c.Z)),
    ∃ (pushOrdinary : forgetting l E c.Z (D c.Z) ⋙ fixedPushOrd l E c.g ≅
    ordinaryTowerPush l E b o c.g ⋙ forgetting l E Y (D Y)),
    ∃ (pushDerived : forgetDerived l E c.Z (D c.Z) (r c.Z) (a c.Z) ⋙
      (fixedPushOrd l E c.g).rightDerivedFunctor ≅
    towerPush l E b o c.g (D c.Z) (D Y) ⋙ forgetDerived l E Y (D Y) (r Y) (a Y)),
    (∀ (N : spCoefficientTowers l E X) (n : ℕ),
    (openOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E c.Z n).map
          ((ordinaryOpenEvaluation l E b o c.i (D X) (D c.Z) (v X) (v c.Z) n).hom.app N) =
      (ordinaryOpenScalar l E b h c.i n).hom.app
        ((spCoefficientEvaluation l E X (D X).equivalence n).obj N)) ∧
    (∀ (N : spCoefficientTowers l E c.Z) (n : ℕ),
    (pushOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E Y n).map
          ((ordinaryPushEvaluation l E b o c.g (D c.Z) (D Y) (v c.Z) (v Y) n).hom.app N) =
      (ordinaryPushScalar l E h c.g n).hom.app
        ((spCoefficientEvaluation l E c.Z (D c.Z).equivalence n).obj N)) ∧
    IsPushScalarNormalized l E b o c.g (D c.Z) (D Y) (r c.Z) (r Y) (a c.Z) (a Y)
    pushOrdinary pushDerived := by
  classical
  let h : ScalarSquares l E := compactificationScalarSquares l E
  let a : ∀ T : Scheme.{u}, LimitPresentation l E T (D T) (r T) :=
    fun T ↦ Classical.choice (compactificationLimitPresentation l E T (D T) (r T))
  let v : ∀ T : Scheme.{u}, Evaluation l E b T (D T) :=
    fun T ↦ evaluation_data l E b T (D T)
  refine ⟨h, a, v, ?_⟩
  intro X Y f c hXqc hXqs hZqc hZqs hYqc hYqs hX hZ hY hj
  let := hXqc
  let := hXqs
  let := hZqc
  let := hZqs
  let := hYqc
  let := hYqs
  let := hj
  obtain ⟨hcj, hcp, hacyc⟩ := compactificationScalarTransitionAcyclicity l E b o h
    X Y f c hX hZ hY (D X) (D c.Z) (D Y) (v X) (v c.Z) (v Y)
  obtain ⟨e₀, d₀, he₀, hd₀⟩ := compactificationOrdinaryScalarAssembly l E b o h
    c.i c.g (D X) (D c.Z) (D Y) (v X) (v c.Z) (v Y) hcj hcp
  obtain ⟨d, hd⟩ := compactificationDerivedScalarComparison l E b o c.g
    (D c.Z) (D Y) (r c.Z) (r Y) (a c.Z) (a Y) d₀ hacyc
  exact ⟨e₀, d₀, d, he₀, hd₀, hd⟩

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
