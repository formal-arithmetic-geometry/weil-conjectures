/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import Mathlib.Analysis.SpecialFunctions.Log.Base
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField

/-! # Weight of a condensed constant Weil twist

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/
`sk-r-real-linear/lem-wf-constant-twist-weight.md`
(blueprint: lem-wf-constant-twist-weight).

The statement uses the actual condensed Weil module and the local return convention
of the current coefficient model. The constant line and its tensor are the
canonical constructions in `CondensedRing.ConstantWeil`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

open NativeCondensedModule MonoidalCategory

private def unitScalars (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    PadicAlgCl l →+* End (𝟙_ (Modules l X)) :=
  (Mod.regularEndRingHom.comp (MonObj.Γ.mapFunctor (upperStarFromPoint X))).comp
    (Profinite.PadicAlgCl.constRingHom l)

private def scalarIso (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (b : (PadicAlgCl l)ˣ) (M : Modules l X) : M ≅ M :=
  (λ_ M).symm ≪≫ (tensorRight M).mapIso
    (Aut.unitsEndEquivAut _ (Units.map (unitScalars l X).toMonoidHom b)) ≪≫ λ_ M

private def coefficientScalars (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    PadicAlgCl l →+* MonObj.Γ (padicAlgClRingObj X l) :=
  (MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
    (Profinite.PadicAlgCl.constRingHom l)

attribute [local instance] linearModules

attribute [local instance] linearLowerStar

attribute [local instance] linearUpperStar

private theorem unitScalars_smul_id (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (a : PadicAlgCl l) : unitScalars l X a = a • 𝟙 (𝟙_ (Modules l X)) := by
  rw [Mod.linearOfRingHom_smul_id (coefficientScalars l X)]
  apply Mod.hom_ext
  exact Mod.rightUnitor_inv_whiskerLeft_mul_eq
    (S := padicAlgClRingObj X l) (coefficientScalars l X a).hom

private theorem left_scalar_eq_right {C : Type*} [Category* C]
    [MonoidalCategory C] [BraidedCategory C] (M : C) (t : End (𝟙_ C)) :
    (λ_ M).inv ≫ t ▷ M ≫ (λ_ M).hom =
      (ρ_ M).inv ≫ M ◁ t ≫ (ρ_ M).hom := by
  rw [← braiding_rightUnitor M,
    BraidedCategory.braiding_naturality_left_assoc,
    braiding_tensorUnit_left]
  simp

private theorem unit_twist_equivariance {C : Type*} [Category* C]
    [MonoidalCategory C] [BraidedCategory C] (P : C ⥤ C) [P.Monoidal]
    (M : C) (φ : P.obj M ≅ M) (t : End (𝟙_ C)) :
    P.map (ρ_ M).hom ≫ φ.hom ≫
        ((λ_ M).inv ≫ t ▷ M ≫ (λ_ M).hom) =
      (Functor.Monoidal.μIso P M (𝟙_ C)).inv ≫
        (φ.hom ⊗ₘ ((Functor.Monoidal.εIso P).inv ≫ t)) ≫ (ρ_ M).hom := by
  rw [left_scalar_eq_right, ← Functor.OplaxMonoidal.right_unitality_hom P M]
  simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, Iso.hom_inv_id_assoc,
    ← whisker_exchange_assoc φ.hom t]
  rfl

private theorem scalarIso_hom_formula (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (b : (PadicAlgCl l)ˣ) (M : Modules l X) :
    (scalarIso l b M).hom =
      (λ_ M).inv ≫ unitScalars l X b ▷ M ≫ (λ_ M).hom := by
  rfl

private theorem scalarIso_hom (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (b : (PadicAlgCl l)ˣ) (M : Modules l X) :
    (scalarIso l b M).hom = (b : PadicAlgCl l) • 𝟙 M := by
  simp only [scalarIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (λ_ M).inv ≫ unitScalars l X b ▷ M ≫ (λ_ M).hom = _
  rw [left_scalar_eq_right, unitScalars_smul_id]
  rw [Mod.linearOfRingHom_smul_id (coefficientScalars l X),
    Mod.linearOfRingHom_smul_id (coefficientScalars l X)]
  rw [← Mod.smulNatTrans_app_tensor]
  have h := (Mod.smulNatTrans (coefficientScalars l X b).hom).naturality (ρ_ M).hom
  simp only [Functor.id_map] at h
  rw [← h, Iso.inv_hom_id_assoc]

private theorem isoChain_naturality {C : Type*} [Category* C]
    (A B : ℕ → C) (M N : C) (f : M ⟶ N)
    (iA : A 0 ≅ M) (iB : B 0 ≅ N)
    (sA : ∀ n, A (n + 1) ≅ A n) (sB : ∀ n, B (n + 1) ≅ B n)
    (v : ∀ n, A n ⟶ B n) (hi : v 0 ≫ iB.hom = iA.hom ≫ f)
    (hs : ∀ n, v (n + 1) ≫ (sB n).hom = (sA n).hom ≫ v n) (n : ℕ) :
    v n ≫ (isoChain B N iB sB n).hom = (isoChain A M iA sA n).hom ≫ f := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change v (n + 1) ≫ ((sB n).hom ≫ (isoChain B N iB sB n).hom) =
      ((sA n).hom ≫ (isoChain A M iA sA n).hom) ≫ f
    rw [← Category.assoc, hs, Category.assoc, ih, Category.assoc]

private theorem isoChain_scalar {C : Type*} [Category* C] [Preadditive C]
    {R : Type*} [CommRing R] [Linear R C] (A : ℕ → C) (M : C)
    (i i' : A 0 ≅ M) (s s' : ∀ n, A (n + 1) ≅ A n)
    (b : R) (hi : i'.hom = b • i.hom) (hs : ∀ n, (s' n).hom = b • (s n).hom)
    (n : ℕ) : (isoChain A M i' s' n).hom = b ^ (n + 1) • (isoChain A M i s n).hom := by
  induction n with
  | zero =>
    change i'.hom = b ^ (0 + 1) • i.hom
    simpa only [Nat.zero_add, pow_one] using hi
  | succ n ih =>
    change (s' n).hom ≫ (isoChain A M i' s' n).hom =
      b ^ (n + 1 + 1) • ((s n).hom ≫ (isoChain A M i s n).hom)
    rw [hs, ih, Linear.smul_comp, Linear.comp_smul, smul_smul, pow_succ b (n + 1), mul_comm b]

private theorem evaluateInitial_naturality {C : Type*} [Category* C]
    (F G : C ⥤ C) (c : F ≅ G) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    F.map f ≫ (evaluateInitial F G c N η).hom =
      (evaluateInitial F G c M θ).hom ≫ f := by
  dsimp only [evaluateInitial, Iso.trans_hom, Iso.app_hom]
  rw [NatTrans.naturality_assoc, hf, Category.assoc]

private theorem evaluateStep_naturality {C : Type*} [Category* C]
    (F G H : C ⥤ C) (c : H ≅ G ⋙ F) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    H.map f ≫ (evaluateStep F G H c N η).hom =
      (evaluateStep F G H c M θ).hom ≫ F.map f := by
  dsimp only [evaluateStep, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, hf, Functor.map_comp, Category.assoc]

private theorem iterate_naturality (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a n)).map f ≫ (iterate l a N η n).hom =
      (iterate l a M θ n).hom ≫ f := by
  unfold iterate
  refine isoChain_naturality
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj M)
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj N) M N f _ _ _ _
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).map f) ?_ ?_ n
  · exact evaluateInitial_naturality _ _ _ M N θ η f hf
  · intro k
    unfold iterateStep
    exact evaluateStep_naturality _ _ _ _ M N θ η f hf

private theorem iterate_scalar (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (a : T ⟶ T) (M : Modules l T)
    (θ θ' : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (b : PadicAlgCl l) (hθ : θ'.hom = b • θ.hom) (n : ℕ) :
    (iterate l a M θ' n).hom = b ^ (n + 1) • (iterate l a M θ n).hom := by
  unfold iterate
  apply isoChain_scalar
  · simp only [evaluateInitial, Iso.trans_hom, hθ, Linear.comp_smul]
  · intro k
    unfold iterateStep evaluateStep
    simp only [Iso.trans_hom, Functor.mapIso_hom, hθ, Functor.map_smul,
      Linear.comp_smul]

set_option maxHeartbeats 200000 in
-- Concrete module-object comparisons require a larger elaboration budget.
private theorem operator_scalar (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ θ' : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (b : PadicAlgCl l) (hθ : θ'.hom = b • θ.hom)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    operator l D a M θ' z n h = ULift.up.{u + 1} (b ^ (n + 1)) • operator l D a M θ z n h := by
  let L := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let c := CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
    (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
      (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x ≫ (c.app M).hom ≫ L.map (iterate l a M θ' n).hom =
    unitScalars l _ (b ^ (n + 1)) ≫
      (x ≫ (c.app M).hom ≫ L.map (iterate l a M θ n).hom)
  rw [iterate_scalar l a M θ θ' b hθ n, Functor.map_smul, unitScalars_smul_id]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]

private theorem pointComparison_naturality (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (a : T ⟶ T)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (M N : Modules l T) (f : M ⟶ N) :
    let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n)
    let L := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
    let c := CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h
    (c.app M).hom ≫ L.map (P.map f) = L.map f ≫ (c.app N).hom := by
  dsimp only
  simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
    Functor.id_map, Iso.app_hom] using
    ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (localPositivePower (frobeniusPointIso D).hom n))
      (localPositivePower a n) h).hom.naturality f).symm

set_option maxHeartbeats 200000 in
-- Concrete module-object comparisons require a larger elaboration budget.
private theorem operator_naturality (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    operator l D a M θ z n h ≫
        (pointSections l D.k).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) =
      (pointSections l D.k).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) ≫
        operator l D a N η z n h := by
  let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n)
  let L := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z
  let c := CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
    (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
      (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h
  have hc := pointComparison_naturality l D a z n h M N f
  have hi := iterate_naturality l a M N θ η f hf n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (x ≫ (c.app M).hom ≫ L.map (iterate l a M θ n).hom) ≫ L.map f =
    (x ≫ L.map f) ≫ (c.app N).hom ≫ L.map (iterate l a N η n).hom
  calc
    (x ≫ (c.app M).hom ≫ L.map (iterate l a M θ n).hom) ≫ L.map f =
        x ≫ (c.app M).hom ≫ L.map ((iterate l a M θ n).hom ≫ f) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = x ≫ (c.app M).hom ≫ L.map (P.map f ≫ (iterate l a N η n).hom) := by rw [hi]
    _ = (x ≫ ((c.app M).hom ≫ L.map (P.map f))) ≫ L.map (iterate l a N η n).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (x ≫ (L.map f ≫ (c.app N).hom)) ≫ L.map (iterate l a N η n).hom := by rw [hc]
    _ = (x ≫ L.map f) ≫ (c.app N).hom ≫ L.map (iterate l a N η n).hom := by
      simp only [Category.assoc]

set_option maxHeartbeats 200000 in
-- Concrete module-object comparisons require a larger elaboration budget.
private theorem constantScalar_hom (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (b : (PadicAlgCl l)ˣ) :
    (CondensedRing.ConstantWeil.scalar l X b).hom = unitScalars l X b := by
  unfold CondensedRing.ConstantWeil.scalar CondensedRing.ConstantWeil.coefficientScalar
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change ((upperStarFromPoint X).mapMod (Profinite.padicAlgClRingObj l)).map
    (Mod.regularEndRingHom (Profinite.PadicAlgCl.constRingHom l b)) = _
  exact Functor.mapMod_map_regularEndRingHom _ _ _

set_option maxHeartbeats 200000 in
-- Concrete module-object comparisons require a larger elaboration budget.
private theorem twist_unitor_compatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hEll : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (F : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius X₀).hom).map (ρ_ F.obj.carrier).hom ≫
      (F.obj.str ≪≫ scalarIso l b F.obj.carrier).hom =
    (CondensedRing.ConstantWeil.twist l D X₀ hEll b F).obj.str.hom ≫
      (ρ_ F.obj.carrier).hom := by
  simp only [CondensedRing.ConstantWeil.twist, CondensedRing.ConstantWeil.line,
    CondensedRing.ConstantWeil.lineModule, CondensedRing.StrictWeilCondensed.unitWeilModule,
    CategoryTheory.Endofunctor.IsoAlgebra.mk_carrier,
    CategoryTheory.Endofunctor.IsoAlgebra.mk_str, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, constantScalar_hom]
  simpa only [scalarIso_hom_formula, Category.assoc] using
    unit_twist_equivariance
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
      F.obj.carrier F.obj.str (unitScalars l (D.geometricFiber X₀).left b)

-- Prevent local-operator expressions from expanding during composition of their identities.
attribute [local irreducible] operator pointSections

-- Keep the naturality/scalar composition abstract to avoid unfolding the concrete tensor.
set_option maxHeartbeats 200000 in
-- Concrete module-object comparisons require a larger elaboration budget.
private theorem operator_rescale_naturality
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η η' : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (b : PadicAlgCl l) (hη : η'.hom = b • η.hom) (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η'.hom =
      θ.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    let fz : fibre l D M z ⟶ fibre l D N z := (pointSections l D.k).map
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f)
    operator l D a M θ z n h ≫ fz =
      fz ≫ (ULift.up.{u + 1} (b ^ (n + 1)) • operator l D a N η z n h) := by
  have hn := operator_naturality l D a M N θ η' f hf z n h
  have hs := operator_scalar l D a N η η' b hη z n h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (congrArg (fun t : fibre l D M z ⟶ fibre l D N z ↦ t x) hn).trans
    (congrArg (fun t : fibre l D N z ⟶ fibre l D N z ↦
      t ((pointSections l D.k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) x)) hs)

/-- The actual right-unit isomorphism on native stalks, with its source fixed explicitly. -/
@[irreducible] private def twistStalkIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hEll : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (F : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    fibre l D (CondensedRing.ConstantWeil.twist l D X₀ hEll b F).obj.carrier z ≅
      fibre l D F.obj.carrier z :=
  (pointSections l D.k).mapIso
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso (ρ_ F.obj.carrier))

set_option maxHeartbeats 200000 in
-- Concrete module-object comparisons require a larger elaboration budget.
private theorem twist_operator
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hEll : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (F : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (n : ℕ)
    (h : z ≫ localPositivePower (D.geometricFrobenius X₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    let T := (CondensedRing.ConstantWeil.twist l D X₀ hEll b F).obj
    let e := twistStalkIso D l hEll X₀ F b z
    operator l D (D.geometricFrobenius X₀).hom T.carrier T.str z n h ≫ e.hom =
      e.hom ≫ (ULift.up.{u + 1} ((b : PadicAlgCl l) ^ (n + 1)) •
        operator l D (D.geometricFrobenius X₀).hom F.obj.carrier F.obj.str z n h) := by
  unfold twistStalkIso
  have hs : (F.obj.str ≪≫ scalarIso l b F.obj.carrier).hom =
      (b : PadicAlgCl l) • F.obj.str.hom := by
    simp only [Iso.trans_hom, scalarIso_hom, Linear.comp_smul, Category.comp_id]
  exact operator_rescale_naturality l D (D.geometricFrobenius X₀).hom
    (CondensedRing.ConstantWeil.twist l D X₀ hEll b F).obj.carrier F.obj.carrier
    (CondensedRing.ConstantWeil.twist l D X₀ hEll b F).obj.str F.obj.str
    (F.obj.str ≪≫ scalarIso l b F.obj.carrier) b hs (ρ_ F.obj.carrier).hom
    (twist_unitor_compatibility D l hEll X₀ F b) z n h

-- Restore the ordinary fibre interface for the vectorwise purity argument.
attribute [local semireducible] operator pointSections

private theorem twist_norm {K : Type*} [Field K] (iota : K →+* ℂ)
    (q : ℕ) (hq : 1 < q) (m : ℕ) (w c : ℝ) (b : Kˣ) (β : K)
    (hb : 2 * Real.logb q ‖iota b‖ = c)
    (hα : ‖iota (β / (b : K) ^ m)‖ = ((q : ℝ) ^ m) ^ (w / 2)) :
    ‖iota β‖ = ((q : ℝ) ^ m) ^ ((w + c) / 2) := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hnorm : ‖iota b‖ = (q : ℝ) ^ (c / 2) := by
    rw [← hb, mul_div_cancel_left₀ _ two_ne_zero,
      Real.rpow_logb (by positivity) hq'.ne'
        (norm_pos_iff.mpr ((map_ne_zero iota).mpr b.ne_zero))]
  have hmul : β = (b : K) ^ m * (β / (b : K) ^ m) := by
    field_simp [pow_ne_zero m b.ne_zero]
  calc
    ‖iota β‖ = ‖iota ((b : K) ^ m * (β / (b : K) ^ m))‖ := congrArg (fun t ↦ ‖iota t‖) hmul
    _ = ((q : ℝ) ^ m) ^ ((w + c) / 2) := by
      rw [map_mul, norm_mul, map_pow, norm_pow, hnorm, hα]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast (q : ℝ), ← Real.rpow_mul (by positivity),
        ← Real.rpow_add (by positivity), ← Real.rpow_mul (by positivity)]
      congr 1
      ring

private theorem pure_of_comparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (F G : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) (w c : ℝ)
    (hF : Pure D l X₀ F iota w) (b : (PadicAlgCl l)ˣ)
    (hb : 2 * Real.logb (Nat.card D.k₀) ‖iota b‖ = c)
    (hcomp : ∀ x i hi, ∃ e :
      fibre l D G.carrier (localClosedPoint D X₀ x i hi) ≅
        fibre l D F.carrier (localClosedPoint D X₀ x i hi),
      closedOperator D l X₀ G x i hi ≫ e.hom =
        e.hom ≫ (ULift.up.{u + 1} ((b : PadicAlgCl l) ^ localClosedPointDegree D X₀ x) •
          closedOperator D l X₀ F x i hi)) : Pure D l X₀ G iota (w + c) := by
  intro x i hi β hβ
  let := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  have : Module.Finite D.k₀ (X₀.left.residueField x.val) :=
    (closedPoint_iff_residueField_trdeg_zero_and_finite X₀.hom x.val).2.1.mp x.prop
  let m := localClosedPointDegree D X₀ x
  let a : ULift.{u + 1} (PadicAlgCl l) := ULift.up ((b : PadicAlgCl l) ^ m)
  obtain ⟨e, hconj⟩ := hcomp x i hi
  have ha : a ≠ 0 := by
    change ULift.up ((b : PadicAlgCl l) ^ m) ≠ (0 : ULift (PadicAlgCl l))
    exact fun h ↦ pow_ne_zero m b.ne_zero (congrArg ULift.down h)
  have hα : Module.End.HasEigenvalue (closedOperator D l X₀ F x i hi).hom (β / a) := by
    obtain ⟨v, hv⟩ := hβ.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e.hom v)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · have key := congrArg
        (fun t : fibre l D G.carrier (localClosedPoint D X₀ x i hi) ⟶
          fibre l D F.carrier (localClosedPoint D X₀ x i hi) ↦ t v) hconj
      change e.hom ((closedOperator D l X₀ G x i hi).hom v) =
        a • (closedOperator D l X₀ F x i hi).hom (e.hom v) at key
      rw [hv.apply_eq_smul, map_smul] at key
      have hk := congrArg (fun t ↦ a⁻¹ • t) key
      simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul, div_eq_mul_inv, mul_comm]
        using hk.symm
    · intro hz
      apply hv.2
      exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance (by simpa using hz)
  have hnormα := hF x i hi (β / a) hα
  have hcard : Nat.card (X₀.left.residueField x.val) = Nat.card D.k₀ ^ m := by
    exact Module.natCard_eq_pow_finrank
  rw [hcard, Nat.cast_pow] at hnormα ⊢
  exact twist_norm iota (Nat.card D.k₀) Finite.one_lt_card m w c b β.down hb hnormα


attribute [local irreducible] CondensedRing.ConstantWeil.twist

private theorem twist_closed_comparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hEll : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (F : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (b : (PadicAlgCl l)ˣ)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    closedOperator D l X₀ (CondensedRing.ConstantWeil.twist l D X₀ hEll b F).obj x i hi ≫
        (twistStalkIso D l hEll X₀ F b (localClosedPoint D X₀ x i hi)).hom =
      (twistStalkIso D l hEll X₀ F b (localClosedPoint D X₀ x i hi)).hom ≫
        (ULift.up.{u + 1} ((b : PadicAlgCl l) ^ localClosedPointDegree D X₀ x) •
          closedOperator D l X₀ F.obj x i hi) := by
  let := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  have : Module.Finite D.k₀ (X₀.left.residueField x.val) :=
    (closedPoint_iff_residueField_trdeg_zero_and_finite X₀.hom x.val).2.1.mp x.prop
  have hm : 1 ≤ localClosedPointDegree D X₀ x := Module.finrank_pos
  have hc := twist_operator D l hEll X₀ F b (localClosedPoint D X₀ x i hi)
    (localClosedPointDegree D X₀ x - 1) (localClosedPoint_return D X₀ x i hi)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  have hv := congrArg
    (fun t : fibre l D (CondensedRing.ConstantWeil.twist l D X₀ hEll b F).obj.carrier
        (localClosedPoint D X₀ x i hi) ⟶
      fibre l D F.obj.carrier (localClosedPoint D X₀ x i hi) ↦ t v) hc
  simpa only [closedOperator, Nat.sub_add_cancel hm] using hv

set_option maxHeartbeats 200000 in
-- The local comparison passes through the concrete condensed module category.
/-- Tensoring a punctually pure condensed Weil module with the constant line rescales
local degree-`m` Frobenius by `b^m`, so its weight is shifted by `c`.

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/
`sk-r-real-linear/lem-wf-constant-twist-weight.proof.md`, first sentence and
norm computation (blueprint: lem-wf-constant-twist-weight).
Proof: the condensed constant-twist stalk comparison identifies every local
operator with `b^m` times the original one. Eigenvalues therefore become
`b^m * α`; the purity hypothesis gives norm `q_y^(w/2)`, while
`2 * log_q ‖ι b‖ = c` gives `‖ι b‖ = q^(c/2)`. Since `q_y = q^m`,
the resulting norm is `q_y^((w+c)/2)` at every closed point. -/
theorem Pure.constantTwist
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hEll : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (F : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (iota : PadicAlgCl l →+* ℂ) (w c : ℝ)
    (hF : Pure D l X₀ F.obj iota w)
    (b : (PadicAlgCl l)ˣ)
    (hb : 2 * Real.logb (Nat.card D.k₀) ‖iota b‖ = c) :
    Pure D l X₀ (CondensedRing.ConstantWeil.twist l D X₀ _hEll b F).obj iota (w + c) := by
  apply pure_of_comparison D l X₀ F.obj
    (CondensedRing.ConstantWeil.twist l D X₀ _hEll b F).obj iota w c hF b hb
  intro x i hi
  exact ⟨twistStalkIso D l _hEll X₀ F b (localClosedPoint D X₀ x i hi),
    twist_closed_comparison D l _hEll X₀ F b x i hi⟩

end WeilConjectures.NativeL2
