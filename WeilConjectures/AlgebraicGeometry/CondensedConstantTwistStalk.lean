/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion

/-! # The condensed constant Weil line and its local Frobenius

Source: latest blueprint, sec-purity-real-sheaves/sk-r-real-linear/
lem-wf-constant-twist-weight.proof.md, first sentence
(blueprint: lem-wf-condensed-constant-twist-stalk).

All modules and pullbacks here are ordinary condensed module objects. The tensor is
relative to the pulled-back coefficient ring. The stalk is point sections of geometric
pullback, and its operator uses the recorded positive-iterate and semilinear return.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedModule.ConstantTwist

/-- Constant scalars acting on the regular module via the pulled-back global section.
Source: latest blueprint constant-line construction and coefficient naturality
(blueprint: lem-wf-condensed-constant-twist-stalk). -/
def unitScalars (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    PadicAlgCl l →+* End (𝟙_ (Modules l X)) :=
  (Mod.regularEndRingHom.comp (MonObj.Γ.mapFunctor (upperStarFromPoint X))).comp
    (Profinite.PadicAlgCl.constRingHom l)

/-- Multiplication by the unit b, using the regular-module scalar and the left unitor.
This supplies the actual inverse from b inverse, with no existence choice.
Source: latest blueprint constant line B_b=(R,be)
(blueprint: lem-wf-condensed-constant-twist-stalk). -/
def scalarIso (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (b : (PadicAlgCl l)ˣ) (M : Modules l X) : M ≅ M :=
  (λ_ M).symm ≪≫ (tensorRight M).mapIso
    (Aut.unitsEndEquivAut _ (Units.map (unitScalars l X).toMonoidHom b)) ≪≫ λ_ M

/-- The same module, with its structure multiplied by b.
Source: latest blueprint constant-twist local-Frobenius sentence
(blueprint: lem-wf-condensed-constant-twist-stalk). -/
def rescale (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {g : X ≅ X}
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g)
    (b : (PadicAlgCl l)ˣ) :
    CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk F.carrier (F.str ≪≫ scalarIso l b F.carrier)

/-- The constant Weil line with the canonical coefficient-unit comparison multiplied by b.
Source: latest blueprint constant line B_b=(R,be)
(blueprint: lem-wf-condensed-constant-twist-stalk). -/
def line (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} (g : X ≅ X)
    (b : (PadicAlgCl l)ˣ) :
    CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g :=
  rescale l (CondensedRing.StrictWeil.unitWeilModule (Profinite.padicAlgClRingObj l) g) b

/-- The relative tensor with the constant line, with inverse tensorator followed by phi tensor be.
Source: latest blueprint constant-line tensor formula
(blueprint: lem-wf-condensed-constant-twist-stalk). -/
def tensorLine (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {g : X ≅ X}
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g)
    (b : (PadicAlgCl l)ˣ) :
    CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (F.carrier ⊗ (line l g b).carrier)
    ((Functor.Monoidal.μIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)
      F.carrier (line l g b).carrier).symm ≪≫ tensorIso F.str (line l g b).str)

/-- The canonical linear stalk isomorphism induced by the ordinary right unitor.
Source: latest blueprint stalk convention Gamma(s,ybar^*M)
(blueprint: lem-wf-condensed-constant-twist-stalk). -/
def stalkUnitor (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} (M : Modules l X) (z : Spec (.of D.k) ⟶ X) :
    fibre l D (M ⊗ 𝟙_ (Modules l X)) z ≅ fibre l D M z :=
  (CondensedRing.pointSections l D.k).mapIso
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso (ρ_ M))

/-- The existing derived-to-ordinary tensor comparison at M[0] and R[0].
Source: latest blueprint degree-zero derived tensor and regular-module flatness
(blueprint: lem-wf-condensed-constant-twist-stalk). -/
def derivedUnitComparison (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} (M : Modules l X) :=
  Functor.LaxMonoidal.μ DerivedCategory.Qh
    ((HomotopyCategory.quotient (Modules l X) (.up ℤ)).obj
      ((CochainComplex.singleFunctor (Modules l X) 0).obj M))
    ((HomotopyCategory.quotient (Modules l X) (.up ℤ)).obj
      ((CochainComplex.singleFunctor (Modules l X) 0).obj (𝟙_ (Modules l X))))

private def coefficientScalars (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    PadicAlgCl l →+* MonObj.Γ (padicAlgClRingObj X l) :=
  (MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
    (Profinite.PadicAlgCl.constRingHom l)

@[instance_reducible] private def linearModules (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Linear (PadicAlgCl l) (Modules l X) :=
  Mod.linearOfRingHom (coefficientScalars l X)

attribute [local instance] linearModules

private theorem linearLowerStar (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).Linear (PadicAlgCl l) := by
  apply Mod.linear_mapMod_comp_comap
    (ProEtale.lowerStar Ab.{u + 1} f) (condensedPushforwardHom _ f)
    (coefficientScalars l X) (coefficientScalars l Y)
  intro a
  simp only [coefficientScalars, RingHom.comp_apply, MonObj.Γ.mapFunctor_hom,
    condensedPushforwardHom, Adjunction.unitAlgHom, Category.assoc]
  exact Adjunction.ε_comp_map_comp_unit_app_comp_map
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (upperStarFromPoint Y) (upperStarFromPoint X) (upperStarFromPointComp f).hom
    ((Profinite.PadicAlgCl.constRingHom l a).hom)

attribute [local instance] linearLowerStar

private theorem linearUpperStar (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).Linear (PadicAlgCl l) :=
  (CondensedRing.upperStarLowerStarAdjunction _ f).left_adjoint_linear

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

private theorem scalarIso_unit (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (b : (PadicAlgCl l)ˣ) :
    (scalarIso l b (𝟙_ (Modules l X))).hom = unitScalars l X b := by
  simp only [scalarIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (λ_ (𝟙_ (Modules l X))).inv ≫ unitScalars l X b ▷ _ ≫
    (λ_ (𝟙_ (Modules l X))).hom = _
  rw [unitors_equal, unitors_inv_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]

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

private theorem constructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hs (T : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
      (e : A ≅ B) (hA : IsFiniteConstantStratified Λ T A) :
      IsFiniteConstantStratified Λ T B := by
    obtain ⟨S, hS⟩ := hA
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨𝒰, h𝒰⟩ := hS a
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)).symm ≪≫ eP⟩⟩
  classical
  unfold IsConstantModelConstructible at *
  split_ifs at * with h
  · exact hs X e hM
  · exact fun U hU ↦ hs U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

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

private theorem operator_scalar (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ θ' : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (b : PadicAlgCl l) (hθ : θ'.hom = b • θ.hom)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    operator l D a M θ' z n h = ULift.up.{v} (b ^ (n + 1)) • operator l D a M θ z n h := by
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
        (CondensedRing.pointSections l D.k).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) =
      (CondensedRing.pointSections l D.k).map
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

private theorem tensorLine_unitor_compatibility (l : ℕ) [Fact l.Prime]
    {X : Scheme.{u}} {g : X ≅ X}
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g)
    (b : (PadicAlgCl l)ˣ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom).map (ρ_ F.carrier).hom ≫
        (rescale l F b).str.hom = (tensorLine l F b).str.hom ≫ (ρ_ F.carrier).hom := by
  simp only [tensorLine, rescale, line, CondensedRing.StrictWeil.unitWeilModule,
    CategoryTheory.Endofunctor.IsoAlgebra.mk_carrier,
    CategoryTheory.Endofunctor.IsoAlgebra.mk_str, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, scalarIso_unit]
  simpa only [scalarIso_hom_formula, Category.assoc] using
    unit_twist_equivariance
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)
      F.carrier F.str (unitScalars l X b)

private theorem tensorLine_weil_iso (l : ℕ) [Fact l.Prime]
    {X : Scheme.{u}} {g : X ≅ X}
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g)
    (b : (PadicAlgCl l)ˣ) :
    ∃ e : tensorLine l F b ≅ rescale l F b, e.hom.hom.f = (ρ_ F.carrier).hom :=
  ⟨CategoryTheory.Endofunctor.IsoAlgebra.isoMk (ρ_ F.carrier)
    (tensorLine_unitor_compatibility l F b), rfl⟩

private theorem tensorLine_constructible (l : ℕ) [Fact l.Prime]
    {X : Scheme.{u}} {g : X ≅ X}
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g)
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X F.carrier)
    (b : (PadicAlgCl l)ˣ) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X
      (tensorLine l F b).carrier := by
  simp only [tensorLine, line, rescale, CondensedRing.StrictWeil.unitWeilModule,
    CategoryTheory.Endofunctor.IsoAlgebra.mk_carrier]
  exact constructible_of_iso (Profinite.padicAlgClRingObj l) X (ρ_ F.carrier).symm hF

private theorem derivedUnitComparison_isIso (l : ℕ) [Fact l.Prime]
    {X : Scheme.{u}} (M : Modules l X) : IsIso (derivedUnitComparison l M) := by
  unfold derivedUnitComparison
  apply DerivedCategory.isIso_μ_Qh_of_kFlat_right
  apply (HomotopyCategory.kFlat_quotient_obj_iff _).2
  exact (CochainComplex.kFlat_single_obj_iff_flat _ 0).2
    (ObjectProperty.prop_unit ObjectProperty.flat)

private theorem tensorLine_operator (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} {g : X ≅ X}
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l) g)
    (b : (PadicAlgCl l)ˣ) (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    operator l D g.hom (tensorLine l F b).carrier (tensorLine l F b).str z n h ≫
        (stalkUnitor l D F.carrier z).hom =
      (stalkUnitor l D F.carrier z).hom ≫
        (ULift.up.{v} ((b : PadicAlgCl l) ^ (n + 1)) •
          operator l D g.hom F.carrier F.str z n h) := by
  have hs : (F.str ≪≫ scalarIso l b F.carrier).hom =
      (b : PadicAlgCl l) • F.str.hom := by
    simp only [Iso.trans_hom, scalarIso_hom, Linear.comp_smul, Category.comp_id]
  have hn := operator_naturality l D g.hom
    (tensorLine l F b).carrier (rescale l F b).carrier
    (tensorLine l F b).str (rescale l F b).str (ρ_ F.carrier).hom
    (tensorLine_unitor_compatibility l F b) z n h
  simp only [rescale, CategoryTheory.Endofunctor.IsoAlgebra.mk_carrier,
    CategoryTheory.Endofunctor.IsoAlgebra.mk_str] at hn
  rw [operator_scalar.{u, v} l D g.hom F.carrier F.str
    (F.str ≪≫ scalarIso l b F.carrier) b hs] at hn
  simpa only [stalkUnitor, Functor.mapIso_hom] using hn

/-- Tensoring with the condensed constant Weil line identifies the structure with b phi,
and the induced canonical linear stalk isomorphism rescales degree-m Frobenius by b^m.
The regular module is flat and its degree-zero derived tensor comparison is invertible.
Source: latest blueprint, lem-wf-constant-twist-weight.proof.md, first sentence
(blueprint: lem-wf-condensed-constant-twist-stalk).

Proof: (1) coefficient comparison is natural for multiplication by b, so every module
pullback and its composition comparisons preserve that scalar. (2) The balanced tensor
relations identify the right unitor with v tensor r mapping to rv, inverse v tensor 1.
Tensoring with the regular module is the identity, hence exact and flat; the K-flat
comparison therefore computes the same degree-zero tensor. (3) Right-unit coherence of
monoidal pullback and naturality of the unitor give u psi = (b phi) P(u), also for the
inverse unitor. The underlying tensor is thus isomorphic to the constructible M.
(4) Induct on the iterate: (b phi)^[n] = b^n phi^[n], including the identity at zero.
Iterating the unitor equation gives its equivariance for every iterate. (5) Apply the
geometric-point pullback and point sections, then the canonical point-return transport.
That transport is linear, natural in the module, and independent of phi. Thus it
intertwines the tensor operator with b^m times the original operator. Point coefficients
identify the scalar field with Omega; no field Frobenius is applied to b. -/
theorem constant_twist_stalk (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hEll : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀))
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left F.carrier) (b : (PadicAlgCl l)ˣ) :
    (∃ e : tensorLine l F b ≅ rescale l F b, e.hom.hom.f = (ρ_ F.carrier).hom) ∧
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left (tensorLine l F b).carrier ∧
    ObjectProperty.flat (𝟙_ (Modules l (D.geometricFiber X₀).left)) ∧
    IsIso (derivedUnitComparison l F.carrier) ∧
    ∀ (y : {y : X₀.left // y ∈ closedPoints X₀.left})
      (ι : X₀.left.residueField y.val →+* D.k)
      (hι : ι.comp (X₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
      operator l D (D.geometricFrobenius X₀).hom (tensorLine l F b).carrier
          (tensorLine l F b).str (localClosedPoint D X₀ y ι hι)
          (localClosedPointDegree D X₀ y - 1) (localClosedPoint_return D X₀ y ι hι) ≫
        (stalkUnitor l D F.carrier (localClosedPoint D X₀ y ι hι)).hom =
      (stalkUnitor l D F.carrier (localClosedPoint D X₀ y ι hι)).hom ≫
        (ULift.up ((b : PadicAlgCl l) ^ localClosedPointDegree D X₀ y) •
          operator l D (D.geometricFrobenius X₀).hom F.carrier F.str
            (localClosedPoint D X₀ y ι hι) (localClosedPointDegree D X₀ y - 1)
            (localClosedPoint_return D X₀ y ι hι)) := by
  refine ⟨tensorLine_weil_iso l F b, tensorLine_constructible l F hF b,
    ObjectProperty.prop_unit ObjectProperty.flat, derivedUnitComparison_isIso l F.carrier, ?_⟩
  intro y ι hι
  simpa only [Nat.sub_add_cancel (localClosedPointDegree_pos D X₀ y)] using
    tensorLine_operator l D F b (localClosedPoint D X₀ y ι hι)
      (localClosedPointDegree D X₀ y - 1) (localClosedPoint_return D X₀ y ι hι)

end WeilConjectures.CondensedModule.ConstantTwist
