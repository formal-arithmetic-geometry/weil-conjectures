/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FieldDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TraceShiftUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.TraceShiftDecomposition
public import WeilConjectures.LinearAlgebra.TraceLongExactSequence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
public import WeilConjectures.TraceFormula.Basic

/-!
# Traces on the point category over a separably closed field

Let `k` be a separably closed field and `s = Spec k`. Evaluation at the geometric point identifies
the bounded constructible derived category `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` with the bounded derived category of
finite-dimensional `ℚ̄_ℓ`-vector spaces (blueprint `def-weil-finite-coefficient-point`,
`ProEtale.CondensedRing.exists_fiberFunctor_point`). Consequently every object of
`Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a finite direct sum of shifts of the unit.

This file shows that the categorical trace on `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is the supertrace on the graded
spaces `Hⁿ(P) = Hom(𝟙⟦n⟧, P)`, and deduces that the trace is additive along every endomorphism of
a distinguished triangle (blueprint `prop-trf-trace-formal-laws`, items (2) and (4)): over a field
the filtered origin of the endomorphism is not needed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

example : MonoidalPreadditive (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  inferInstance

example (n : ℤ) :
    (shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).Additive :=
  inferInstance

/-- **The point category, evaluated** (blueprint `def-weil-finite-coefficient-point`): for `k`
separably closed, evaluation at the geometric point `s = Spec k` is an exact equivalence
`Fib_s : Dᵇc(s)⟦ℚ̲̄_ℓ⟧ ≃ Dᵇ_fd(ℚ̄_ℓ)` onto the bounded complexes of `ℚ̄_ℓ`-vector spaces with
finite-dimensional cohomology, with quasi-inverse `P ↦ ℚ̲̄_ℓ,s ⊗ P`; in particular it sends the
unit `ℚ̲̄_ℓ,s` to `ℚ̄_ℓ[0]`. -/
theorem exists_fiberFunctor_point :
    ∃ (G : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
        DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)))) (_ : G.CommShift ℤ),
      G.Additive ∧ Nonempty G.FullyFaithful ∧
      (∀ P, DerivedCategory.boundedFiniteCohomology _ (G.obj P)) ∧
      (∀ M, DerivedCategory.boundedFiniteCohomology _ M → ∃ P, Nonempty (G.obj P ≅ M)) ∧
      Nonempty (G.obj (𝟙_ _) ≅ (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ)))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

namespace DerivedCategory

variable {F : Type (u + 1)} [Field F]

/-- A retract of a bounded complex with finite-dimensional cohomology is again bounded with
finite-dimensional cohomology. -/
lemma boundedFiniteCohomology_of_retract {X Y : DerivedCategory (ModuleCat.{u + 1} F)}
    (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X) (hY : boundedFiniteCohomology F Y) :
    boundedFiniteCohomology F X := by
  have hz (n : ℤ) (hn : IsZero ((homologyFunctor _ n).obj Y)) :
      IsZero ((homologyFunctor _ n).obj X) := by
    rw [IsZero.iff_id_eq_zero, ← (homologyFunctor _ n).map_id, ← h, Functor.map_comp,
      hn.eq_of_tgt ((homologyFunctor _ n).map i) 0, zero_comp]
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hfin⟩ := hY
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun n ↦ ?_⟩
  · have ha' := (isGE_iff Y a).1 ha
    exact (isGE_iff X a).2 fun n hn ↦ hz n (ha' n hn)
  · have hb' := (isLE_iff Y b).1 hb
    exact (isLE_iff X b).2 fun n hn ↦ hz n (hb' n hn)
  · have := hfin n
    refine Module.Finite.of_surjective ((homologyFunctor _ n).map p).hom fun x ↦
      ⟨((homologyFunctor _ n).map i).hom x, ?_⟩
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, h, CategoryTheory.Functor.map_id]
    rfl

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

/-- Over a separably closed field, every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a finite direct sum of
shifts of the unit: transported along the fibre functor of `exists_fiberFunctor_point`, this is
the splitting of bounded complexes of vector spaces
(`DerivedCategory.prop_of_boundedFiniteCohomology_of_field`). -/
theorem nonempty_shiftDecomposition_point
    (P : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (ShiftDecomposition (𝟙_ _) P) := by
  obtain ⟨G, _, hadd, ⟨hG⟩, hbfc, hess, ⟨e₀⟩⟩ := exists_fiberFunctor_point ℓ k
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  let F := ULift.{u + 1} (PadicAlgCl ℓ)
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} F)) := fun Y ↦
    DerivedCategory.boundedFiniteCohomology F Y →
      ∀ P, (G.obj P ≅ Y) → Nonempty (ShiftDecomposition (𝟙_ _) P)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun {Y Y'} e hY hY' P e' ↦
    hY ((DerivedCategory.boundedFiniteCohomology F).prop_of_iso e.symm hY') P (e' ≪≫ e.symm)⟩
  refine DerivedCategory.prop_of_boundedFiniteCohomology_of_field Q ?_ ?_ ?_ ?_ (hbfc P) (hbfc P)
    P (Iso.refl _)
  · intro Y hY _ P e
    refine ⟨ShiftDecomposition.ofIsZero ?_⟩
    rw [IsZero.iff_id_eq_zero]
    exact hG.map_injective (by rw [G.map_id, G.map_zero]; exact (hY.of_iso e).eq_of_src _ _)
  · intro X Y hX hY hXY P e
    have hX' := DerivedCategory.boundedFiniteCohomology_of_retract biprod.inl biprod.fst
      biprod.inl_fst hXY
    have hY' := DerivedCategory.boundedFiniteCohomology_of_retract biprod.inr biprod.snd
      biprod.inr_snd hXY
    obtain ⟨PX, ⟨eX⟩⟩ := hess X hX'
    obtain ⟨PY, ⟨eY⟩⟩ := hess Y hY'
    obtain ⟨DX⟩ := hX hX' PX eX
    obtain ⟨DY⟩ := hY hY' PY eY
    refine ⟨DX.sum DY (hG.preimage (eX.hom ≫ biprod.inl ≫ e.inv))
      (hG.preimage (eY.hom ≫ biprod.inr ≫ e.inv)) (hG.preimage (e.hom ≫ biprod.fst ≫ eX.inv))
      (hG.preimage (e.hom ≫ biprod.snd ≫ eY.inv)) ?_ ?_ ?_ ?_ ?_⟩
    · apply hG.map_injective
      simp only [G.map_add, G.map_comp, hG.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        G.map_id]
      rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp, Iso.hom_inv_id]
    all_goals
      apply hG.map_injective
      simp only [G.map_add, G.map_comp, hG.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        G.map_id, G.map_zero, biprod.inl_fst_assoc, biprod.inr_snd_assoc, biprod.inl_snd_assoc,
        biprod.inr_fst_assoc, Iso.hom_inv_id, zero_comp, comp_zero]
  · intro X n hX hXn P e
    let P' := (shiftFunctor _ (-n)).obj P
    let e' : G.obj P' ≅ X := (G.commShiftIso (-n)).app P ≪≫ (shiftFunctor _ (-n)).mapIso e ≪≫
      (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app X
    obtain ⟨D⟩ := hX ((DerivedCategory.boundedFiniteCohomology F).prop_of_iso e' (hbfc P')) P' e'
    exact ⟨(D.shift n).ofIso ((shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).app P)⟩
  · intro _ P e
    exact ⟨(ShiftDecomposition.self _).ofIso (hG.preimageIso (e₀ ≪≫ e.symm))⟩

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The abelian category of `ℚ̲̄_ℓ`-module objects on the pro-étale site of the point
`s = Spec k`, the ambient category of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
abbrev PointMod : Type _ :=
  Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Ambient

/-- The shifted unit `𝟙⟦n⟧` of `D(Mod_{ℚ̲̄_ℓ,s})`. -/
noncomputable abbrev shiftedUnit (n : ℤ) : DerivedCategory (PointMod ℓ k) :=
  (shiftFunctor (DerivedCategory (PointMod ℓ k)) n).obj (𝟙_ _)

/-- The scalars `ℚ̄_ℓ` acting on the unit of `D(Mod_{ℚ̲̄_ℓ,s})`. -/
noncomputable def pointScalar : PadicAlgCl ℓ →+* End (𝟙_ (DerivedCategory (PointMod ℓ k))) :=
  ((boundedConstructible _).ι.mapEndRingHom
    (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))).comp
    (padicAlgClUnitEndRingHom ℓ (point k))

lemma bijective_pointScalar [IsSepClosed k] : Function.Bijective (pointScalar ℓ k) :=
  ((ObjectProperty.fullyFaithfulι _).map_bijective _ _).comp
    (bijective_padicAlgClUnitEndRingHom_point ℓ k)

/-- The scalars acting on the shifted unit `𝟙⟦n⟧` by precomposition. -/
noncomputable def shiftedUnitScalar (n : ℤ) :
    PadicAlgCl ℓ →+* (End (shiftedUnit ℓ k n))ᵐᵒᵖ :=
  (((shiftFunctor (DerivedCategory (PointMod ℓ k)) n).mapEndRingHom _).comp
    (pointScalar ℓ k)).toOpposite fun x y ↦ by
      unfold Commute SemiconjBy
      rw [← map_mul, mul_comm, map_mul]

/-- The graded pieces `Hⁿ(Y) = Hom(𝟙⟦n⟧, Y)` of `Y ∈ D(Mod_{ℚ̲̄_ℓ,s})`, as `ℚ̄_ℓ`-vector
spaces. -/
noncomputable def gradedHom (n : ℤ) : DerivedCategory (PointMod ℓ k) ⥤ ModuleCat (PadicAlgCl ℓ) :=
  preadditiveCoyonedaObj (shiftedUnit ℓ k n) ⋙
    ModuleCat.restrictScalars (shiftedUnitScalar ℓ k n)

instance (n : ℤ) : (gradedHom ℓ k n).Additive := by
  unfold gradedHom
  infer_instance

lemma gradedHom_map_apply (n : ℤ) {Y Y' : DerivedCategory (PointMod ℓ k)} (f : Y ⟶ Y')
    (x : shiftedUnit ℓ k n ⟶ Y) : ((gradedHom ℓ k n).map f).hom x = x ≫ f :=
  rfl

lemma gradedHom_smul (n : ℤ) (Y : DerivedCategory (PointMod ℓ k)) (c : PadicAlgCl ℓ)
    (x : (gradedHom ℓ k n).obj Y) :
    c • x = ((shiftFunctor (DerivedCategory (PointMod ℓ k)) n).map (pointScalar ℓ k c) ≫ x :
      shiftedUnit ℓ k n ⟶ Y) :=
  rfl

end Ambient

end AlgebraicGeometry.ProEtale.CondensedRing

namespace DerivedCategory

variable {F : Type (u + 1)} [Field F]

/-- Morphisms `M[-b] ⟶ Z` vanish when `Hᵇ(Z) = 0`, over a field. -/
lemma eq_zero_of_singleFunctor_of_field (b : ℤ) (M : ModuleCat.{u + 1} F)
    (Z : DerivedCategory (ModuleCat.{u + 1} F))
    (hZ : IsZero ((homologyFunctor (ModuleCat.{u + 1} F) b).obj Z))
    (g : (singleFunctor (ModuleCat.{u + 1} F) b).obj M ⟶ Z) : g = 0 := by
  have : Projective M := inferInstanceAs (Projective (ModuleCat.of F M))
  apply (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) b).map_injective
  rw [Functor.map_zero, ← cancel_epi
    (((singleFunctors (ModuleCat.{u + 1} F)).shiftIso b 0 b (by lia)).inv.app M), Limits.comp_zero]
  refine eq_zero_of_isZero_homology_zero M _ ?_ _
  exact hZ.of_iso (((homologyFunctor (ModuleCat.{u + 1} F) 0).shiftIso b 0 b (by lia)).app Z)

/-- Over a field, there are no nonzero morphisms between distinct shifts of `F[0]`. -/
lemma subsingleton_hom_shift_singleFunctor (a b : ℤ) (hab : a ≠ b) :
    Subsingleton ((shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) a).obj
        ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)) ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) b).obj
        ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F))) := by
  refine ⟨fun φ ψ ↦ ?_⟩
  suffices h : ∀ φ : (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) a).obj
      ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)) ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) b).obj
        ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)), φ = 0 by
    rw [h φ, h ψ]
  intro φ
  rw [← cancel_epi (((singleFunctors (ModuleCat.{u + 1} F)).shiftIso a (-a) 0 (by lia)).inv.app
    (ModuleCat.of F F)), Limits.comp_zero]
  refine eq_zero_of_singleFunctor_of_field (-a) _ _ ?_ _
  refine IsZero.of_iso ?_ (((homologyFunctor (ModuleCat.{u + 1} F) 0).shiftIso b (-a)
    (b - a) (by lia)).app _)
  rcases lt_or_gt_of_ne (sub_ne_zero.2 hab.symm) with h | h
  · exact isZero_of_isGE _ 0 _ h
  · exact isZero_of_isLE _ 0 _ h

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

/-- There are no nonzero morphisms between distinct shifts of the unit of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
lemma subsingleton_hom_shift_unit_point (a b : ℤ) (hab : a ≠ b) :
    Subsingleton ((shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) a).obj
        (𝟙_ _) ⟶
      (shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) b).obj (𝟙_ _)) := by
  obtain ⟨G, _, _, ⟨hG⟩, -, -, ⟨e₀⟩⟩ := exists_fiberFunctor_point ℓ k
  have := DerivedCategory.subsingleton_hom_shift_singleFunctor
    (F := ULift.{u + 1} (PadicAlgCl ℓ)) a b hab
  exact (hG.homEquiv.trans (Iso.homCongr ((G.commShiftIso a).app _ ≪≫
    (shiftFunctor _ a).mapIso e₀) ((G.commShiftIso b).app _ ≪≫
      (shiftFunctor _ b).mapIso e₀))).subsingleton

/-- There are no nonzero morphisms between distinct shifts of the unit of `D(Mod_{ℚ̲̄_ℓ,s})`. -/
lemma subsingleton_hom_shiftedUnit (a b : ℤ) (hab : a ≠ b) :
    Subsingleton (shiftedUnit ℓ k a ⟶ shiftedUnit ℓ k b) := by
  have := subsingleton_hom_shift_unit_point ℓ k a b hab
  exact ((ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj
    (Profinite.padicAlgClRingObj ℓ) (point k).left))).homEquiv.trans
    (Iso.homCongr (((boundedConstructible _).ι.commShiftIso a).app (𝟙_ _))
      (((boundedConstructible _).ι.commShiftIso b).app (𝟙_ _)))).symm.subsingleton

end AlgebraicGeometry.ProEtale.CondensedRing
