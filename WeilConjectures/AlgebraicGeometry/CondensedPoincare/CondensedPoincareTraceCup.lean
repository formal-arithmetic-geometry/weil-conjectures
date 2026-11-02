/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasic
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

import WeilConjectures.CategoryTheory.DerivedCategory.CondensedDualSingle
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-! # Trace and cup product with actual condensed rational coefficients

Source: latest blueprint, sec-poincare-duality/sk-thm-poincare-duality/
def-weil-poincare-trace-cup.md (blueprint: def-weil-poincare-trace-cup).

Cohomology is represented by maps from the coefficient unit in the actual ordinary
condensed derived category. The product is the tensor product of these classes.
The trace is the exceptional counit, untwisted by the closed tensor adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedPoincare

variable (ell : ℕ) [Fact ell.Prime]

/-- The coefficient multiplication gives the graded-commutative cup product.
Source: the displayed graded-commutativity identity
(blueprint: def-weil-poincare-trace-cup).
Proof: move the two shifts out of the tensor product. Interchanging them contributes
(-1)^(ij), while symmetry of the coefficient-unit multiplication removes the switch
of the two unshifted factors. The derived unitors commute with shift, so the
Eckmann-Hilton identity gives the stated formula. -/
theorem cup_comm {X : Scheme.{u}} (i j : ℤ)
    (x : cohomology ell X i) (y : cohomology ell X j) :
    cup ell y x = (i * j).negOnePow • (cup ell x y ≫
      (eqToIso (congrArg (fun n : ℤ ↦ (unit ell X) ⟦n⟧) (add_comm i j))).hom) := by
  exact MonoidalCategory.shiftProduct_comm (DerivedCategory.unitorsCommShift _) x y

open PurityTransport

/-- The derived dual presentation is the existing signed Tate line in degree zero.
Source: the signed Tate convention (blueprint: def-weil-poincare-trace-cup).
Proof: a root-trivializing cover makes the positive line free of rank one. Its
ordinary internal dual is therefore already its derived internal dual. The
degree-zero tensor and unit comparisons give the displayed isomorphism, including
d=0, and these canonical evaluation-transpose maps descend from the cover. -/
theorem negativeLine_published (X : Scheme.{u})
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ) :
    Nonempty (CondensedRing.StrictWeil.derivedTateLine ell .rationals X (-(d : ℤ)) ≅
      negativeLine ell X d) := by
  let A := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (ring.{u} ell) X)
  have hInv : IsUnit (ell : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((X.presheaf.germ ⊤ x hx).hom (ell : Γ(X, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : X.residueField x)
  obtain ⟨𝒰, h𝒰⟩ := tateModule_locally_trivial X ell hInv
  have hT : IsLocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) X) (tateModule X ell) := by
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨e⟩ := h𝒰 i
    exact ⟨1, ⟨e ≪≫ (biproductUniqueIso (fun _ : Fin 1 ↦ 𝟙_ _)).symm⟩⟩
  let F := Mod.extendScalars (coefficientMap (Coefficient.rationals.integralMap ell) X)
  let : F.Monoidal := Mod.extendScalarsMonoidal _
  have hL : IsDualizable (Coefficient.rationals.firstLine ell X) :=
    IsDualizable.map F hT.isDualizable
  have hd (n : ℕ) : IsDualizable (Coefficient.rationals.line ell X n) := by
    induction n with
    | zero => exact isDualizable_unit
    | succ n hn => exact hn.tensorObj hL
  cases d with
  | zero =>
      obtain ⟨e⟩ := DerivedCategory.nonempty_ihom_single_unit (𝟙_ A) isDualizable_unit 0
      exact ⟨(DerivedCategory.singleFunctor A 0).mapIso
        (MonoidalClosed.unitIsoSelf (X := 𝟙_ A)).symm ≪≫ e.symm⟩
  | succ n =>
      obtain ⟨e⟩ := DerivedCategory.nonempty_ihom_single_unit
        (Coefficient.rationals.line ell X (n + 1)) (hd (n + 1)) 0
      exact ⟨e.symm⟩

/-- The coefficient prime is invertible at every residue field over the fixed closure.
Source: the standing prime convention (blueprint: def-weil-poincare-trace-cup).
Proof: the fixed closure has characteristic p. The distinct prime ell is nonzero
there; its inverse maps to an inverse through the field map into each residue field. -/
theorem residue_prime_unit (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k)) (x : X) :
    IsUnit (ell : X.residueField x) := by
  simpa only [map_natCast] using
    (PurityTransport.primeUnit D ell hEll).map
      ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫ a.appTop ≫ X.Γevaluation x).hom

variable {ell} {D : WeilConjectures.FiniteFieldDatum.{u}} (s : SmoothDatum D)

/-- The regular module is constructible and has Tor interval [0,0].
Source: the coefficient unit (blueprint: def-weil-poincare-trace-cup).
Proof: on the identity stratification its model is the free rank-one scalar module.
The complex is concentrated in degree zero and its tensor functor is the identity. -/
theorem unit_mem : property ell .rationals s.Y.left
    (PurityTransport.unit ell .rationals s.Y.left) := by
  let Λ := ring.{u} ell
  let X := s.Y.left
  let C := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s.Y.hom
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s.Y.hom
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  let : (upperStarFromPoint X).Braided :=
    { toMonoidal := inferInstance
      braided := Functor.LaxBraided.braided }
  have hfp : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
    let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
    exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget (X := Mod.finiteFree Λ 0)).symm⟩⟩
  have hzero : Mod.IsFinitelyPresented Λ (0 : Mod _ Λ) :=
    ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  have hr : IsConstantModelConstructible Λ X (Mod.regular (condensedRingObj Λ X)) := by
    rw [IsConstantModelConstructible, if_pos hX]
    refine ⟨S, fun _ ↦ ?_⟩
    refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
    refine ⟨Mod.regular Λ, hfp, ⟨?_⟩⟩
    exact (CondensedRing.upperStar Λ (𝟙 X)).mapIso
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
      Functor.Monoidal.εIso ((upperStarFromPoint X).mapMod Λ)
  have hz : IsConstantModelConstructible Λ X (0 : C) := by
    rw [IsConstantModelConstructible, if_pos hX]
    refine ⟨S, fun _ ↦ ?_⟩
    refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
    refine ⟨0, hzero, ⟨?_⟩⟩
    exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
      ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero (isZero_zero _))).iso
        (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  have hb : constantModelBoundedConstructible Λ X
      ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm hr
    · have h : IsZero ((DerivedCategory.homologyFunctor C n).obj
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))) := by
        rcases lt_or_gt_of_ne hn with h | h
        · exact (DerivedCategory.isGE_iff _ 0).1 inferInstance n h
        · exact (DerivedCategory.isLE_iff _ 0).1 inferInstance n h
      exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
        ((isZero_zero _).iso h) hz
  refine ⟨hb, 0, 0, ?_⟩
  intro N
  let e := tensorIso (DerivedCategory.singleFunctorObjUnitIso C) (Iso.refl
    ((DerivedCategory.singleFunctor C 0).obj N)) ≪≫ λ_ _
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm 0⟩

/-- The fixed closure has the prescribed positive characteristic.
Source: finite-field conventions (blueprint: def-weil-poincare-trace-cup).
Proof: a finite field of cardinality p^a with a positive has characteristic p.
An algebraic extension of a field has the same characteristic. -/
theorem closure_characteristic : ringChar D.k = D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ringChar.eq D.k D.p

/-- The rational ring is one of the actual native exceptional coefficients.
Source: the coefficient convention (blueprint: def-weil-poincare-trace-cup).
Proof: choose the rational disjunct and the identity ring-object isomorphism. -/
theorem nativeCoefficient : CondensedRing.IsNativeExceptionalCoefficient ell (ring.{u} ell) :=
  by exact Or.inr (Or.inl ⟨Iso.refl _⟩)

end AlgebraicGeometry.ProEtale.CondensedPoincare
