/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.Transport
public import WeilConjectures.AlgebraicGeometry.CondensedPurityCoefficientChange
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Adic and rational smooth dualizing complexes

Source: current blueprint, condensed coefficient corollary
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace WeilConjectures.AdicSmoothDualizing.Condensed

section UnitMembership
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
private theorem regular_finitelyPresented : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
  let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
  exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget (X := Mod.finiteFree Λ 0)).symm⟩⟩

omit [IsCommMonObj Λ] in
private theorem zero_finitelyPresented : Mod.IsFinitelyPresented Λ (0 : Mod _ Λ) := by
  exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩

private instance pointBraided (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

private theorem model_regular {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨Mod.regular Λ, regular_finitelyPresented Λ, ⟨?_⟩⟩
  exact (CondensedRing.upperStar Λ (𝟙 X)).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm ≪≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
    Functor.Monoidal.εIso ((upperStarFromPoint X).mapMod Λ)

private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ f).obj
      (0 : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

private def oneStratum (X : Scheme.{u}) : Scheme.Stratification X :=
  { n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
    isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
    iUnion_stratum_eq_univ := Set.iUnion_const _
    pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
    domain := fun _ ↦ X
    immersion := fun _ ↦ 𝟙 X
    range_immersion := fun _ ↦ Set.range_id' }

private theorem regular_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (Mod.regular (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_regular Λ (𝟙 X)⟩

private theorem zero_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X
      (0 : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero Λ (𝟙 X)⟩

set_option maxHeartbeats 800000 in
-- The homology comparison elaborates through the internal module category.
/-- The coefficient sheaf in degree zero has a finite constant model.
Source: rational projective-line unit/counit proof step 5, rank-one scalar model
(blueprint: lem-sfb-rational-p1-line-from-preservation).
Proof: use the one-stratum partition and the identity cover. The scalar model is the
regular coefficient module, with its rank-one finite presentation. Monoidality of
inverse image identifies both pullbacks of this regular module. The single complex
is bounded, has this module as its zeroth cohomology and zero cohomology otherwise. -/
private theorem coefficientUnit_boundedConstructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) := by
  let C := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
      (regular_constructible Λ X)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact (DerivedCategory.isGE_iff _ 0).1 inferInstance n h
      · exact (DerivedCategory.isLE_iff _ 0).1 inferInstance n h
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((isZero_zero _).iso hz) (zero_constructible Λ X)


end UnitMembership

/-- The actual coefficient unit belongs to the native bounded constructible finite-Tor
category: its constant model is free of rank one and its Tor amplitude is [0,0].
Source: current corollary, coefficient-unit application
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
theorem unit_mem (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : property ell c X (unit ell c X) := by
  refine ⟨coefficientUnit_boundedConstructible (c.obj ell) X, 0, 0, ?_⟩
  intro N
  let e := tensorIso (DerivedCategory.singleFunctorObjUnitIso _) (Iso.refl
    ((DerivedCategory.singleFunctor _ 0).obj N)) ≪≫ λ_ _
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm 0⟩

/-- The counit equation for the canonical condensed smooth-purity comparison.
The comparison is the canonical `rightAdjointUniq`; its counit equation is the
injective Hom-equivalence equation and does not depend on a legacy coefficient
model. It is the coefficient-unit instance of the current blueprint corollary.
Source: current blueprint coefficient-unit application
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
-/
theorem condensed_purity_counit_comparison {ell : ℕ} [Fact ell.Prime]
    {D : WeilConjectures.FiniteFieldDatum.{u}} {c : Coefficient ell} {s : SmoothDatum D}
    (A : ExplicitAdjunction ell D c s)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
    (K : c.ctf ell s.Y.left) :
    (R.lower.map ((A.adjunction.rightAdjointUniq R.restrictedAdjunction).hom.app K)).hom ≫
        R.counit K =
      (A.adjunction.counit.app K).hom := by
  exact congrArg (fun f ↦ f.hom)
    (Adjunction.rightAdjointUniq_hom_app_counit A.adjunction R.restrictedAdjunction K)

/-- The Brown exceptional coefficient unit, identified with the native shifted Tate line.
The map is the inverse of the unique counit-compatible natural comparison, followed
by the canonical pullback-unit and tensor-unit isomorphisms.
Source: current blueprint coefficient-unit application
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def identification {ell : ℕ} [Fact ell.Prime]
    {D : FiniteFieldDatum.{u}} {c : Coefficient ell} {s : SmoothDatum D}
    (A : ExplicitAdjunction ell D c s)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
    (hU : property ell c s.Y.left (unit ell c s.Y.left)) :
    (R.upper.obj ⟨_, hU⟩).obj ≅ c.derivedLine ell s.X.left s.dim :=
  (property ell c s.X.left).ι.mapIso
    ((A.adjunction.rightAdjointUniq R.restrictedAdjunction).symm.app ⟨_, hU⟩) ≪≫
      sourceUnit ell c s.map s.dim

/-- Integration on the shifted Tate line is the same explicit smooth counit in
canonical coefficient-unit coordinates.
Source: current blueprint smooth-trace clause
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integration {ell : ℕ} [Fact ell.Prime]
    {D : FiniteFieldDatum.{u}} {c : Coefficient ell} {s : SmoothDatum D}
    (A : ExplicitAdjunction ell D c s)
    (hU : property ell c s.Y.left (unit ell c s.Y.left)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).obj (c.derivedLine ell s.X.left s.dim) ⟶
        unit ell c s.Y.left :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification
    (c.obj ell) s.compactification).map (sourceUnit ell c s.map s.dim).inv ≫
      A.trace ⟨_, hU⟩

private theorem map_iso_coordinates {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z : C} (g : X ≅ Y) (e : X ≅ Z) {W : D}
    (eps : F.obj Y ⟶ W) (t : F.obj X ⟶ W) (h : F.map g.hom ≫ eps = t) :
    F.map (g.inv ≫ e.hom) ≫ (F.map e.inv ≫ t) = eps := by
  calc
    F.map (g.inv ≫ e.hom) ≫ (F.map e.inv ≫ t) =
        (F.map g.inv ≫ (F.map e.hom ≫ F.map e.inv)) ≫ t := by
      simp only [F.map_comp, Category.assoc]
    _ = F.map g.inv ≫ t := by
      rw [← F.map_comp, e.hom_inv_id, F.map_id, Category.comp_id]
    _ = eps := by
      rw [← h, ← F.map_comp_assoc, g.inv_hom_id, F.map_id, Category.id_comp]

/-- The dualizing identification carries the Brown counit to smooth integration.
Source: current blueprint counit clause
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: expand the two canonical unit coordinates, cancel them, and apply the
counit equation for right-adjoint uniqueness; then cancel gamma with its inverse. -/
theorem identification_counit {ell : ℕ} [Fact ell.Prime]
    {D : FiniteFieldDatum.{u}} {c : Coefficient ell} {s : SmoothDatum D}
    (A : ExplicitAdjunction ell D c s)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
    (hU : property ell c s.Y.left (unit ell c s.Y.left)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).map (identification A R hU).hom ≫
        integration A hU = R.counit ⟨_, hU⟩ := by
  let F := CondensedRing.rightDerivedLowerShriekOfCompactification
    (c.obj ell) s.compactification
  let g : (c.smoothSource ell s.map s.dim).obj (unit ell c s.Y.left) ≅
      (R.upper.obj ⟨_, hU⟩).obj :=
    (property ell c s.X.left).ι.mapIso
      ((A.adjunction.rightAdjointUniq R.restrictedAdjunction).app ⟨_, hU⟩)
  let e := sourceUnit ell c s.map s.dim
  let t : F.obj ((c.smoothSource ell s.map s.dim).obj (unit ell c s.Y.left)) ⟶
      unit ell c s.Y.left := A.trace ⟨_, hU⟩
  have hg : F.map g.hom ≫ R.counit ⟨_, hU⟩ = t :=
    condensed_purity_counit_comparison A R ⟨_, hU⟩
  change F.map (g.inv ≫ e.hom) ≫ (F.map e.inv ≫ t) = _
  exact map_iso_coordinates F g e (R.counit ⟨_, hU⟩) t hg

/-- The current condensed smooth-dualizing corollary, simultaneously for integral,
rational and algebraically closed coefficients. The family is normalized by the
finite integration maps and retains the native coefficient-change equations.
For a structural geometric index, `R.upper` applied to the coefficient unit is
omega_X; `identification` identifies it with Lambda_X(d)[2d], and the displayed
equation identifies its counit with smooth integration. The stronger relative
version is stated, so the structural specialization requires no new choices.
Source: current blueprint corollary and its coefficient-unit proof
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: obtain the normalized family and its coefficient equations from the existing
condensed coefficient-change theorem. The rank-one unit has bounded constructible
finite-Tor amplitude. Evaluate the canonical comparison at this unit, compose
with sourceUnit, and apply identification_counit. All coefficient reduction,
inversion and extension equations are retained on the same family. -/
theorem adic_and_rational_smooth_dualizing_complexes
    (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p) :
    ∃ A : AdjunctionFamily ell D,
      BrownComparison ell D A ∧ ScalarCompatible ell D A ∧
      BaseChangeCompatible ell D A ∧ CompositionCompatible ell D hEll A ∧
      AffineNormalized ell D A ∧
      ∃ P : PurityCoefficientChange.Coordinates.{u} ell,
        PurityCoefficientChange.Equations ell D hEll A P ∧
        PurityCoefficientChange.FrobeniusCompatible ell D P ∧
        PurityCoefficientChange.CompositionCoherent ell D hEll P ∧
        PurityCoefficientChange.IdentityCoherent ell D hEll P ∧
        ∀ (c : Coefficient ell) (s : SmoothDatum D)
          (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification),
          ∃ hU : property ell c s.Y.left (unit ell c s.Y.left),
            Nonempty ((R.upper.obj ⟨_, hU⟩).obj ≅ c.derivedLine ell s.X.left s.dim) ∧
            (CondensedRing.rightDerivedLowerShriekOfCompactification
              (c.obj ell) s.compactification).map (identification (A c s) R hU).hom ≫
                integration (A c s) hU = R.counit ⟨_, hU⟩ := by
  obtain ⟨A, hB, hS, hBC, hC, hN, P, hE, hF, hComp, hId⟩ :=
    PurityCoefficientChange.condensed_purity_coefficient_change ell D hEll
  refine ⟨A, hB, hS, hBC, hC, hN, P, hE, hF, hComp, hId, ?_⟩
  intro c s R
  have : CompactSpace s.Y.left := QuasiCompact.compactSpace_of_compactSpace s.Y.hom
  have : IsNoetherian s.Y.left := isNoetherian_of_locallyOfFiniteType s.Y.hom
  let hU := unit_mem ell c s.Y.left
  exact ⟨hU, ⟨identification (A c s) R hU⟩, identification_counit (A c s) R hU⟩

end WeilConjectures.AdicSmoothDualizing.Condensed
