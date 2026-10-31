/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
import WeilConjectures.DeligneLaumon.CondensedCoefficientUnit
import WeilConjectures.AlgebraicGeometry.FiniteSmoothAdjunctionGeneralBase

/-! # Normalized smooth dualizing objects over a perfect field

Source: thm-a1-curve-perverse-heart, Step 2, smooth purity at the unit.
(blueprint: lem-per-condensed-lisse-normalized-purity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime]

set_option maxHeartbeats 2000000 in
-- Elaborating the finite/general-field index and its counit compares large native categories.
/-- The specified localizing adjoint has the finite-system-normalized purity at the unit.
Source: Step 2, smooth-purity paragraph
(blueprint: lem-per-condensed-lisse-normalized-purity).

Proof: invertibility of ell gives characteristic different from ell. Finite-type
schemes over the field are noetherian, and their structure maps therefore give
indices for the existing finite smooth adjunction theorem. The transported family
provides the localizing right adjoints and their bounded restrictions. The unit
is bounded constructible of Tor amplitude zero. Apply the unique counit-compatible
isomorphism between smooth pullback and the restricted adjoint to that unit.
The monoidal unit constraint identifies smooth pullback of the unit with the
shifted Tate line. The counit equation is exactly the required normalized trace,
after factoring the inverse of this composite isomorphism. All choices here are
adjunction data with the stated counit-preserving uniqueness, not arbitrary
coefficient objects.
-/
theorem normalized_purity_exists (k : Type u) [Field k] [PerfectField k]
    (hEll : IsUnit (ell : k)) :
    ∃ (A : ∀ T : Space k, AdjointData ell PurityTransport.Coefficient.closure T)
      (p : PurityComparisons ell PurityTransport.Coefficient.closure A),
      Normalized ell PurityTransport.Coefficient.closure A p := by
  classical
  let c : PurityTransport.Coefficient ell := .closure
  have : Fact (ringChar k ≠ ell) := ⟨by
    intro h
    have hz : (ell : k) = 0 := by
      rw [← h]
      exact (ringChar.spec k _).mpr dvd_rfl
    exact hEll.ne_zero hz⟩
  have hn (T : Space k) : IsNoetherian T.scheme := by
    have : IsLocallyNoetherian T.scheme := LocallyOfFiniteType.isLocallyNoetherian T.map
    have : CompactSpace T.scheme := QuasiCompact.compactSpace_of_compactSpace T.map
    exact {}
  have hfinite (T : Space k) :
      Etale.FiniteSmoothPurity.FiniteSmoothAdjunctionDatum ell T.map T.dim.val
        T.compactification (hn T) inferInstance := by
    let : T.scheme.Over (Spec (.of k)) := ⟨T.map⟩
    have : IsSeparated (T.scheme ↘ Spec (.of k)) := by
      change IsSeparated T.map
      infer_instance
    have : LocallyOfFiniteType (T.scheme ↘ Spec (.of k)) := by
      change LocallyOfFiniteType T.map
      infer_instance
    have : QuasiCompact (T.scheme ↘ Spec (.of k)) := by
      change QuasiCompact T.map
      infer_instance
    let : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩
    let : T.map.IsOver (Spec (.of k)) := ⟨by
      change T.map ≫ 𝟙 _ = T.map
      simp⟩
    obtain ⟨cf, hX, hY, h⟩ := Etale.FiniteSmoothPurity.finiteSmoothAdjunctionGeneralBase
      ell k T.map T.dim.val
    exact h
  let s (T : Space k) : GeneralFieldSmoothTransport.Index.{u} ell :=
    { base := ⟨k, hEll⟩
      X := Over.mk T.map
      Y := Over.mk (𝟙 (Spec (.of k)))
      dimX := T.dim
      dimY := ⟨0, by decide⟩
      xSmooth := by change SmoothOfRelativeDimension T.dim.val T.map; infer_instance
      ySmooth := by change SmoothOfRelativeDimension 0 (𝟙 _); infer_instance
      xFinite := by change LocallyOfFiniteType T.map; infer_instance
      yFinite := by change LocallyOfFiniteType (𝟙 _); infer_instance
      xCompact := by change QuasiCompact T.map; infer_instance
      yCompact := by change QuasiCompact (𝟙 _); infer_instance
      xSeparated := by change IsSeparated T.map; infer_instance
      ySeparated := by change IsSeparated (𝟙 _); infer_instance
      f := T.map
      isOver := ⟨by change T.map ≫ 𝟙 _ = T.map; simp⟩
      dim := T.dim
      compactification := T.compactification
      noetherianX := hn T
      noetherianY := by change IsNoetherian (Spec (.of k)); infer_instance
      finite := hfinite T }
  obtain ⟨N, hN, hSc, hM, hIso, hRat, hLoc, hCoc⟩ :=
    GeneralFieldSmoothTransport.finite_to_condensed_smooth_adjunction_transport.{u} ell
  have hunit : PurityTransport.property ell c (Spec (.of k)) (𝟙_ _) :=
    CondensedRing.condensedCoefficientUnit_mem (c.obj ell) (Spec (.of k))
  let U : c.ctf ell (Spec (.of k)) := ⟨𝟙_ _, hunit⟩
  have hA (T : Space k) :
      ∃ (A : AdjointData ell c T) (p : A.omega ell c ≅ c.derivedLine ell T.scheme T.dim.val),
        purityTrace ell c A p = transportedTrace ell c N (s T) U (Iso.refl _) := by
    obtain ⟨hL, G, b, hG, bctf, hb, gamma, hg, _⟩ := (hLoc (s T)).1
    let A : AdjointData ell c T :=
      { support_mem := hL
        exceptional := G
        adjunction := b
        unit_mem := ((PurityTransport.inclusion ell c _).obj U).property }
    let e : (c.smoothSource ell T.map T.dim.val).obj (𝟙_ _) ≅ A.omega ell c :=
      (PurityTransport.property ell c T.scheme).ι.mapIso (gamma.app U)
    let p : A.omega ell c ≅ c.derivedLine ell T.scheme T.dim.val :=
      e.symm ≪≫ smoothUnit ell c (s T)
    refine ⟨A, p, ?_⟩
    have hc := congrArg (fun f ↦ f.hom) (hg U)
    have hbU := eq_of_heq (hb U)
    have hc' : (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) T.compactification).map e.hom ≫
        (b.counit.app ((PurityTransport.inclusion ell c _).obj U)).hom =
        (N c (s T)).trace ell U := by
      change _ ≫ _ = _ at hc
      rw [← hbU]
      exact hc
    change (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) T.compactification).map
          ((smoothUnit ell c (s T)).inv ≫ e.hom) ≫
        (b.counit.app ((PurityTransport.inclusion ell c _).obj U)).hom =
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) T.compactification).map
          ((smoothUnit ell c (s T)).inv ≫
            (c.smoothSource ell T.map T.dim.val).map (𝟙 U.obj)) ≫
        (N c (s T)).trace ell U ≫ 𝟙 _
    rw [(c.smoothSource ell T.map T.dim.val).map_id U.obj]
    simp only [Category.comp_id, Functor.map_comp, Category.assoc]
    have ht : (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) T.compactification).map
          (𝟙 ((c.smoothSource ell T.map T.dim.val).obj U.obj)) ≫
        (N c (s T)).trace ell U = (N c (s T)).trace ell U := by
      exact (congrArg (fun f ↦ f ≫ (N c (s T)).trace ell U)
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) T.compactification).map_id _)).trans (Category.id_comp _)
    exact congrArg
      (fun f ↦ (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) T.compactification).map (smoothUnit ell c (s T)).inv ≫ f)
        (hc'.trans ht.symm)
  choose A p hp using hA
  refine ⟨A, p, N, hN, hSc, hIso, ?_⟩
  intro T
  exact ⟨s T, rfl, rfl, rfl, HEq.rfl, rfl, HEq.rfl, U, Iso.refl _, (hp T).heq⟩

end AlgebraicGeometry.ProEtale.CondensedLisseDual
