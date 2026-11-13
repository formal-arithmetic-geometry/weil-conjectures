/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedKummerReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernScalarUnit
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedChernFiniteBoundary
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.KummerLineTwisting
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Normalized Chern and line-twist data at one scheme -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private def kummerInclusion (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    roots l T ⟶ powerUnits l T :=
  NatTrans.ofOpSequence (fun n ↦ Scheme.proEtaleRootsOfUnityInclusion T (l ^ (n + 1)))
    (fun n ↦ by
      simp only [roots, Scheme.proEtaleRootsOfUnityTower, powerUnits,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply Sheaf.hom_ext
      ext U x
      exact Scheme.proEtaleRootsOfUnityTransition_prime T l Fact.out n U x)

private def kummerPower (l : ℕ) (T : Scheme.{u}) :
    powerUnits l T ⟶ units T :=
  NatTrans.ofOpSequence (fun n ↦ Scheme.proEtaleUnitsPower T (l ^ (n + 1)))
    (fun n ↦ by
      simp only [powerUnits, units, constant, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.const_obj_map]
      change (l • 𝟙 (Scheme.proEtaleUnitsSheaf T)) ≫
        (l ^ (n + 1) • 𝟙 (Scheme.proEtaleUnitsSheaf T)) =
          (l ^ (n + 2) • 𝟙 (Scheme.proEtaleUnitsSheaf T)) ≫ 𝟙 _
      simp only [Preadditive.comp_nsmul, Category.comp_id, smul_smul]
      rw [← pow_succ])

private theorem kummerZero (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    kummerInclusion l T ≫ kummerPower l T = 0 := by
  apply NatTrans.ext
  funext n
  change Scheme.proEtaleRootsOfUnityInclusion T (l ^ (n.unop + 1)) ≫
    Scheme.proEtaleUnitsPower T (l ^ (n.unop + 1)) = 0
  exact kernel.condition (Scheme.proEtaleUnitsPower T (l ^ (n.unop + 1)))

private theorem kummerExact (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) :
    (ShortComplex.mk (kummerInclusion l T) (kummerPower l T) (kummerZero l T)).ShortExact := by
  let S := ShortComplex.mk (kummerInclusion l T) (kummerPower l T) (kummerZero l T)
  have hs (n : ℕᵒᵖ) : (S.map ((CategoryTheory.evaluation _ _).obj n)).ShortExact := by
    exact cartierProKummer_exact T (l ^ (n.unop + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (by simpa using hT.pow (n.unop + 1))
  have hm : ∀ n : ℕᵒᵖ, Mono ((kummerInclusion l T).app n) := fun n ↦ (hs n).mono_f
  have he : ∀ n : ℕᵒᵖ, Epi ((kummerPower l T).app n) := fun n ↦ (hs n).epi_g
  refine { mono_f := NatTrans.mono_of_mono_app _
           epi_g := NatTrans.epi_of_epi_app _
           exact := ?_ }
  apply S.exact_iff_isZero_homology.mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  apply NatTrans.ext
  funext n
  have hz := ((S.map ((CategoryTheory.evaluation _ _).obj n)).exact_iff_isZero_homology.mp
    (hs n).exact).of_iso (S.mapHomologyIso
    ((CategoryTheory.evaluation _ _).obj n)).symm
  exact hz.eq_of_src _ _

private def kummerData (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) : Kummer l T where
  inclusion := kummerInclusion l T
  inclusion_eq _ := rfl
  power := kummerPower l T
  power_eq _ := rfl
  zero := kummerZero l T
  exact := kummerExact l T hT

/-- Normalized simultaneous Kummer reduction admits the actual tensor/Hom line twist. -/
theorem exists_diagonalTraceChernTwist (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤))) :
    ∃ c : Chern l (ULift.{u} (Padic l)) T,
      c.Normalized l (ULift.{u} (Padic l)) ∧
      FiniteChernNormalization l (ULift.{u} (Padic l)) c ∧
      Nonempty (Twisting l (ULift.{u} (Padic l)) c) := by
  let E := ULift.{u} (Padic l)
  let k := kummerData l T hT
  obtain ⟨r, M, i, a, b, ha, hb⟩ := exists_normalizedKummerReduction l T hT k
  obtain ⟨s⟩ := (WeilConjectures.SemilinearSections.semilinearScalarData.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T)
    (fun n ↦ (Rrings l T).obj (op n))
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
    (SpTowerClasses.coefficientMap l E T)
    (SpTowerClasses.coefficientMap_transition l E T)).1
  obtain ⟨e, he⟩ := exists_normalizedScalarUnit l E T s
  let c : Chern l E T :=
    { kummer := k
      reduction := r
      rootModule := M
      rootForget := i
      unitIso := a
      rootIso := b
      scalar := s
      scalarUnit := e }
  have hc : c.Normalized l E := ⟨ha, hb, he⟩
  exact ⟨c, hc, finiteChernNormalization_of_normalized l E c hc,
    nonempty_kummerLineTwisting l E T hT c⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
