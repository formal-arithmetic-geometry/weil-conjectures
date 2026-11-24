/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkFiniteMatrixLift
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Prod

/-! # Lifting reverse-degree components without imposing homotopy equations
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem transport_lift
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (S : D ⥤ E) (T : C ⥤ E) (e : R ⋙ S ≅ T)
    {M N M' N' : C} (bM : M ≅ M') (bN : N ≅ N')
    (f : T.obj M ⟶ T.obj N) (g : R.obj M' ⟶ R.obj N')
    (hg : S.map g = (e.app M').hom ≫
      (T.map bM.inv ≫ f ≫ T.map bN.hom) ≫ (e.app N').inv) :
    S.map (R.map bM.hom ≫ g ≫ R.map bN.inv) =
      (e.app M).hom ≫ f ≫ (e.app N).inv := by
  have hbM := e.hom.naturality bM.hom
  have hbN := (e.inv.naturality bN.inv).symm
  change S.map (R.map bM.hom) ≫ (e.app M').hom =
    (e.app M).hom ≫ T.map bM.hom at hbM
  change (e.app N').inv ≫ S.map (R.map bN.inv) =
    T.map bN.inv ≫ (e.app N).inv at hbN
  calc
    _ = (S.map (R.map bM.hom) ≫ (e.app M').hom) ≫
        (T.map bM.inv ≫ f ≫ T.map bN.hom) ≫
        ((e.app N').inv ≫ S.map (R.map bN.inv)) := by
      simp only [Functor.map_comp, hg, Category.assoc]
    _ = ((e.app M).hom ≫ T.map bM.hom) ≫
        (T.map bM.inv ≫ f ≫ T.map bN.hom) ≫
        (T.map bN.inv ≫ (e.app N).inv) := by rw [hbM, hbN]
    _ = _ := by
      simp only [Category.assoc]
      change (e.app M).hom ≫ (T.mapIso bM).hom ≫ (T.mapIso bM).inv ≫ f ≫
        (T.mapIso bN).hom ≫ (T.mapIso bN).inv ≫ (e.app N).inv = _
      simp only [Iso.hom_inv_id_assoc]

-- Termwise restriction and pullback require additional definitional-equality checks.
/-- Lift a family of reverse-degree maps, without any equations involving the differential. -/
theorem exists_lift_reverse_components
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (h : ∀ i j : ℤ,
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)).X i ⟶
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)).X j)
    (hzero : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0) :
    ∃ (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U),
      let R := (restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let S := (Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let T := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let PV := ((restrictFunctor V.ι).mapHomologicalComplex _).obj P
      ∃ (e : R ⋙ S ≅ T) (k : ∀ i j : ℤ, (R.obj PV).X i ⟶ (R.obj PV).X j),
        (∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → k i j = 0) ∧
        ∀ i j, (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (k i j) =
          (e.app PV).hom.f i ≫ h i j ≫ (e.app PV).inv.f j := by
  classical
  let PV := ((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let J := {n : ℤ // n ∈ Finset.Icc 0 (d : ℤ)}
  let : Fintype J := Finset.Subtype.fintype _
  let I := J × J
  let : Fintype I := inferInstanceAs (Fintype (J × J))
  have hPVfree (n : ℤ) : ∃ s : ℕ, Nonempty
      (PV.X n ≅ SheafOfModules.free (R := V.toScheme.ringCatSheaf)
        (ULift.{u} (Fin s))) := by
    obtain ⟨s, ⟨b⟩⟩ := hfree n
    exact ⟨s, ⟨(restrictFunctor V.ι).mapIso b ≪≫ restrictFreeIso V.ι _⟩⟩
  choose r hr using hPVfree
  let b (n : ℤ) := (hr n).some
  let T₀ := pullback (V.fromSpecStalkOfMem y hyV)
  change ∀ i j : ℤ, T₀.obj (PV.X i) ⟶ T₀.obj (PV.X j) at h
  let t (q : I) := T₀.map (b q.1.val).inv ≫ h q.1.val q.2.val ≫ T₀.map (b q.2.val).hom
  obtain ⟨U, hUV, hyU, g, hg⟩ := exists_finite_free_matrices_of_stalk_local y V hyV
    (fun q : I ↦ r q.1.val) (fun q : I ↦ r q.2.val) t
  let R₀ := restrictFunctor (Y.homOfLE hUV)
  let S₀ := pullback (U.fromSpecStalkOfMem y hyU)
  let e₀ := stalkRestrictionWithinIso y V hyV U hUV hyU
  change ∀ q, S₀.map (g q) = (e₀.app _).hom ≫ t q ≫ (e₀.app _).inv at hg
  let e : R₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      S₀.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      T₀.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso e₀ (ComplexShape.up ℤ)
  let g' (q : I) := R₀.map (b q.1.val).hom ≫ g q ≫ R₀.map (b q.2.val).inv
  have hg' (q : I) : S₀.map (g' q) =
      (e₀.app (PV.X q.1.val)).hom ≫ h q.1.val q.2.val ≫ (e₀.app (PV.X q.2.val)).inv :=
    transport_lift R₀ S₀ T₀ e₀ (b q.1.val) (b q.2.val) (h q.1.val q.2.val) (g q) (hg q)
  let k : ∀ i j : ℤ, (R₀.obj (PV.X i)) ⟶ (R₀.obj (PV.X j)) := fun i j ↦
    if hi : 0 ≤ i ∧ i ≤ (d : ℤ) then
      if hj : 0 ≤ j ∧ j ≤ (d : ℤ) then
        if (ComplexShape.up ℤ).Rel j i then
          g' (⟨i, Finset.mem_Icc.mpr hi⟩, ⟨j, Finset.mem_Icc.mpr hj⟩)
        else 0
      else 0
    else 0
  refine ⟨U, hUV, hyU, e, k, ?_, ?_⟩
  · intro i j hij
    by_cases hi : 0 ≤ i ∧ i ≤ (d : ℤ)
    · by_cases hj : 0 ≤ j ∧ j ≤ (d : ℤ)
      · simp only [k, dite_eq_left hi, dite_eq_left hj, ite_eq_right hij]
      · simp only [k, dite_eq_left hi, dite_eq_right hj]
    · simp only [k, dite_eq_right hi]
  · intro i j
    change S₀.map (k i j) = (e₀.app (PV.X i)).hom ≫ h i j ≫ (e₀.app (PV.X j)).inv
    by_cases hi : 0 ≤ i ∧ i ≤ (d : ℤ)
    · by_cases hj : 0 ≤ j ∧ j ≤ (d : ℤ)
      · by_cases hij : (ComplexShape.up ℤ).Rel j i
        · dsimp only [k]
          rw [dite_eq_left hi, dite_eq_left hj, ite_eq_left hij]
          exact hg' (⟨i, Finset.mem_Icc.mpr hi⟩, ⟨j, Finset.mem_Icc.mpr hj⟩)
        · simp only [k, dite_eq_left hi, dite_eq_left hj, ite_eq_right hij, Functor.map_zero,
            hzero i j hij, zero_comp, comp_zero]
      · have hz : IsZero (P.X j) := by
          by_cases hj0 : j < 0
          · exact P.isZero_of_isStrictlyGE 0 j hj0
          · exact P.isZero_of_isStrictlyLE d j (by omega)
        have hz' := (pullback (V.fromSpecStalkOfMem y hyV)).map_isZero
          ((restrictFunctor V.ι).map_isZero hz)
        have hh : h i j = 0 := hz'.eq_of_tgt _ _
        simp only [k, dite_eq_left hi, dite_eq_right hj, Functor.map_zero, hh, zero_comp, comp_zero]
    · have hz : IsZero (P.X i) := by
        by_cases hi0 : i < 0
        · exact P.isZero_of_isStrictlyGE 0 i hi0
        · exact P.isZero_of_isStrictlyLE d i (by omega)
      have hz' := (pullback (V.fromSpecStalkOfMem y hyV)).map_isZero
        ((restrictFunctor V.ι).map_isZero hz)
      have hh : h i j = 0 := hz'.eq_of_src _ _
      simp only [k, dite_eq_right hi, Functor.map_zero, hh, zero_comp, comp_zero]

end AlgebraicGeometry.Scheme.Modules
