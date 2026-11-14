/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.Topology.ProfiniteCondensedRing

/-!
# A Tor interval from the Tor intervals of cohomology modules

proof.md,
Complexes paragraph, generalized to a common cohomology Tor interval `[c,d]`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A complex with cohomology in `[a,b]`, each cohomology module in degree zero having
Tor amplitude in `[c,d]`, has Tor amplitude in `[a+c,b+d]`. No constructibility is assumed. -/
theorem torAmplitudeIn_of_cohomology_interval
    (X : Scheme.{u}) (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (hK : ∀ q : ℤ, q ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hH : ∀ q : ℤ, q ∈ Set.Icc a b →
      DerivedCategory.torAmplitudeIn _ c d
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) :
    DerivedCategory.torAmplitudeIn _ (a + c) (b + d) K := by
  classical
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)
  let Q := DerivedCategory.torAmplitudeIn C (a + c) (b + d)
  let P : ℤ → ObjectProperty C := fun q M ↦
    q ∈ Set.Icc a b ∧ DerivedCategory.torAmplitudeIn C c d
      ((DerivedCategory.singleFunctor C 0).obj M)
  let (q : ℤ) : (P q).IsClosedUnderIsomorphisms := ⟨fun e h ↦
    ⟨h.1, (DerivedCategory.torAmplitudeIn C c d).prop_of_iso
      ((DerivedCategory.singleFunctor C 0).mapIso e) h.2⟩⟩
  have hzero (M : DerivedCategory C) (hM : IsZero M) : Q M := by
    intro N
    let F := (CategoryTheory.MonoidalCategory.curriedTensor (DerivedCategory C)).flip.obj
      ((DerivedCategory.singleFunctor C 0).obj N)
    have hz := F.map_isZero hM
    exact ⟨(DerivedCategory.isGE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ hz,
      (DerivedCategory.isLE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ hz⟩
  have hext (T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory C))
      (hT : T ∈ distTriang (DerivedCategory C)) (h₁ : Q T.obj₁) (h₃ : Q T.obj₃) :
      Q T.obj₂ :=
    (constantModelConstructibleFiniteTor_wellDefined Λ.X X).2.2.2.2.2.1
      T (a + c) (b + d) (add_le_add hab hcd) hT h₁ h₃
  have hsingle (q : ℤ) (M : C) (hM : P q M) :
      Q ((DerivedCategory.singleFunctor C q).obj M) := by
    have hs : DerivedCategory.torAmplitudeIn C (c - (-q)) (d - (-q))
        (((DerivedCategory.singleFunctor C 0).obj M)⟦-q⟧) := by
      intro N
      let F := (CategoryTheory.MonoidalCategory.curriedTensor (DerivedCategory C)).flip.obj
        ((DerivedCategory.singleFunctor C 0).obj N)
      obtain ⟨h₁, h₂⟩ := hM.2 N
      let e := (F.commShiftIso (-q)).app ((DerivedCategory.singleFunctor C 0).obj M)
      have hg₀ : DerivedCategory.TStructure.t.IsGE
          (F.obj ((DerivedCategory.singleFunctor C 0).obj M)) c := h₁
      have hl₀ : DerivedCategory.TStructure.t.IsLE
          (F.obj ((DerivedCategory.singleFunctor C 0).obj M)) d := h₂
      have hg := DerivedCategory.TStructure.t.isGE_shift
        (F.obj ((DerivedCategory.singleFunctor C 0).obj M)) c (-q) (c - (-q)) (by omega)
      have hl := DerivedCategory.TStructure.t.isLE_shift
        (F.obj ((DerivedCategory.singleFunctor C 0).obj M)) d (-q) (d - (-q)) (by omega)
      exact ⟨⟨(DerivedCategory.TStructure.t.ge (c - (-q))).prop_of_iso e.symm hg.ge⟩,
        ⟨(DerivedCategory.TStructure.t.le (d - (-q))).prop_of_iso e.symm hl.le⟩⟩
    exact (DerivedCategory.torAmplitudeIn C (a + c) (b + d)).prop_of_iso
      (((DerivedCategory.singleFunctors C).shiftIso (-q) q 0 (by omega)).app M)
      (hs.mono (by have := hM.1.1; omega) (by have := hM.1.2; omega))
  have hge : K.IsGE a := (DerivedCategory.isGE_iff K a).2 fun q hq ↦ hK q (by
    simp only [Set.mem_Icc]; omega)
  have hle : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun q hq ↦ hK q (by
    simp only [Set.mem_Icc]; omega)
  -- The existing degreewise dévissage performs the finite truncation induction.
  apply DerivedCategory.prop_of_isGE_of_isLE_of_degreewise Q hzero hext P hsingle
    (b - a + 1).toNat a K hge
    (DerivedCategory.TStructure.t.isLE_of_le K b _ (by omega))
  intro q hq hq'
  have hqi : q ∈ Set.Icc a b := by
    simp only [Set.mem_Icc]; omega
  exact ⟨hqi, hH q hqi⟩

end AlgebraicGeometry.ProEtale
