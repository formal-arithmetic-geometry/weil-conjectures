/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Bounded-below direct image and quasi-coherence

Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The zero sheaf is quasi-coherent, using the free sheaf on no generators. -/
private theorem qcoh_containsZero (Y : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).ContainsZero := by
  have hzero : Limits.IsZero
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  exact ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
    (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}⟩⟩

/-- Kernel and Limits.cokernel closure propagate quasi-coherence to every derived page. -/
private theorem qcoh_pages {Y : Scheme.{u}}
    (S : BigradedExactCouple (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0)
    (hS : ∀ p q : ℤ, (S.E p q).IsQuasicoherent) :
    ∀ (r : ℕ) (p q : ℤ), (S.page r p q).IsQuasicoherent := by
  suffices h : ∀ (r : ℕ) (p q : ℤ), ((S.pageCouple r).E p q).IsQuasicoherent by
    intro r p q
    exact h (r - 2) p q
  intro r
  induction r with
  | zero => exact hS
  | succ r ih =>
    intro p q
    let : ((S.pageCouple r).E p q).IsQuasicoherent := ih p q
    let : ((S.pageCouple r).E (p + 2 + r) (q - 1 - r)).IsQuasicoherent :=
      ih _ _
    let : ((S.pageCouple r).E (p - r - 2) (q + r + 1)).IsQuasicoherent :=
      ih _ _
    let k := Limits.kernel ((S.pageCouple r).d p q)
    let kl := Limits.kernel.lift ((S.pageCouple r).d p q)
      ((S.pageCouple r).dInto p q) ((S.pageCouple r).dInto_comp_d p q)
    have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel _
    let : k.IsQuasicoherent := hk
    exact (Scheme.Modules.quasiCoherent_cokernel_image kl).2.2.2.2.2.2.1

/-- An isomorphism-invariant extension-closed property passes from finite graded pieces
to the filtered object, by descending induction from the zero step. -/
private theorem property_of_filtration {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hext : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {M : C} (F : PBCDecreasingFiltration M) (N : ℕ)
    (hfull : F.step 0 = ⊤) (hzero : F.step N = ⊥)
    (hgraded : ∀ p : ℤ, P (F.gradedPiece p)) : P M := by
  have hstep : ∀ k : ℕ, k ≤ N → P (F.step ((N : ℤ) - k)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hz : F.step ((N : ℤ) - 0) = ⊥ := by simpa using hzero
        change P (F.step ((N : ℤ) - 0))
        rw [hz]
        exact P.prop_of_iso Subobject.botCoeIsoZero.symm (P.prop_of_isZero (isZero_zero C))
    | succ k ih =>
        intro hk
        let p : ℤ := (N : ℤ) - k - 1
        have hp : (N : ℤ) - (k + 1) = p := by
          dsimp [p]
          ring
        have hp' : (N : ℤ) - k = p + 1 := by
          dsimp [p]
          ring
        let i := Subobject.ofLE (F.step (p + 1)) (F.step p)
          (F.antitone_step (by omega))
        have hi : Mono i := inferInstance
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact :=
          { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
            mono_f := inferInstance
            epi_g := inferInstance }
        have htarget : P (F.step p) := by
          apply hext S hS
          · simpa only [hp'] using ih (by omega)
          · change P (cokernel i)
            change P (F.gradedPiece p)
            exact hgraded p
        simpa [hp, Nat.cast_add] using htarget
  have htop : P (F.step 0) := by
    simpa only [show (N : ℤ) - N = 0 by omega] using hstep N (le_refl N)
  have : IsIso (F.step 0).arrow := by
    rw [hfull]
    infer_instance
  exact P.prop_of_iso (asIso (F.step 0).arrow) htop

/-- Derived direct image of a bounded-below object with quasi-coherent cohomology
has quasi-coherent cohomology. No compactness of the target is required.
Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).

Proof:
1. Represent E by a strictly bounded-below complex, using the standard t-structure.
   Apply exists_truncationHypercohomology to the module direct-image functor.
   Its right derived functor is definitionally schemeDerivedDirectImage.
   The E2 comparisons identify the terms with R^p f_* H^j(E).
2. The qcqs higher-direct-image theorem (Tag 01XJ, lem-pc-finite-support-hi)
   makes these terms quasi-coherent. Negative p and j < a terms vanish.
3. Each later page is a Limits.kernel modulo an image. The quasi-coherent Limits.kernel and
   Limits.cokernel/image lemmas imply, by induction on the page, quasi-coherence of
   every page term. In total degree q only 0 <= p <= q-a occurs, and each
   term stabilizes at a finite page by the half-plane bounds.
4. The convergence theorem supplies a finite filtration of H^q(Rf_*E), with
   those stable terms as graded pieces. Start from its zero last step and use
   isQuasicoherent_of_shortExact successively to deduce quasi-coherence of all
   filtration steps, ending at H^q(Rf_*E). This applies to every integer q.
-/
theorem schemeDerivedDirectImage_preserves_QCoh_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a : ℤ) [E.IsGE a] :
    schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) := by
  classical
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let P : ObjectProperty B := SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)
  let : Zero B := CategoryTheory.Limits.HasZeroObject.zero' B
  have : P.ContainsZero := qcoh_containsZero Y
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso e h⟩
  have : Limits.PreservesFiniteLimits F := by
    change Limits.PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  have : IsGrothendieckAbelian.{u} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E a
  let Kplus : CochainComplex.Plus A := ⟨K, a, hK⟩
  have ha : ∀ q : ℤ, q < a → Limits.IsZero (Kplus.obj.homology q) := by
    intro q hq
    exact (K.exactAt_of_isGE a q hq).isZero_homology
  obtain ⟨T, _, _, _, _, _, hsecond, hneg, _, _, _, _, _, _, _, _, _, hconv⟩ :=
    exists_truncationHypercohomology F Kplus a ha
  let eH (q : ℤ) := (DerivedCategory.homologyFunctor A q).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors A q).app K
  have hsecondQC : ∀ p q : ℤ, P (T.E p q) := by
    intro p q
    by_cases hp : p < 0
    · exact P.prop_of_isZero (hneg p q hp)
    · obtain ⟨_, _, eK, _⟩ := hsecond p.toNat q
      have hRq : P ((F.rightDerived p.toNat).obj (Kplus.obj.homology q)) := by
        let : (Kplus.obj.homology q).IsQuasicoherent := by
          change (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace))
            ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).obj K)
          exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
            (eH q) (hE q)
        exact Scheme.Modules.isQuasicoherent_higherDirectImage f
          (Kplus.obj.homology q) p.toNat
      have hEq : P (T.E (p.toNat : ℤ) q) := P.prop_of_iso eK.symm hRq
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ p)] using hEq
  have hpages := qcoh_pages T hsecondQC
  obtain ⟨_, _, H, hH, _, _, _, FH, hconv'⟩ := hconv
  obtain ⟨_, _, _, _, _, _, _, _, _, hFHfull, hFHtop, hFHbot, _, hnegative, hpositive,
    hpositive'⟩ := hconv'
  have hHQ : ∀ n : ℤ, P (H n) := by
    intro n
    apply property_of_filtration P
      (fun (C : ShortComplex B) hC h₁ h₃ ↦ by
        let : C.X₁.IsQuasicoherent := h₁
        let : C.X₃.IsQuasicoherent := h₃
        exact Scheme.Modules.isQuasicoherent_of_shortExact (S := C) hC)
      (FH n) (max 0 (n - a + 1)).toNat (hFHtop n 0 (by omega))
    · apply hFHbot
      omega
    · intro p
      by_cases hp : p < 0
      · have hz := (hnegative p (n - p) hp).1
        have heq : p + (n - p) = n := by omega
        rw [heq] at hz
        exact P.prop_of_isZero hz
      · obtain ⟨_, _, psi, grc, _, _, _, _, _⟩ :=
          hpositive p (n - p) (by omega)
        have hqc := hpages (max (p + 3) (n - p - a + 2)).toNat p (n - p)
        have hqc' : P ((FH (p + (n - p))).gradedPiece p) :=
          P.prop_of_iso (grc.symm ≪≫ psi).symm hqc
        have heq : p + (n - p) = n := by omega
        rw [heq] at hqc'
        exact hqc'
  have hcohOut : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor B n).obj
      ((schemeDerivedDirectImage f).obj E)) := by
    intro n
    have hQ : P ((DerivedCategory.homologyFunctor B n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K))) := by
      simpa only [hH] using hHQ n
    exact P.prop_of_iso
      ((DerivedCategory.homologyFunctor B n).mapIso
        ((schemeDerivedDirectImage f).mapIso e)).symm hQ
  change ∀ n : ℤ, P ((DerivedCategory.homologyFunctor B n).obj
      ((schemeDerivedDirectImage f).obj E))
  exact hcohOut

end AlgebraicGeometry
