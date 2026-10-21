/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.Algebra.Homology.FlatResolutionTorComparison
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# The integral bounded Kunneth short exact sequence

Source: Stacks Project, More on Algebra, Tags 0H7Z and 0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact).

`ModuleCat (ULift ℤ)` represents abelian groups in any universe: the scalar action is the
unique integral action, transported along the ring isomorphism `ULift ℤ ≃+* ℤ`.
The lift allows the coefficient ring and module carriers to have the same universe,
as required by the existing module tensor. Coproducts here are direct sums.
The tensor on the derived category is the existing K-flat derived monoidal tensor,
whose restriction to a fixed second complex computes the functor of Tag 06Y6.
-/

@[expose] public section

universe u v w

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped ZeroObject

namespace IntegralKunnethProof
variable {C : Type u} [Category.{v} C] [Abelian C]

/- Zero differentials give canonical, natural identifications with homology. These
   identifications will transport every later page back to the second page. -/
private noncomputable def zeroDifferentialIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : ι)
    (hf : K.dFrom i = 0) (ht : K.dTo i = 0) : K.X i ≅ K.homology i :=
  (K.iCyclesIso i _ rfl hf).symm ≪≫ K.isoHomologyπ _ i rfl ht

@[reassoc]
private theorem zeroDifferentialIso_naturality {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι)
    (hf : K.dFrom i = 0) (ht : K.dTo i = 0)
    (hf' : L.dFrom i = 0) (ht' : L.dTo i = 0) :
    f.f i ≫ (zeroDifferentialIso L i hf' ht').hom =
      (zeroDifferentialIso K i hf ht).hom ≫ HomologicalComplex.homologyMap f i := by
  have := K.isIso_iCycles i _ rfl hf
  apply (cancel_epi (K.iCycles i)).1
  simp only [zeroDifferentialIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.isoHomologyπ_hom,
    ← Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id, Category.id_comp]
  rw [← HomologicalComplex.cyclesMap_i]
  simp only [Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
    HomologicalComplex.homologyπ_naturality]

private noncomputable def stepIso (E : E₂CohomologicalSpectralSequence C) (n : ℕ)
    (i : ℤ × ℤ) (hz : ∀ i j, (E.page (2 + n) (by omega)).d i j = 0) :
    (E.page (2 + n) (by omega)).X i ≅
      (E.page (2 + (n + 1 : ℕ)) (by omega)).X i :=
  zeroDifferentialIso _ i (hz _ _) (hz _ _) ≪≫
    E.iso (2 + n) (2 + (n + 1 : ℕ)) i (by push_cast; omega) (by omega)

private theorem twoColumn_d_zero (r : ℤ) (hr : 2 ≤ r)
    (K : HomologicalComplex C (ComplexShape.up' (r, 1 - r)))
    (hz : ∀ p q : ℤ, p ≠ -1 → p ≠ 0 → IsZero (K.X (p, q)))
    (i j : ℤ × ℤ) : K.d i j = 0 := by
  by_cases h : (ComplexShape.up' (r, 1 - r)).Rel i j
  · have hij : i.1 + r = j.1 := by
      have h' : i + (r, 1-r) = j := h
      exact congrArg Prod.fst h'
    by_cases hi : i.1 = -1 ∨ i.1 = 0
    · exact (hz j.1 j.2 (by omega) (by omega)).eq_of_tgt _ _
    · exact (hz i.1 i.2 (by omega) (by omega)).eq_of_src _ _
  · exact K.shape i j h

private theorem twoColumn_support (E : E₂CohomologicalSpectralSequence C)
    (h₂ : ∀ p q : ℤ, p ≠ -1 → p ≠ 0 → IsZero ((E.page 2).X (p, q)))
    (n : ℕ) (p q : ℤ) (hp : p ≠ -1) (hp' : p ≠ 0) :
    IsZero ((E.page (2 + n) (by omega)).X (p, q)) := by
  induction n with
  | zero => exact h₂ p q hp hp'
  | succ n ih =>
    apply IsZero.of_iso _ (E.iso (2 + n) (2 + (n + 1 : ℕ)) (p, q)
      (by push_cast; omega) (by omega)).symm
    exact (HomologicalComplex.ExactAt.of_isZero ih).isZero_homology

private theorem twoColumn_zero (E : E₂CohomologicalSpectralSequence C)
    (h₂ : ∀ p q : ℤ, p ≠ -1 → p ≠ 0 → IsZero ((E.page 2).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (i j : ℤ × ℤ) : (E.page r hr).d i j = 0 := by
  apply twoColumn_d_zero r hr
  intro p q hp hp'
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = 2 + n := ⟨(r - 2).toNat, by omega⟩
  exact twoColumn_support E h₂ n p q hp hp'

private noncomputable def pageIso (E : E₂CohomologicalSpectralSequence C)
    (hz : ∀ (r : ℤ) (hr : 2 ≤ r) i j, (E.page r hr).d i j = 0)
    (i : ℤ × ℤ) : ∀ n : ℕ, (E.page 2).X i ≅ (E.page (2 + n) (by omega)).X i
  | 0 => Iso.refl _
  | n + 1 => (pageIso E hz i n) ≪≫
      stepIso E n i (hz _ _)

@[reassoc]
private theorem stepIso_naturality {E E' : E₂CohomologicalSpectralSequence C}
    (f : E ⟶ E') (n : ℕ) (i : ℤ × ℤ)
    (hz : ∀ i j, (E.page (2 + n) (by omega)).d i j = 0)
    (hz' : ∀ i j, (E'.page (2 + n) (by omega)).d i j = 0) :
    (f.hom (2 + n) (by omega)).f i ≫ (stepIso E' n i hz').hom =
      (stepIso E n i hz).hom ≫ (f.hom (2 + (n + 1 : ℕ)) (by omega)).f i := by
  dsimp only [stepIso, Iso.trans_hom]
  rw [zeroDifferentialIso_naturality_assoc (f.hom (2 + n) (by omega)) i
    (hz _ _) (hz _ _) (hz' _ _) (hz' _ _),
    f.comm (2 + n) (2 + (n + 1 : ℕ)) i (by push_cast; omega) (by omega)]
  simp only [Category.assoc]

@[reassoc]
private theorem pageIso_naturality {E E' : E₂CohomologicalSpectralSequence C}
    (f : E ⟶ E')
    (hz : ∀ (r : ℤ) (hr : 2 ≤ r) i j, (E.page r hr).d i j = 0)
    (hz' : ∀ (r : ℤ) (hr : 2 ≤ r) i j, (E'.page r hr).d i j = 0)
    (i : ℤ × ℤ) (n : ℕ) :
    (f.hom 2).f i ≫ (pageIso E' hz' i n).hom =
      (pageIso E hz i n).hom ≫ (f.hom (2 + n) (by omega)).f i := by
  induction n with
  | zero => simp [pageIso]
  | succ n ih =>
    dsimp only [pageIso, Iso.trans_hom]
    rw [← Category.assoc, ih, Category.assoc, stepIso_naturality f n i (hz _ _) (hz' _ _)]
    simp only [Category.assoc]

/- Successor coherence makes the graded comparison independent of the sufficiently
   late page chosen. This is needed when the stabilization threshold varies with the objects. -/
private theorem stableIso (E : E₂CohomologicalSpectralSequence C)
    (hz : ∀ (r : ℤ) (hr : 2 ≤ r) i j, (E.page r hr).d i j = 0)
    (i : ℤ × ℤ) {A : C} (N : ℕ)
    (e : ∀ (n : ℕ) (_hn : N ≤ n), A ≅ (E.page (2 + n) (by omega)).X i)
    (he : ∀ (n : ℕ) (hn : N ≤ n),
      (E.page (2 + n) (by omega)).iCycles i ≫ (e n hn).inv =
        (E.page (2 + n) (by omega)).homologyπ i ≫
          (E.iso (2 + n) (2 + (n + 1 : ℕ)) i (by push_cast; omega) (by omega)).hom ≫
            (e (n + 1) (by omega)).inv) :
    ∃ a : A ≅ (E.page 2).X i, ∀ (n : ℕ) (hn : N ≤ n),
      a.hom ≫ (pageIso E hz i n).hom = (e n hn).hom := by
  let a := fun n hn ↦ pageIso E hz i n ≪≫ (e n hn).symm
  have hstep (n : ℕ) (hn : N ≤ n) :
      (e n hn).inv = (stepIso E n i (hz _ _)).hom ≫
        (e (n + 1) (by omega)).inv := by
    have := (E.page (2 + n) (by omega)).isIso_iCycles i _ rfl (hz _ _ _ _)
    apply (cancel_epi ((E.page (2 + n) (by omega)).iCycles i)).1
    simpa only [stepIso, zeroDifferentialIso, Iso.trans_hom, Iso.symm_hom,
      HomologicalComplex.isoHomologyπ_hom, ← Category.assoc,
      HomologicalComplex.iCyclesIso_hom_inv_id, Category.id_comp] using he n hn
  have hconst (n : ℕ) (hn : N ≤ n) : a N (le_refl _) = a n hn := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [ih]
      apply Iso.ext
      dsimp only [a, Iso.trans_hom, Iso.symm_hom, pageIso]
      rw [hstep n hn]
      simp only [Category.assoc]
  refine ⟨(a N (le_refl _)).symm, ?_⟩
  intro n hn
  rw [hconst n hn]
  simp only [a, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/- A finite filtration with only two nonzero graded pieces is a short exact sequence.
   Work with the given subobjects and their cokernels, without choosing representatives. -/
private theorem filtration_step_eq {A : C} (F : DecreasingFiltration A) (p : ℤ)
    (hz : IsZero (F.gr p)) : F.F (p + 1) = F.F p := by
  have : Epi (Subobject.ofLE _ _ (F.F_succ_le p)) := Preadditive.epi_of_isZero_cokernel _ hz
  have : IsIso (Subobject.ofLE _ _ (F.F_succ_le p)) := isIso_of_mono_of_epi _
  apply le_antisymm (F.F_succ_le p)
  apply Subobject.le_of_comm (inv (Subobject.ofLE _ _ (F.F_succ_le p)))
  rw [← Subobject.ofLE_arrow (F.F_succ_le p), IsIso.inv_hom_id_assoc]

private theorem filtration_interval_eq {A : C} (F : DecreasingFiltration A)
    (a b : ℤ) (hab : a ≤ b)
    (hz : ∀ p : ℤ, a ≤ p → p < b → IsZero (F.gr p)) : F.F a = F.F b := by
  induction b, hab using Int.leInduction with
  | base => rfl
  | succ b hb ih =>
    exact (ih (fun p hp hp' ↦ hz p hp (by omega))).trans
      (filtration_step_eq F b (hz b hb (by omega))).symm

private theorem filtration_twoColumn_bounds {A : C} (F : DecreasingFiltration A)
    (hfinite : ∃ a b : ℤ, F.F a = ⊤ ∧ F.F b = ⊥)
    (hz : ∀ p : ℤ, p ≠ -1 → p ≠ 0 → IsZero (F.gr p)) :
    F.F (-1) = ⊤ ∧ F.F 1 = ⊥ := by
  obtain ⟨a, b, ha, hb⟩ := hfinite
  constructor
  · by_cases h : a ≤ -1
    · rw [← filtration_interval_eq F a (-1) h (fun p _ hp ↦ hz p (by omega) (by omega))]
      exact ha
    · apply top_unique
      rw [← ha]
      exact F.antitone (by omega)
  · by_cases h : 1 ≤ b
    · rw [filtration_interval_eq F 1 b h (fun p hp _ ↦ hz p (by omega) (by omega))]
      exact hb
    · apply bot_unique
      rw [← hb]
      exact F.antitone (by omega)

private noncomputable def filtrationLeft {A : C} (F : DecreasingFiltration A) (hb : F.F 1 = ⊥) :
    F.gr 0 ⟶ A := by
  have hz : IsZero (F.F 1 : C) := by
    rw [hb]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  have : IsIso (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0))) :=
    cokernel.π_of_zero (hz.eq_of_src _ _)
  exact inv (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0))) ≫ (F.F 0).arrow

@[reassoc]
private theorem filtrationLeft_fac {A : C} (F : DecreasingFiltration A) (hb : F.F 1 = ⊥) :
    cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0)) ≫ filtrationLeft F hb =
      (F.F 0).arrow := by
  simp [filtrationLeft]

private noncomputable def filtrationRight {A : C} (F : DecreasingFiltration A) (ht : F.F (-1) = ⊤) :
    A ⟶ F.gr (-1) := by
  have : IsIso (F.F (-1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ht
  exact inv (F.F (-1)).arrow ≫ cokernel.π (Subobject.ofLE _ _ (F.F_succ_le (-1)))

@[reassoc]
private theorem filtrationRight_fac {A : C} (F : DecreasingFiltration A) (ht : F.F (-1) = ⊤) :
    (F.F (-1)).arrow ≫ filtrationRight F ht =
      cokernel.π (Subobject.ofLE _ _ (F.F_succ_le (-1))) := by
  simp [filtrationRight]

private theorem filtrationLeft_comp_right {A : C} (F : DecreasingFiltration A)
    (hb : F.F 1 = ⊥) (ht : F.F (-1) = ⊤) :
    filtrationLeft F hb ≫ filtrationRight F ht = 0 := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0)))).1
  rw [filtrationLeft_fac_assoc, comp_zero]
  have hi := Subobject.ofLE_arrow (F.F_succ_le (-1))
  change Subobject.ofLE _ _ (F.F_succ_le (-1)) ≫ (F.F (-1)).arrow = (F.F 0).arrow at hi
  rw [← hi, Category.assoc, filtrationRight_fac, cokernel.condition]

private noncomputable def filtrationShortComplex {A : C} (F : DecreasingFiltration A)
    (hb : F.F 1 = ⊥) (ht : F.F (-1) = ⊤) : ShortComplex C :=
  ShortComplex.mk (filtrationLeft F hb) (filtrationRight F ht)
    (filtrationLeft_comp_right F hb ht)

private theorem filtrationShortComplex_shortExact {A : C} (F : DecreasingFiltration A)
    (hb : F.F 1 = ⊥) (ht : F.F (-1) = ⊤) :
    (filtrationShortComplex F hb ht).ShortExact := by
  have hz : IsZero (F.F 1 : C) := by
    rw [hb]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  have : IsIso (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0))) :=
    cokernel.π_of_zero (hz.eq_of_src _ _)
  have : IsIso (F.F (-1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ht
  let j := Subobject.ofLE _ _ (F.F_succ_le (-1))
  let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hs : S.ShortExact := ⟨ShortComplex.exact_cokernel j⟩
  apply ShortComplex.shortExact_of_iso _ hs
  refine ShortComplex.isoMk (asIso (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0))))
    (asIso (F.F (-1)).arrow) (Iso.refl _) ?_ ?_
  · change cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0)) ≫
        filtrationLeft F hb = j ≫ (F.F (-1)).arrow
    rw [filtrationLeft_fac]
    exact (Subobject.ofLE_arrow (F.F_succ_le (-1))).symm
  · simp only [S, Iso.refl_hom, Category.comp_id,
      filtrationShortComplex, asIso_hom, filtrationRight_fac, j]

@[reassoc]
private theorem filtrationLeft_naturality {A A' : C} (F : DecreasingFiltration A)
    (F' : DecreasingFiltration A') (hb : F.F 1 = ⊥) (hb' : F'.F 1 = ⊥)
    (h : A ⟶ A') (a : (F.F 0 : C) ⟶ (F'.F 0 : C)) (b : F.gr 0 ⟶ F'.gr 0)
    (ha : a ≫ (F'.F 0).arrow = (F.F 0).arrow ≫ h)
    (hbmap : cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0)) ≫ b =
      a ≫ cokernel.π (Subobject.ofLE _ _ (F'.F_succ_le 0))) :
    b ≫ filtrationLeft F' hb' = filtrationLeft F hb ≫ h := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le 0)))).1
  rw [← Category.assoc, hbmap, Category.assoc, filtrationLeft_fac,
    filtrationLeft_fac_assoc, ha]

@[reassoc]
private theorem filtrationRight_naturality {A A' : C} (F : DecreasingFiltration A)
    (F' : DecreasingFiltration A') (ht : F.F (-1) = ⊤) (ht' : F'.F (-1) = ⊤)
    (h : A ⟶ A') (a : (F.F (-1) : C) ⟶ (F'.F (-1) : C))
    (b : F.gr (-1) ⟶ F'.gr (-1))
    (ha : a ≫ (F'.F (-1)).arrow = (F.F (-1)).arrow ≫ h)
    (hbmap : cokernel.π (Subobject.ofLE _ _ (F.F_succ_le (-1))) ≫ b =
      a ≫ cokernel.π (Subobject.ofLE _ _ (F'.F_succ_le (-1)))) :
    h ≫ filtrationRight F' ht' = filtrationRight F ht ≫ b := by
  have : IsIso (F.F (-1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ht
  apply (cancel_epi (F.F (-1)).arrow).1
  rw [← Category.assoc, ← ha, Category.assoc, filtrationRight_fac,
    filtrationRight_fac_assoc, hbmap]

end IntegralKunnethProof

namespace IntegralKunnethProof
section Tor
variable {R : Type u} [CommRing R]

/- An epimorphic projective presentation has torsion-free kernel over a Bezout domain.
   Its explicit two-term complex is a flat resolution; only vanishing uses this choice. -/
private noncomputable def shortResolution {P M : ModuleCat.{u} R} (f : P ⟶ M) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ match n with
    | 0 => P
    | 1 => ModuleCat.of R (LinearMap.ker f.hom)
    | _ + 2 => 0)
    (fun n ↦ match n with
    | 0 => ModuleCat.ofHom (LinearMap.ker f.hom).subtype
    | _ + 1 => 0)
    (by intro n; cases n <;> simp)

private noncomputable def shortAugmentation {P M : ModuleCat.{u} R} (f : P ⟶ M) :
    shortResolution f ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨f, by
    simp only [shortResolution]
    ext x
    exact x.property⟩

private theorem shortAugmentation_quasiIso {P M : ModuleCat.{u} R} (f : P ⟶ M) [Epi f] :
    QuasiIso (shortAugmentation f) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)).2
    constructor
    · apply (ShortComplex.moduleCat_exact_iff _).2
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · simpa [HomologicalComplex.shortComplexFunctor', HomologicalComplex.sc',
        shortAugmentation] using (inferInstance : Epi f)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ (n + 1) (ChainComplex.exactAt_succ_single_obj _ _)]
    cases n with
    | zero =>
      rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
      apply (ShortComplex.moduleCat_exact_iff _).2
      intro x hx
      have hx' : x.val = 0 := hx
      have hx'' : x = 0 := Subtype.ext hx'
      exact ⟨0, by simpa using hx''.symm⟩
    | succ n =>
      apply HomologicalComplex.ExactAt.of_isZero
      exact isZero_zero _

private noncomputable def torZeroIso (M N : ModuleCat.{u} R) :
    ((Tor' (ModuleCat.{u} R) 0).obj M).obj N ≅ M ⊗ N := by
  have : PreservesFiniteColimits (tensorRight N) := inferInstance
  exact (tensorRight N).leftDerivedZeroIsoSelf.app M

/- Naturality in the second Tor variable comes from a natural transformation of
   tensor functors. Compute its degree-zero comparison on a projective resolution. -/
set_option backward.defeqAttrib.useBackward true in
private theorem fromLeftDerivedZero_naturality_functor
    {F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R}
    [F.Additive] [G.Additive] (α : F ⟶ G) (M : ModuleCat.{u} R) :
    (NatTrans.leftDerived α 0).app M ≫ G.fromLeftDerivedZero.app M =
      F.fromLeftDerivedZero.app M ≫ α.app M := by
  let P := projectiveResolution M
  rw [P.leftDerived_app_eq, P.fromLeftDerivedZero_eq, P.fromLeftDerivedZero_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply congrArg (fun k ↦ (P.isoLeftDerivedObj F 0).hom ≫ k)
  dsimp only [ChainComplex.isoHomologyι₀]
  simp only [HomologicalComplex.isoHomologyι_hom]
  change HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α _).app P.complex) 0 ≫ _ = _
  rw [HomologicalComplex.homologyι_naturality_assoc]
  apply congrArg (fun k ↦ _ ≫ k)
  apply (cancel_epi (HomologicalComplex.pOpcycles
    ((F.mapHomologicalComplex _).obj P.complex) 0)).1
  simp only [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  exact (α.naturality (P.π.f 0)).symm

@[reassoc]
private theorem torZeroIso_naturality {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((Tor' (ModuleCat.{u} R) 0).map f).app N ≫
        ((Tor' (ModuleCat.{u} R) 0).obj M').map g ≫ (torZeroIso M' N').hom =
      (torZeroIso M N).hom ≫ (f ⊗ₘ g) := by
  dsimp only [torZeroIso, Functor.leftDerivedZeroIsoSelf, asIso_hom]
  change ((tensorRight N).leftDerived 0).map f ≫
    (NatTrans.leftDerived ((tensoringRight (ModuleCat.{u} R)).map g) 0).app M' ≫
      (tensorRight N').fromLeftDerivedZero.app M' =
    (tensorRight N).fromLeftDerivedZero.app M ≫ (f ⊗ₘ g)
  rw [fromLeftDerivedZero_naturality_functor]
  rw [← Category.assoc, NatTrans.naturality, Category.assoc]
  congr 1
  change (f ⊗ₘ 𝟙 N) ≫ (𝟙 M' ⊗ₘ g) = f ⊗ₘ g
  rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/- No finite-generation assumption enters the higher-Tor vanishing argument. -/
variable [IsDomain R] [IsBezout R]

private theorem higherTor_isZero (M N : ModuleCat.{u} R) (j : ℕ) (hj : 2 ≤ j) :
    IsZero (((Tor' (ModuleCat.{u} R) j).obj M).obj N) := by
  let P := projectiveResolution M
  let f := P.π.f 0
  have : Epi f := inferInstance
  have : Module.Flat R (P.complex.X 0) := Module.Flat.of_projective
  have : Module.IsTorsionFree R (P.complex.X 0) := inferInstance
  have hk : Module.Flat R (LinearMap.ker f.hom) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have hf (i : ℕ) : Module.Flat R ((shortResolution f).X i) := by
    cases i with
    | zero => change Module.Flat R (P.complex.X 0); infer_instance
    | succ i => cases i with
      | zero => exact hk
      | succ i => change Module.Flat R (0 : ModuleCat.{u} R); infer_instance
  have : QuasiIso (shortAugmentation f) := shortAugmentation_quasiIso f
  obtain ⟨e⟩ := ModuleCat.flatResolution_torComparison M _ (shortAugmentation f) hf N j
  apply IsZero.of_iso _ e
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  change IsZero ((0 : ModuleCat.{u} R) ⊗ N)
  exact Functor.map_isZero (tensorRight N) (isZero_zero _)

end Tor

end IntegralKunnethProof

namespace DerivedCategory

/-- Abelian groups of size `u`, encoded as modules over the canonically lifted integers.
Source: Stacks Project, Tag 0H80 (blueprint: lem-kun-integral-bounded-kunneth-exact). -/
abbrev IntegralModuleCat : Type (u + 1) := ModuleCat.{u} (ULift.{u} ℤ)

variable [HasDerivedCategory.{w} IntegralModuleCat.{u}]

/-- The tensor direct sum in degree `r` of the integral Kunneth sequence.
Source: Stacks Project, Tag 0H80 (blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTensorTerm (r : ℤ)
    (C D : Bounded IntegralModuleCat.{u}) : IntegralModuleCat.{u} :=
  ∐ fun p : {p : ℤ × ℤ // p.1 + p.2 = r} ↦
    (homologyFunctor IntegralModuleCat.{u} p.val.1).obj C.obj ⊗
      (homologyFunctor IntegralModuleCat.{u} p.val.2).obj D.obj

/-- The Tor-one direct sum, indexed by total cohomological degree `r + 1`.
Source: Stacks Project, Tag 0H80 (blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTorTerm (r : ℤ)
    (C D : Bounded IntegralModuleCat.{u}) : IntegralModuleCat.{u} :=
  ∐ fun p : {p : ℤ × ℤ // p.1 + p.2 = r + 1} ↦
    ((Tor' IntegralModuleCat.{u} 1).obj
      ((homologyFunctor IntegralModuleCat.{u} p.val.1).obj C.obj)).obj
        ((homologyFunctor IntegralModuleCat.{u} p.val.2).obj D.obj)

/-- The direct sum of the ordinary tensor maps induced by two derived morphisms.
Source: Stacks Project, Tags 0H7Z/0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTensorMap (r : ℤ)
    {C C' D D' : Bounded IntegralModuleCat.{u}} (f : C ⟶ C') (g : D ⟶ D') :
    integralKunnethTensorTerm r C D ⟶ integralKunnethTensorTerm r C' D' :=
  Limits.Sigma.map fun p ↦
    (homologyFunctor IntegralModuleCat.{u} p.val.1).map f.hom ⊗ₘ
      (homologyFunctor IntegralModuleCat.{u} p.val.2).map g.hom

/-- The direct sum of the first-variable-derived Tor maps induced by two morphisms.
Source: Stacks Project, Tags 00LY and 0H7Z/0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTorMap (r : ℤ)
    {C C' D D' : Bounded IntegralModuleCat.{u}} (f : C ⟶ C') (g : D ⟶ D') :
    integralKunnethTorTerm r C D ⟶ integralKunnethTorTerm r C' D' :=
  Limits.Sigma.map fun p ↦
    ((Tor' IntegralModuleCat.{u} 1).map
      ((homologyFunctor IntegralModuleCat.{u} p.val.1).map f.hom)).app
        ((homologyFunctor IntegralModuleCat.{u} p.val.2).obj D.obj) ≫
    ((Tor' IntegralModuleCat.{u} 1).obj
      ((homologyFunctor IntegralModuleCat.{u} p.val.1).obj C'.obj)).map
        ((homologyFunctor IntegralModuleCat.{u} p.val.2).map g.hom)

open IntegralKunnethProof

private theorem integralPage_isZero (C D : Bounded IntegralModuleCat.{u}) (p q : ℤ)
    (hp : p ≠ -1) (hp' : p ≠ 0) :
    IsZero (kunnethTorPage (ULift.{u} ℤ) p q C D) := by
  have : IsDomain (ULift.{u} ℤ) := ULift.ringEquiv.toMulEquiv.isDomain ℤ
  have : IsPrincipalIdealRing (ULift.{u} ℤ) :=
    IsPrincipalIdealRing.of_surjective
      (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom ULift.ringEquiv.symm.surjective
  apply (IsZero.iff_id_eq_zero _).2
  apply Sigma.hom_ext
  intro ij
  simp only [comp_zero]
  have hz : IsZero (((kunnethIntegerTor (ULift.{u} ℤ) (-p)).obj
    ((homologyFunctor IntegralModuleCat.{u} ij.val.1).obj C.obj)).obj
      ((homologyFunctor IntegralModuleCat.{u} ij.val.2).obj D.obj)) := by
    by_cases h : 0 < p
    · simp only [kunnethIntegerTor, show -p < 0 by omega, if_pos]
      exact isZero_zero _
    · simp only [kunnethIntegerTor, show ¬-p < 0 by omega]
      exact higherTor_isZero _ _ _ (by omega)
  exact hz.eq_of_src _ _

private noncomputable def tensorPageIso (r : ℤ) (C D : Bounded IntegralModuleCat.{u}) :
    kunnethTorPage (ULift.{u} ℤ) 0 r C D ≅ integralKunnethTensorTerm r C D :=
  Sigma.mapIso fun _ij ↦ torZeroIso _ _

@[reassoc]
private theorem tensorPageIso_naturality (r : ℤ)
    {C C' D D' : Bounded IntegralModuleCat.{u}} (f : C ⟶ C') (g : D ⟶ D') :
    kunnethTorPageMap (ULift.{u} ℤ) 0 r f g ≫ (tensorPageIso r C' D').hom =
      (tensorPageIso r C D).hom ≫ integralKunnethTensorMap r f g := by
  apply Sigma.hom_ext
  intro ij
  dsimp only [kunnethTorPageMap, integralKunnethTensorMap, tensorPageIso]
  simp only [Category.assoc, Sigma.ι_map, Sigma.ι_map_assoc,
    Sigma.ι_mapIso_hom, Sigma.ι_mapIso_hom_assoc]
  exact torZeroIso_naturality_assoc
    ((homologyFunctor IntegralModuleCat.{u} ij.val.1).map f.hom)
    ((homologyFunctor IntegralModuleCat.{u} ij.val.2).map g.hom) _

private noncomputable def torPageIso (r : ℤ) (C D : Bounded IntegralModuleCat.{u}) :
    kunnethTorPage (ULift.{u} ℤ) (-1) (r + 1) C D ≅ integralKunnethTorTerm r C D :=
  Iso.refl _

@[reassoc]
private theorem torPageIso_naturality (r : ℤ)
    {C C' D D' : Bounded IntegralModuleCat.{u}} (f : C ⟶ C') (g : D ⟶ D') :
    kunnethTorPageMap (ULift.{u} ℤ) (-1) (r + 1) f g ≫ (torPageIso r C' D').hom =
      (torPageIso r C D).hom ≫ integralKunnethTorMap r f g := by
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  rfl

set_option maxHeartbeats 1000000 in
-- Dependent page indices and naturality comparisons need additional elaboration heartbeats.
/-- For bounded derived abelian groups the integral Kunneth sequence is short exact,
with both arrows natural in both derived arguments. No finite generation is assumed.
Source: Stacks Project, More on Algebra, Tags 0H7Z and 0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact).

Proof (the five DAG steps):
1. Apply `lem-kun-bounded-tensor-tor-spectral-sequence` over the integers. Its second page
   is the direct sum of Tor in bidegree `(p,q)`, with Tor degree `-p` and `i+j=q`.
   It converges with a finite natural decreasing filtration to derived-tensor cohomology.
2. Resolve any abelian group M by a projective group mapping onto M and its kernel.
   Projectivity gives flatness and torsion-freeness; the kernel is torsion free, hence flat by
   `lem-weil-pbc-pid-torsion-free-module-flat`. This is a two-term flat resolution;
   `lem-pc-flat-resolution-tor-comparison` proves Tor vanishes in degrees at least two.
   Neither group needs to be finitely generated.
3. Only columns -1 and 0 of the spectral sequence remain. All differentials from page
   two onward have zero source or target, so the successor-page homology rule of
   `def-sp-spectral-sequence` gives canonical stationary-page identifications. Tor-zero
   is the ordinary tensor of `def-weil-pbc-tor-modules`.
4. In the finite decreasing filtration of `def-sp-filtration`, vanishing of the other
   graded pieces implies F^1=0 and F^{-1}=H^r. Inclusion of F^0 and the quotient by F^0
   give the sequence. The two graded identifications give precisely the tensor sum
   in degree r and the Tor-one sum in degree r+1.
5. Functoriality of the spectral sequence preserves F^0 and commutes with its graded
   identifications. The inclusion and quotient squares commute, and their outside
   maps are exactly the direct sums of cohomological tensor and Tor maps below.
   No choice of a splitting is made. -/
theorem integral_bounded_kunneth_exact (r : ℤ) :
    ∃ ι : ∀ C D : Bounded IntegralModuleCat.{u},
        integralKunnethTensorTerm r C D ⟶
          (homologyFunctor IntegralModuleCat.{u} r).obj (C.obj ⊗ D.obj),
    ∃ π : ∀ C D : Bounded IntegralModuleCat.{u},
        (homologyFunctor IntegralModuleCat.{u} r).obj (C.obj ⊗ D.obj) ⟶
          integralKunnethTorTerm r C D,
      (∀ C D : Bounded IntegralModuleCat.{u},
        Function.Injective (ι C D) ∧ Function.Exact (ι C D) (π C D) ∧
          Function.Surjective (π C D)) ∧
      (∀ (C C' D D' : Bounded IntegralModuleCat.{u}) (f : C ⟶ C') (g : D ⟶ D'),
        integralKunnethTensorMap r f g ≫ ι C' D' =
          ι C D ≫ (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom)) ∧
      (∀ (C C' D D' : Bounded IntegralModuleCat.{u}) (f : C ⟶ C') (g : D ⟶ D'),
        (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom) ≫ π C' D' =
          π C D ≫ integralKunnethTorMap r f g) := by
  classical
  obtain ⟨S, F, N, hN, e₂, eInf, hfinite, h₂, _, hsucc, hnat⟩ :=
    bounded_tensor_tor_spectral_sequence.{u, w} (ULift.{u} ℤ)
  let E := fun C D ↦ (S.obj C).obj D
  have hz (C D : Bounded IntegralModuleCat.{u}) (t : ℤ) (ht : 2 ≤ t) (i j : ℤ × ℤ) :
      ((E C D).page t ht).d i j = 0 := by
    apply twoColumn_zero
    intro p q hp hp'
    exact (integralPage_isZero C D p q hp hp').of_iso (e₂ C D p q)
  let NN := fun C D n p ↦ (N C D n p - 2).toNat
  have he (C D : Bounded IntegralModuleCat.{u}) (n p : ℤ) :
      ∃ a : (F C D n).gr p ≅ ((E C D).page 2 (by decide)).X (p, n - p),
        ∀ (k : ℕ) (hk : NN C D n p ≤ k),
          a.hom ≫ (pageIso (E C D) (hz C D) (p, n - p) k).hom =
            (eInf C D n p (2 + k) (by omega) (by dsimp [NN] at hk; omega)).hom := by
    apply stableIso (E C D) (hz C D) (p, n - p) (NN C D n p)
    intro k hk
    exact hsucc C D n p (2 + k) (by omega) (by dsimp [NN] at hk; omega)
  choose a ha using he
  let e := fun C D n p ↦ a C D n p ≪≫ e₂ C D p (n - p)
  have hgrzero (C D : Bounded IntegralModuleCat.{u}) (n p : ℤ)
      (hp : p ≠ -1) (hp' : p ≠ 0) : IsZero ((F C D n).gr p) :=
    (integralPage_isZero C D p (n - p) hp hp').of_iso (e C D n p)
  have hb (C D : Bounded IntegralModuleCat.{u}) :
      (F C D r).F (-1) = ⊤ ∧ (F C D r).F 1 = ⊥ :=
    filtration_twoColumn_bounds (F C D r) (hfinite C D r) (hgrzero C D r)
  let e0 (C D : Bounded IntegralModuleCat.{u}) :
      (F C D r).gr 0 ≅ kunnethTorPage (ULift.{u} ℤ) 0 r C D :=
    e C D r 0 ≪≫ eqToIso (congrArg
      (fun q ↦ kunnethTorPage (ULift.{u} ℤ) 0 q C D) (sub_zero r))
  let e1 (C D : Bounded IntegralModuleCat.{u}) :
      (F C D r).gr (-1) ≅ kunnethTorPage (ULift.{u} ℤ) (-1) (r + 1) C D :=
    e C D r (-1) ≪≫ eqToIso (congrArg
      (fun q ↦ kunnethTorPage (ULift.{u} ℤ) (-1) q C D) (Int.sub_neg r 1))
  let eL := fun C D ↦ e0 C D ≪≫ tensorPageIso r C D
  let eR := fun C D ↦ e1 C D ≪≫ torPageIso r C D
  let ι := fun C D ↦ (eL C D).inv ≫ filtrationLeft (F C D r) (hb C D).2
  let π := fun C D ↦ filtrationRight (F C D r) (hb C D).1 ≫ (eR C D).hom
  have hnatArrows (C C' D D' : Bounded IntegralModuleCat.{u})
      (f : C ⟶ C') (g : D ⟶ D') :
      (integralKunnethTensorMap r f g ≫ ι C' D' =
        ι C D ≫ (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom)) ∧
      ((homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom) ≫ π C' D' =
        π C D ≫ integralKunnethTorMap r f g) := by
    obtain ⟨aa, bb, haa, hbb, hbbInf⟩ := hnat C C' D D' f g
    have heNat (n p : ℤ) : bb n p ≫ (e C' D' n p).hom =
        (e C D n p).hom ≫ kunnethTorPageMap (ULift.{u} ℤ) p (n - p) f g := by
      let k := max (NN C D n p) (NN C' D' n p)
      have hk : NN C D n p ≤ k := le_max_left _ _
      have hk' : NN C' D' n p ≤ k := le_max_right _ _
      have hi : bb n p ≫ (a C' D' n p).hom =
          (a C D n p).hom ≫
            (((S.map f).app D ≫ (S.obj C').map g).hom 2 (by decide)).f (p, n - p) := by
        apply (cancel_mono (pageIso (E C' D') (hz C' D') (p, n - p) k).hom).1
        rw [Category.assoc, ha C' D' n p k hk', Category.assoc,
          pageIso_naturality ((S.map f).app D ≫ (S.obj C').map g)
            (hz C D) (hz C' D') (p, n - p) k,
          ← Category.assoc, ha C D n p k hk]
        exact hbbInf n p (2 + k) (by omega) (by dsimp [NN] at hk; omega)
          (by dsimp [NN] at hk'; omega)
      dsimp only [e, Iso.trans_hom]
      rw [← Category.assoc, hi, Category.assoc, h₂ C C' D D' f g p (n - p)]
      simp only [Category.assoc]
    constructor
    · have heL : bb r 0 ≫ (eL C' D').hom =
          (eL C D).hom ≫ integralKunnethTensorMap r f g := by
        dsimp only [eL, Iso.trans_hom]
        have h0 : bb r 0 ≫ (e0 C' D').hom =
            (e0 C D).hom ≫ kunnethTorPageMap (ULift.{u} ℤ) 0 r f g := by
          dsimp only [e0, Iso.trans_hom, eqToIso.hom]
          rw [← Category.assoc, heNat r 0, Category.assoc,
            eqToHom_naturality
              (fun q ↦ kunnethTorPageMap (ULift.{u} ℤ) 0 q f g) (sub_zero r)]
          simp only [Category.assoc]
        rw [← Category.assoc, h0, Category.assoc, tensorPageIso_naturality]
        simp only [Category.assoc]
      have hi : integralKunnethTensorMap r f g ≫ (eL C' D').inv =
          (eL C D).inv ≫ bb r 0 := by
        apply (Iso.comp_inv_eq (eL C' D')).2
        rw [Category.assoc, heL, Iso.inv_hom_id_assoc]
      change integralKunnethTensorMap r f g ≫
          ((eL C' D').inv ≫ filtrationLeft (F C' D' r) (hb C' D').2) =
        ((eL C D).inv ≫ filtrationLeft (F C D r) (hb C D).2) ≫
          (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom)
      rw [← Category.assoc, hi, Category.assoc,
        filtrationLeft_naturality (F C D r) (F C' D' r) (hb C D).2 (hb C' D').2
          _ (aa r 0) (bb r 0) (haa r 0) (hbb r 0)]
      simp only [Category.assoc]
    · have heR : bb r (-1) ≫ (eR C' D').hom =
          (eR C D).hom ≫ integralKunnethTorMap r f g := by
        dsimp only [eR, Iso.trans_hom]
        have h1 : bb r (-1) ≫ (e1 C' D').hom =
            (e1 C D).hom ≫ kunnethTorPageMap (ULift.{u} ℤ) (-1) (r + 1) f g := by
          dsimp only [e1, Iso.trans_hom, eqToIso.hom]
          rw [← Category.assoc, heNat r (-1), Category.assoc,
            eqToHom_naturality
              (fun q ↦ kunnethTorPageMap (ULift.{u} ℤ) (-1) q f g) (Int.sub_neg r 1)]
          simp only [Category.assoc]
        rw [← Category.assoc, h1, Category.assoc, torPageIso_naturality]
        simp only [Category.assoc]
      change (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom) ≫
          (filtrationRight (F C' D' r) (hb C' D').1 ≫ (eR C' D').hom) =
        (filtrationRight (F C D r) (hb C D).1 ≫ (eR C D).hom) ≫
          integralKunnethTorMap r f g
      rw [← Category.assoc,
        filtrationRight_naturality (F C D r) (F C' D' r) (hb C D).1 (hb C' D').1
          _ (aa r (-1)) (bb r (-1))
          (haa r (-1)) (hbb r (-1)), Category.assoc, heR]
      simp only [Category.assoc]
  refine ⟨ι, π, ?_, ?_, ?_⟩
  · intro C D
    have hS := filtrationShortComplex_shortExact (F C D r) (hb C D).2 (hb C D).1
    have hzero : ι C D ≫ π C D = 0 := by
      dsimp only [ι, π]
      rw [Category.assoc, ← Category.assoc (filtrationLeft _ _) (filtrationRight _ _),
        filtrationLeft_comp_right, zero_comp, comp_zero]
    let T := ShortComplex.mk (ι C D) (π C D) hzero
    have heT : filtrationShortComplex (F C D r) (hb C D).2 (hb C D).1 ≅ T := by
      refine ShortComplex.isoMk (eL C D) (Iso.refl _) (eR C D) ?_ ?_
      · simp [T, ι, filtrationShortComplex]
      · simp [T, π, filtrationShortComplex]
    have ht := ShortComplex.shortExact_of_iso heT hS
    exact ⟨ht.injective_f,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).1 ht.exact,
      ht.surjective_g⟩
  · intro C C' D D' f g
    exact (hnatArrows C C' D D' f g).1
  · intro C C' D D' f g
    exact (hnatArrows C C' D D' f g).2

end DerivedCategory
