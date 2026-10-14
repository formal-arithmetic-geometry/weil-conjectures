/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Int.Interval

/-! # Finite blocks in a flat telescope

Source: the finite-cone-block paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-compact-flat-telescope-blocks).

The degreewise splittings are explicit coproduct projections. Compactness is used
only in the proved finite-piece factorization theorem, never to supply block data.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace FlatTelescopeBlocks

variable {Y : Scheme.{u}}
  (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (t : ∀ n : ℕ, E n ⟶ E (n + 1))

noncomputable def sum (n : ℕ) := ∐ (fun k : Fin (n + 1) ↦ E k)

noncomputable def inclusion (n : ℕ) : sum E n ⟶ sum E (n + 1) :=
  Sigma.desc (fun k : Fin (n + 1) ↦ Sigma.ι (fun j : Fin (n + 2) ↦ E j) k.castSucc)

noncomputable def inclusionAll (n : ℕ) : sum E n ⟶ ∐ E :=
  Sigma.desc (fun k : Fin (n + 1) ↦ Sigma.ι E k)

noncomputable def shift (n : ℕ) : sum E n ⟶ sum E (n + 1) :=
  Sigma.desc (fun k : Fin (n + 1) ↦ t k ≫ Sigma.ι (fun j : Fin (n + 2) ↦ E j) k.succ)

noncomputable def differential (n : ℕ) : sum E n ⟶ sum E (n + 1) :=
  inclusion E n - shift E t n

lemma differential_inclusionAll (n : ℕ) :
    differential E t n ≫ inclusionAll E (n + 1) =
      inclusionAll E n ≫ flatTelescopeDifferential E t := by
  apply Sigma.hom_ext
  intro k
  simp [differential, inclusion, shift, inclusionAll, flatTelescopeDifferential,
    Preadditive.comp_sub, Preadditive.sub_comp]

lemma differential_inclusion (n : ℕ) :
    differential E t n ≫ inclusion E (n + 1) =
      inclusion E n ≫ differential E t (n + 1) := by
  apply Sigma.hom_ext
  intro k
  simp [differential, inclusion, shift, Preadditive.comp_sub, Preadditive.sub_comp]

noncomputable def block (n : ℕ) := CochainComplex.mappingCone (differential E t n)

noncomputable def toTelescope (n : ℕ) :
    block E t n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t) :=
  CochainComplex.mappingCone.map (differential E t n) (flatTelescopeDifferential E t)
    (inclusionAll E n) (inclusionAll E (n + 1)) (differential_inclusionAll E t n)

noncomputable def transition (n : ℕ) : block E t n ⟶ block E t (n + 1) :=
  CochainComplex.mappingCone.map (differential E t n) (differential E t (n + 1))
    (inclusion E n) (inclusion E (n + 1)) (differential_inclusion E t n)

lemma inclusion_inclusionAll (n : ℕ) :
    inclusion E n ≫ inclusionAll E (n + 1) = inclusionAll E n := by
  apply Sigma.hom_ext
  intro k
  simp [inclusion, inclusionAll]

lemma transition_toTelescope (n : ℕ) :
    transition E t n ≫ toTelescope E t (n + 1) = toTelescope E t n := by
  dsimp [transition, toTelescope]
  rw [← CochainComplex.mappingCone.map_comp]
  simp only [inclusion_inclusionAll]

noncomputable def projectionAll (n : ℕ) : ∐ E ⟶ sum E n :=
  Sigma.desc (fun k : ℕ ↦ if h : k < n + 1 then
    Sigma.ι (fun j : Fin (n + 1) ↦ E j) ⟨k, h⟩ else 0)

lemma inclusionAll_projectionAll (n : ℕ) :
    inclusionAll E n ≫ projectionAll E n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro k
  simp only [inclusionAll, projectionAll, Sigma.ι_desc_assoc, Sigma.ι_desc,
    dif_pos k.isLt]
  simp [sum]

instance inclusionAll_split (n : ℕ) : IsSplitMono (inclusionAll E n) :=
  IsSplitMono.mk' ⟨projectionAll E n, inclusionAll_projectionAll E n⟩

instance inclusion_split (n : ℕ) : IsSplitMono (inclusion E n) :=
  IsSplitMono.mk' ⟨inclusionAll E (n + 1) ≫ projectionAll E n, by
    rw [← Category.assoc, inclusion_inclusionAll, inclusionAll_projectionAll]⟩

set_option backward.isDefEq.respectTransparency false in
lemma cone_map_split
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {K L K' L' : CochainComplex A ℤ} (d : K ⟶ L) (d' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : d ≫ b = a ≫ d') (i : ℤ)
    [IsSplitMono (a.f (i + 1))] [IsSplitMono (b.f i)] :
    IsSplitMono ((CochainComplex.mappingCone.map d d' a b h).f i) := by
  classical
  let e := HomologicalComplex.homotopyCofiber.XIsoBiprod d i (i + 1) rfl
  let e' := HomologicalComplex.homotopyCofiber.XIsoBiprod d' i (i + 1) rfl
  refine IsSplitMono.mk' ⟨e'.hom ≫
    biprod.map (retraction (a.f (i + 1))) (retraction (b.f i)) ≫ e.inv, ?_⟩
  apply (cancel_mono e.hom).1
  apply CochainComplex.mappingCone.ext_from d (i + 1) i rfl
  · simp only [Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    simp [e, e', CochainComplex.mappingCone.inl]
  · simp only [Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f]
    simp [e, e',
      CochainComplex.mappingCone.inr]

instance toTelescope_split (n : ℕ) (i : ℤ) : IsSplitMono ((toTelescope E t n).f i) := by
  apply cone_map_split

instance transition_split (n : ℕ) (i : ℤ) : IsSplitMono ((transition E t n).f i) := by
  apply cone_map_split

private lemma finite_bound
    (hb : ∀ k : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E k).X i)) (n : ℕ) :
    ∃ b : ℤ, ∀ k : ℕ, k ≤ n → ∀ i : ℤ, b < i → IsZero ((E k).X i) := by
  induction n with
  | zero =>
    obtain ⟨b, h⟩ := hb 0
    exact ⟨b, fun k hk ↦ by obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk; exact h⟩
  | succ n hn =>
    obtain ⟨b, h⟩ := hn
    obtain ⟨b', h'⟩ := hb (n + 1)
    refine ⟨max b b', ?_⟩
    intro k hk i hi
    obtain hk | rfl := Nat.le_succ_iff.mp hk
    · exact h k hk i (lt_of_le_of_lt (le_max_left _ _) hi)
    · exact h' i (lt_of_le_of_lt (le_max_right _ _) hi)

private lemma sum_isZero (n : ℕ) (i : ℤ)
    (h : ∀ k : Fin (n + 1), IsZero ((E k).X i)) : IsZero ((sum E n).X i) := by
  apply IsZero.of_iso _ (PreservesCoproduct.iso
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) (fun k : Fin (n + 1) ↦ E k))
  exact (colimit.isColimit (Discrete.functor _)).isZero_pt
    ((Discrete.functor _).isZero (fun k ↦ h k.as))

lemma block_bounded
    (hb : ∀ k : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E k).X i)) (n : ℕ) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((block E t n).X i) := by
  obtain ⟨b, h⟩ := finite_bound E hb (n + 1)
  refine ⟨b, ?_⟩
  intro i hi
  apply (CochainComplex.mappingCone.isZero_X_iff _ _).mpr
  constructor
  · exact sum_isZero E n (i + 1) (fun k ↦ h k (by lia) (i + 1) (by lia))
  · exact sum_isZero E (n + 1) i (fun k ↦ h k (by lia) i hi)

private lemma flat_of_iso
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)} (e : M ≅ N)
    (hN : SheafOfModules.IsFlat N) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hN

private lemma flat_coproduct_small {K : Type*} [Small.{u} K]
    (M : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : ∀ k : K, SheafOfModules.IsFlat (M k)) : SheafOfModules.IsFlat (∐ M) := by
  apply flat_of_iso (Sigma.reindex (equivShrink K).symm M).symm
  exact SheafOfModules.isFlat_coproduct Y.sheaf _ (fun k ↦ hM _)

private lemma flat_biprod
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    (hM : SheafOfModules.IsFlat M) (hN : SheafOfModules.IsFlat N) :
    SheafOfModules.IsFlat (M ⊞ N) := by
  let G : WalkingPair → SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
    fun k ↦ (Limits.pair M N).obj ⟨k⟩
  apply flat_of_iso ((biprod.isoCoprod M N) ≪≫
    (HasColimit.isoOfNatIso (Discrete.natIso fun _ ↦ Iso.refl _)).symm)
  apply flat_coproduct_small G
  intro k
  cases k <;> assumption

private lemma sum_flat (hf : ∀ k : ℕ, ∀ i : ℤ, SheafOfModules.IsFlat ((E k).X i))
    (n : ℕ) (i : ℤ) : SheafOfModules.IsFlat ((sum E n).X i) := by
  apply flat_of_iso (PreservesCoproduct.iso
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) (fun k : Fin (n + 1) ↦ E k))
  exact flat_coproduct_small _ (fun k ↦ hf k i)

lemma block_flat (hf : ∀ k : ℕ, ∀ i : ℤ, SheafOfModules.IsFlat ((E k).X i))
    (n : ℕ) (i : ℤ) : SheafOfModules.IsFlat ((block E t n).X i) := by
  apply flat_of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod
    (differential E t n) i (i + 1) rfl)
  exact flat_biprod (sum_flat E hf n (i + 1)) (sum_flat E hf (n + 1) i)

private lemma factors_finite_sum
    {A : Type*} [Category* A] [HasZeroMorphisms A] [HasCoproducts.{u} A] [HasCoproducts.{0} A]
    {M : A} {I : Type u} [Finite I] (G : I → A) (e : M ≅ ∐ G)
    (hc : ∀ k : I, ∀ (K : Type u) (H : K → A) (f : G k ⟶ ∐ H),
      ∃ S : Finset K, ∃ g : G k ⟶ ∐ (fun t : {t // t ∈ S} ↦ H t.1),
        g ≫ Sigma.desc (fun t : {t // t ∈ S} ↦ Sigma.ι H t.1) = f)
    (H : ℕ → A) (f : M ⟶ ∐ H) :
    ∃ n : ℕ, ∃ g : M ⟶ ∐ (fun k : Fin (n + 1) ↦ H k),
      g ≫ Sigma.desc (fun k : Fin (n + 1) ↦ Sigma.ι H k) = f := by
  classical
  let H' : ULift.{u} ℕ → A := fun k ↦ H k.down
  let eH : ∐ H' ≅ ∐ H := Sigma.reindex (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) H
  choose S g hg using fun k ↦ hc k (ULift.{u} ℕ) H'
    (Sigma.ι G k ≫ e.inv ≫ f ≫ eH.inv)
  obtain ⟨b, hb⟩ := Finite.exists_le (fun k : (Σ k : I, {t // t ∈ S k}) ↦ k.2.1.down)
  let n := b
  let a (k : I) : ∐ (fun t : {t // t ∈ S k} ↦ H' t.1) ⟶
      ∐ (fun k : Fin (n + 1) ↦ H k) :=
    Sigma.desc (fun t ↦ Sigma.ι (fun k : Fin (n + 1) ↦ H k)
      ⟨t.1.down, Nat.lt_succ_of_le (hb ⟨k, t⟩)⟩)
  refine ⟨n, e.hom ≫ Sigma.desc (fun k ↦ g k ≫ a k), ?_⟩
  rw [← cancel_epi e.inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply Sigma.hom_ext
  intro k
  simp only [Sigma.ι_desc_assoc, Category.assoc]
  have ha : a k ≫ Sigma.desc (fun k : Fin (n + 1) ↦ Sigma.ι H k) =
      Sigma.desc (fun t : {t // t ∈ S k} ↦ Sigma.ι H' t.1) ≫ eH.hom := by
    apply Sigma.hom_ext
    intro j
    simp only [a, Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact (Sigma.ι_reindex_hom (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) H j.1).symm
  rw [ha, ← Category.assoc, hg k]
  simp

noncomputable def inclusionLE {n m : ℕ} (h : n ≤ m) : sum E n ⟶ sum E m :=
  Sigma.desc (fun k : Fin (n + 1) ↦
    Sigma.ι (fun j : Fin (m + 1) ↦ E j) ⟨k, lt_of_lt_of_le k.isLt (Nat.add_le_add_right h 1)⟩)

lemma inclusionLE_inclusionAll {n m : ℕ} (h : n ≤ m) :
    inclusionLE E h ≫ inclusionAll E m = inclusionAll E n := by
  apply Sigma.hom_ext
  intro k
  simp [inclusionLE, inclusionAll]

lemma differential_inclusionLE {n m : ℕ} (h : n ≤ m) :
    differential E t n ≫ inclusionLE E (Nat.add_le_add_right h 1) =
      inclusionLE E h ≫ differential E t m := by
  apply Sigma.hom_ext
  intro k
  simp [differential, inclusion, shift, inclusionLE,
    Preadditive.comp_sub, Preadditive.sub_comp]

noncomputable def transitionLE {n m : ℕ} (h : n ≤ m) : block E t n ⟶ block E t m :=
  CochainComplex.mappingCone.map (differential E t n) (differential E t m)
    (inclusionLE E h) (inclusionLE E (Nat.add_le_add_right h 1))
    (differential_inclusionLE E t h)

lemma transitionLE_toTelescope {n m : ℕ} (h : n ≤ m) :
    transitionLE E t h ≫ toTelescope E t m = toTelescope E t n := by
  dsimp [transitionLE, toTelescope]
  rw [← CochainComplex.mappingCone.map_comp]
  simp only [inclusionLE_inclusionAll]

set_option backward.isDefEq.respectTransparency false in
private lemma component_finite_sum
    {M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    {I : Type u} [Finite I] (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (e : M ≅ ∐ G)
    (hc : ∀ k : I, ∀ (K : Type u) (H : K → SheafOfModules.{u}
      (moduleRings Y.toRingedSpace)) (f : G k ⟶ ∐ H),
      ∃ S : Finset K, ∃ g : G k ⟶ ∐ (fun t : {t // t ∈ S} ↦ H t.1),
        g ≫ Sigma.desc (fun t : {t // t ∈ S} ↦ Sigma.ι H t.1) = f)
    (i : ℤ) (f : M ⟶ (∐ E).X i) :
    ∃ n : ℕ, ∃ g : M ⟶ (sum E n).X i, g ≫ (inclusionAll E n).f i = f := by
  let F := HomologicalComplex.eval
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) i
  let eAll := PreservesCoproduct.iso F E
  obtain ⟨n, g, hg⟩ := factors_finite_sum G e hc (fun k ↦ (E k).X i) (f ≫ eAll.hom)
  let eFin := PreservesCoproduct.iso F (fun k : Fin (n + 1) ↦ E k)
  refine ⟨n, g ≫ eFin.inv, ?_⟩
  apply (cancel_mono eAll.hom).1
  rw [Category.assoc, Category.assoc]
  change g ≫ eFin.inv ≫ F.map (inclusionAll E n) ≫ eAll.hom = _
  have h : eFin.inv ≫ F.map (inclusionAll E n) ≫ eAll.hom =
      Sigma.desc (fun k : Fin (n + 1) ↦ Sigma.ι (fun j ↦ (E j).X i) k) := by
    apply Sigma.hom_ext
    intro k
    simp only [eFin, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc]
    rw [← F.map_comp_assoc]
    simp only [inclusionAll, Sigma.ι_desc]
    have hh : eAll.hom = inv (sigmaComparison F E) := by
      change eAll.hom = inv eAll.inv
      simp
    rw [hh]
    exact map_ι_comp_inv_sigmaComparison F E k
  rw [h, hg]

set_option backward.isDefEq.respectTransparency false in
private lemma toTelescope_f_iso (n : ℕ) (i : ℤ) :
    (toTelescope E t n).f i ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          (flatTelescopeDifferential E t) i (i + 1) rfl).hom =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (differential E t n) i (i + 1) rfl).hom ≫
          biprod.map ((inclusionAll E n).f (i + 1)) ((inclusionAll E (n + 1)).f i) := by
  apply CochainComplex.mappingCone.ext_from (differential E t n) (i + 1) i rfl
  · simp only [toTelescope, Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    simp [CochainComplex.mappingCone.inl]
  · simp only [toTelescope, Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f]
    simp [CochainComplex.mappingCone.inr]

private lemma component_factor
    {M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    {I : Type u} [Finite I] (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (e : M ≅ ∐ G)
    (hc : ∀ k : I, ∀ (K : Type u) (H : K → SheafOfModules.{u}
      (moduleRings Y.toRingedSpace)) (f : G k ⟶ ∐ H),
      ∃ S : Finset K, ∃ g : G k ⟶ ∐ (fun t : {t // t ∈ S} ↦ H t.1),
        g ≫ Sigma.desc (fun t : {t // t ∈ S} ↦ Sigma.ι H t.1) = f)
    (i : ℤ) (f : M ⟶ (CochainComplex.mappingCone (flatTelescopeDifferential E t)).X i) :
    ∃ n : ℕ, ∃ g : M ⟶ (block E t n).X i, g ≫ (toTelescope E t n).f i = f := by
  let eT := HomologicalComplex.homotopyCofiber.XIsoBiprod
    (flatTelescopeDifferential E t) i (i + 1) rfl
  obtain ⟨n₁, g₁, hg₁⟩ := component_finite_sum E G e hc (i + 1) (f ≫ eT.hom ≫ biprod.fst)
  obtain ⟨n₂, g₂, hg₂⟩ := component_finite_sum E G e hc i (f ≫ eT.hom ≫ biprod.snd)
  let n := max n₁ n₂
  let eN := HomologicalComplex.homotopyCofiber.XIsoBiprod
    (differential E t n) i (i + 1) rfl
  let a := g₁ ≫ (inclusionLE E (le_max_left n₁ n₂)).f (i + 1)
  let b := g₂ ≫ (inclusionLE E
    (le_trans (le_max_right n₁ n₂) (Nat.le_succ n))).f i
  refine ⟨n, biprod.lift a b ≫ eN.inv, ?_⟩
  apply (cancel_mono eT.hom).1
  rw [Category.assoc, Category.assoc, toTelescope_f_iso]
  change biprod.lift a b ≫ eN.inv ≫ eN.hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst]
    rw [← Category.assoc, biprod.lift_fst]
    change g₁ ≫ (inclusionLE E _).f (i + 1) ≫ (inclusionAll E n).f (i + 1) = _
    rw [← HomologicalComplex.comp_f, inclusionLE_inclusionAll, hg₁]
  · simp only [Category.assoc, biprod.map_snd]
    rw [← Category.assoc, biprod.lift_snd]
    change g₂ ≫ (inclusionLE E _).f i ≫ (inclusionAll E (n + 1)).f i = _
    rw [← HomologicalComplex.comp_f, inclusionLE_inclusionAll, hg₂]

/-- A finite compact-flat source complex factors through one finite telescope block.

Source: the finite-cone-block paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-factor-telescope-block).

Proof: In a fixed degree, write the source as its given finite coproduct. Each
compact summand factors through a finite subset of each of the two countable
coproducts making up the telescope cone term. Their finitely many supports have
a common natural-number bound. Lift both components into a finite cone block.
The source has only finitely many nonzero degrees, so the degreewise block bounds
have a common bound N. In the other degrees use zero. The degreewise lifts commute
with the differentials because their composites into the telescope do, and its
block inclusions are monomorphisms in every degree. -/
theorem factor_diagram_object
    {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (j : D.index)
    (f : D.diagram.obj j ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t)) :
    ∃ n : ℕ, ∃ g : D.diagram.obj j ⟶ block E t n, g ≫ toTelescope E t n = f := by
  classical
  have term (i : ℤ) : ∃ n : ℕ, ∃ g : (D.diagram.obj j).X i ⟶ (block E t n).X i,
      g ≫ (toTelescope E t n).f i = f.f i := by
    obtain ⟨I, hI, G, ⟨e⟩, _, hc⟩ := D.generators j i
    let := hI
    exact component_factor E t G e hc i (f.f i)
  obtain ⟨lo, hi, hzero⟩ := D.finiteDegrees j
  let S := Finset.Icc lo hi
  choose n g hg using fun i : {i // i ∈ S} ↦ term i.1
  obtain ⟨N, hN⟩ := Finite.exists_le n
  let lift (i : ℤ) : (D.diagram.obj j).X i ⟶ (block E t N).X i :=
    if h : i ∈ S then g ⟨i, h⟩ ≫ (transitionLE E t (hN ⟨i, h⟩)).f i else 0
  have fac (i : ℤ) : lift i ≫ (toTelescope E t N).f i = f.f i := by
    by_cases h : i ∈ S
    · simp only [lift, dif_pos h]
      rw [Category.assoc, ← HomologicalComplex.comp_f, transitionLE_toTelescope]
      exact hg ⟨i, h⟩
    · simp only [lift, dif_neg h, zero_comp]
      apply (hzero i (by
        simp only [S, Finset.mem_Icc] at h
        omega)).eq_of_src
  let g' : D.diagram.obj j ⟶ block E t N :=
    { f := lift
      comm' := by
        intro i k _
        apply (cancel_mono ((toTelescope E t N).f k)).1
        rw [Category.assoc, ← (toTelescope E t N).comm, ← Category.assoc, fac,
          Category.assoc, fac, f.comm] }
  exact ⟨N, g', by apply HomologicalComplex.Hom.ext; funext i; exact fac i⟩

end FlatTelescopeBlocks
end AlgebraicGeometry
