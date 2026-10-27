/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import WeilConjectures.WeilSheaf.Category
import Sheaf.DeligneLaumon.SimpleFrobeniusEigenembedding
import WeilConjectures.WeilSheaf.GeometricConstituent

/-! # Multiplicity one in the geometric restriction of a simple Weil sheaf

Source: the multiplicity-eigenline argument in the first two paragraphs of
`lem-zl-geometric-constituents-any-base.proof.md`.
(blueprint: lem-zl-geometric-multiplicity-one).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

section Helpers

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} [IrreducibleSpace Y]

-- Compare the given decomposition with a multiplicity-free one. This uses
-- only Schur's nonzero-isomorphism lemma, not scalar Schur's lemma.
private theorem distinct_of_iso_biproduct {n m : ℕ}
    (T : Fin n → AdicSheaf l Y) (U : Fin m → AdicSheaf l Y)
    (hT : ∀ a, IsIrreducibleAdicLocalSystem (T a))
    (hU : ∀ a, IsIrreducibleAdicLocalSystem (U a))
    (hUdist : ∀ a b, Nonempty (U a ≅ U b) → a = b)
    (s : ⨁ T ≅ ⨁ U) : ∀ a b, Nonempty (T a ≅ T b) → a = b := by
  classical
  let f (a : Fin n) := biproduct.ι T a ≫ s.hom
  have hf (a : Fin n) : ∃ c, f a ≫ biproduct.π U c ≠ 0 := by
    by_contra! h
    have hz : f a = 0 := biproduct.hom_ext _ _ (fun c ↦ by simpa using h c)
    have : Mono (f a) := by dsimp [f]; infer_instance
    exact (hT a).2.1 (IsZero.of_mono_eq_zero (f a) hz)
  intro a b ⟨e⟩
  obtain ⟨c, hc⟩ := hf a
  have hi : IsIso (f a ≫ biproduct.π U c) := (hT a).isIso_of_ne_zero (hU c) _ hc
  let g : T a ≅ U c := asIso (f a ≫ biproduct.π U c)
  have hzero (d : Fin m) (hd : d ≠ c) : f b ≫ biproduct.π U d = 0 := by
    by_contra hz
    have : IsIso (f b ≫ biproduct.π U d) := (hT b).isIso_of_ne_zero (hU d) _ hz
    exact hd (hUdist d c ⟨(asIso (f b ≫ biproduct.π U d)).symm ≪≫ e.symm ≪≫ g⟩)
  have hza (d : Fin m) (hd : d ≠ c) : f a ≫ biproduct.π U d = 0 := by
    by_contra hz
    have : IsIso (f a ≫ biproduct.π U d) := (hT a).isIso_of_ne_zero (hU d) _ hz
    exact hd (hUdist d c ⟨(asIso (f a ≫ biproduct.π U d)).symm ≪≫ g⟩)
  let q : T b ⟶ T a := f b ≫ biproduct.π U c ≫ g.inv
  have hfac : f b = q ≫ f a := by
    apply biproduct.hom_ext
    intro d
    by_cases hd : d = c
    · subst d
      simp [q, g]
    · simp [Category.assoc, hzero d hd, hza d hd]
  by_contra hab
  have hid : 𝟙 (T b) = 0 := by
    have h := congrArg (fun z ↦ z ≫ s.inv ≫ biproduct.π T b) hfac
    simpa [f, hab] using h
  exact (hT b).2.1 ((IsZero.iff_id_eq_zero _).2 hid)

-- A sum of embeddings of pairwise nonisomorphic simple local systems is mono.
private theorem mono_desc_distinct {n : ℕ} (U : Fin n → AdicSheaf l Y)
    (hU : ∀ a, IsIrreducibleAdicLocalSystem (U a))
    (hUdist : ∀ a b, Nonempty (U a ≅ U b) → a = b)
    (Z : AdicSheaf l Y) (hZ : IsAdicLisseSheaf Z)
    (j : ∀ a, U a ⟶ Z) (hj : ∀ a, Mono (j a)) : Mono (biproduct.desc j) := by
  classical
  let w := biproduct.desc j
  have hW := IsAdicLisseSheaf.biproduct_fin n U fun a ↦ (hU a).1
  have hK := (hW.kernel_cokernel_of_irreducibleSpace hZ w).1
  apply Preadditive.mono_of_isZero_kernel
  by_contra hK0
  obtain ⟨R, z, hz, hR⟩ := hK.exists_mono_isIrreducibleAdicLocalSystem hK0
  let p : R ⟶ ⨁ U := z ≫ kernel.ι w
  have hp : Mono p := by dsimp [p]; infer_instance
  obtain ⟨a, ha⟩ : ∃ a, p ≫ biproduct.π U a ≠ 0 := by
    by_contra! h
    have hp0 : p = 0 := biproduct.hom_ext _ _ (fun a ↦ by simpa using h a)
    exact hR.2.1 (IsZero.of_mono_eq_zero p hp0)
  have : IsIso (p ≫ biproduct.π U a) := hR.isIso_of_ne_zero (hU a) _ ha
  let e : R ≅ U a := asIso (p ≫ biproduct.π U a)
  have hzero (b : Fin n) (hb : b ≠ a) : p ≫ biproduct.π U b = 0 := by
    by_contra h
    have : IsIso (p ≫ biproduct.π U b) := hR.isIso_of_ne_zero (hU b) _ h
    exact hb (hUdist b a ⟨(asIso (p ≫ biproduct.π U b)).symm ≪≫ e⟩)
  have hfac : p = e.hom ≫ biproduct.ι U a := by
    apply biproduct.hom_ext
    intro b
    by_cases hb : a = b
    · subst b; simp [e]
    · simp [hb, hzero b (Ne.symm hb)]
  have hcomp : e.hom ≫ j a = 0 := by
    rw [← biproduct.ι_desc j a, ← Category.assoc, ← hfac]
    simp [p, w]
  have : Mono (j a) := hj a
  have : Mono (e.hom ≫ j a) := inferInstance
  exact hR.2.1 (IsZero.of_mono_eq_zero _ hcomp)

end Helpers

section FrobeniusOrbit

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

private noncomputable abbrev Q (n : ℕ) :=
  ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X n

private noncomputable def qzero : Q (k₀ := k₀) (l := l) (X := X) 0 ≅ 𝟭 _ :=
  adicLowerStarCongr l (by rw [pow_zero]; rfl) ≪≫ adicLowerStarId l _

private noncomputable def qsucc (n : ℕ) :
    Q (k₀ := k₀) (l := l) (X := X) (n + 1) ≅ Q n ⋙ frobeniusPullback k₀ l X :=
  adicLowerStarCongr l (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]) ≪≫
    (adicLowerStarComp l _ _).symm

private noncomputable def qadd (a b : ℕ) :
    Q (k₀ := k₀) (l := l) (X := X) (a + b) ≅ Q a ⋙ Q b :=
  adicLowerStarCongr l (by rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]) ≪≫
    (adicLowerStarComp l _ _).symm

omit [Fact (ringChar k₀ ≠ l)]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] in
private theorem q_irreducible
    {S : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hS : IsIrreducibleAdicLocalSystem S) (n : ℕ) :
    IsIrreducibleAdicLocalSystem ((Q n).obj S) := by
  induction n with
  | zero => exact hS.of_iso (qzero.app S).symm
  | succ n ih =>
    exact (isIrreducibleAdicLocalSystem_frobeniusPullback_obj ih).of_iso
      ((qsucc n).app S).symm

omit [Fact (ringChar k₀ ≠ l)]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] in
private theorem period_of_pair
    (S : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {a b : ℕ} (hab : a ≤ b) (e : (Q a).obj S ≅ (Q b).obj S) :
    Nonempty ((Q (b - a)).obj S ≅ S) := by
  let c : (Q b).obj S ≅ (Q a).obj ((Q (b - a)).obj S) :=
    eqToIso (congrArg (fun n ↦ (Q n).obj S) (by omega : b = b - a + a)) ≪≫
      (qadd (b - a) a).app S
  exact ⟨((Q a).preimageIso (e ≪≫ c)).symm⟩

-- A finite semisimple carrier makes every embedded simple isomorphism class
-- periodic. Take its least positive period to get distinct translates.
private theorem exists_least_period
    (V : WeilSheaf k₀ l X) {n : ℕ}
    (T : Fin n → AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hT : ∀ a, IsIrreducibleAdicLocalSystem (T a)) (s : V.obj.carrier ≅ ⨁ T)
    (S : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hS : IsIrreducibleAdicLocalSystem S) (j : S ⟶ V.obj.carrier) [Mono j] :
    ∃ d, 0 < d ∧ Nonempty ((Q d).obj S ≅ S) ∧
      ∀ a b : Fin d, Nonempty ((Q a.val).obj S ≅ (Q b.val).obj S) → a = b := by
  classical
  let jn (m : ℕ) := (Q m).map j ≫ (V.obj.frobeniusPowIso m).hom ≫ s.hom
  have hjn (m : ℕ) : Mono (jn m) := by dsimp [jn, Q]; infer_instance
  have hfactor (m : ℕ) : ∃ a, Nonempty ((Q m).obj S ≅ T a) := by
    obtain ⟨a, ha⟩ : ∃ a, jn m ≫ biproduct.π T a ≠ 0 := by
      by_contra! h
      have hz : jn m = 0 := biproduct.hom_ext _ _ (fun a ↦ by simpa using h a)
      exact (q_irreducible hS m).2.1 (IsZero.of_mono_eq_zero (jn m) hz)
    have : IsIso (jn m ≫ biproduct.π T a) :=
      (q_irreducible hS m).isIso_of_ne_zero (hT a) _ ha
    exact ⟨a, ⟨asIso (jn m ≫ biproduct.π T a)⟩⟩
  choose t ht using hfactor
  have hnot := Fintype.not_injective_of_card_lt (fun a : Fin (n + 1) ↦ t a.val)
    (by simp)
  obtain ⟨a, b, heq, hab⟩ := Function.not_injective_iff.1 hnot
  have hex : ∃ d, 0 < d ∧ Nonempty ((Q d).obj S ≅ S) := by
    have e : Nonempty ((Q a.val).obj S ≅ (Q b.val).obj S) :=
      ⟨(ht a.val).some ≪≫ eqToIso (congrArg T heq) ≪≫ (ht b.val).some.symm⟩
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b.val - a.val, by omega, period_of_pair S (Nat.le_of_lt h) e.some⟩
    · exact ⟨a.val - b.val, by omega, period_of_pair S (Nat.le_of_lt h) e.some.symm⟩
  let d := Nat.find hex
  have hd := Nat.find_spec hex
  refine ⟨d, hd.1, hd.2, ?_⟩
  intro a b ⟨e⟩
  by_contra hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact Nat.find_min hex (by omega : b.val - a.val < d)
      ⟨by omega, period_of_pair S (Nat.le_of_lt h) e⟩
  · exact Nat.find_min hex (by omega : a.val - b.val < d)
      ⟨by omega, period_of_pair S (Nat.le_of_lt h) e.symm⟩

end FrobeniusOrbit

set_option maxHeartbeats 800000 in
-- Dependent finite-index transports and iterated-pullback comparisons need extra elaboration.
/-- In a finite simple decomposition of the geometric carrier of an irreducible
lisse Weil sheaf, no two distinct summands are isomorphic.

Source: blueprint `sec-deligne-laumon-general/sk-lem-wgen-geometric-constituents/`
`lem-zl-geometric-constituents-any-base.proof.md`, paragraphs 1--2.
(blueprint: lem-zl-geometric-multiplicity-one).

Proof: Choose an embedded simple factor S. Every Frobenius translate of S
embeds in the carrier, so a nonzero projection identifies it with some factor
of the given finite decomposition. Pigeonhole and cancellation of a Frobenius
power give a positive period. Choose the least positive period d; its first d
translates are pairwise nonisomorphic. Apply the eigenembedding lemma to the
finite-dimensional space Hom(S,V): replace the embedding by a nonzero
eigenvector for the d-th return. Sum its first d translates. This sum embeds:
a nonzero kernel would contain a simple local system whose projections can
meet only one summand, contradicting injectivity of that summand's embedding.
The return shifts the translates and closes at d by the eigenvector equation.
Its restriction is invertible because it is mono between lisse sheaves of the
same rank. Thus the sum is a nonzero lisse Weil subobject, hence all of V.
Finally compare the resulting multiplicity-free decomposition with the given
one. Schur's nonzero-isomorphism lemma forces an embedding of any simple factor
into just one summand of the multiplicity-free decomposition. Two isomorphic
factors in the given decomposition would factor through that same summand;
composing with the original biproduct projections gives a contradiction. -/
theorem geometric_factors_pairwise_nonisomorphic
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    (N : ℕ) (T : Fin N → AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hT : ∀ i, IsIrreducibleAdicLocalSystem (T i)) (vT : V.obj.carrier ≅ ⨁ T) :
    ∀ a b, Nonempty (T a ≅ T b) → a = b := by
  classical
  have hn : 0 < N := by
    by_contra h
    have hN : N = 0 := by omega
    subst N
    exact hV.2.1 (isZero_iff_isZero_carrier.2
      ((isZero_biproduct_fin_zero T).of_iso vT))
  let a₀ : Fin N := ⟨0, hn⟩
  let S := T a₀
  let j : S ⟶ V.obj.carrier := biproduct.ι T a₀ ≫ vT.inv
  have hj : Mono j := by dsimp [j]; infer_instance
  obtain ⟨d, hd, ⟨e⟩, hdist⟩ := exists_least_period V T hT vT S (hT a₀) j
  obtain ⟨j', hj', e', he'⟩ :=
    exists_simple_frobenius_eigenembedding V hV.1 S (hT a₀) j d e
  let F := frobeniusPullback k₀ l X
  let U (a : Fin d) := (Q a.val).obj S
  have hU (a : Fin d) : IsIrreducibleAdicLocalSystem (U a) := q_irreducible (hT a₀) a.val
  let i (n : ℕ) : (Q n).obj S ⟶ V.obj.carrier :=
    (Q n).map j' ≫ (V.obj.frobeniusPowIso n).hom
  have him (n : ℕ) : Mono (i n) := by dsimp [i, Q]; infer_instance
  have hi0 : i 0 = (qzero.app S).hom ≫ j' := by
    exact qzero.hom.naturality j'
  have hitrans {m n : ℕ} (h : m = n) :
      eqToHom (congrArg (fun r ↦ (Q r).obj S) h) ≫ i n = i m := by
    subst n
    simp
  have his (n : ℕ) :
      (qsucc n).inv.app S ≫ i (n + 1) = F.map (i n) ≫ V.obj.str.hom := by
    dsimp [i]
    have hφ : (V.obj.frobeniusPowIso (n + 1)).hom =
        (qsucc n).hom.app V.obj.carrier ≫
          F.map (V.obj.frobeniusPowIso n).hom ≫ V.obj.str.hom := rfl
    rw [hφ, ← Category.assoc, ← Category.assoc,
      ← (qsucc n).inv.naturality j']
    simp [Functor.map_comp, F]
  let W := ⨁ U
  have hW : IsAdicLisseSheaf W :=
    IsAdicLisseSheaf.biproduct_fin d U fun a ↦ (hU a).1
  let w : W ⟶ V.obj.carrier := biproduct.desc fun a ↦ i a.val
  have hw : Mono w := mono_desc_distinct U hU hdist V.obj.carrier hV.1 _ fun a ↦ him a.val
  let u (a : Fin d) : F.obj (U a) ⟶ W :=
    (qsucc a.val).inv.app S ≫
      if h : a.val + 1 < d then biproduct.ι U ⟨a.val + 1, h⟩ else
        eqToHom (congrArg (fun n ↦ (Q n).obj S) (by omega : a.val + 1 = d)) ≫
          e'.hom ≫ (qzero.app S).inv ≫ biproduct.ι U ⟨0, hd⟩
  have hu (a : Fin d) : u a ≫ w = F.map (i a.val) ≫ V.obj.str.hom := by
    dsimp only [u]
    split_ifs with h
    · simpa [w, Category.assoc] using his a.val
    · have ha : a.val + 1 = d := by omega
      have he : e'.hom ≫ j' = i d := he'
      simp only [Category.assoc, w, biproduct.ι_desc]
      change (qsucc a.val).inv.app S ≫ eqToHom _ ≫ e'.hom ≫
        (qzero.app S).inv ≫ i 0 = _
      rw [hi0, Iso.inv_hom_id_assoc, ← Category.assoc, he]
      rw [Category.assoc, hitrans ha]
      exact his a.val
  let t : F.obj W ⟶ W := (F.mapBiproduct U).hom ≫ biproduct.desc u
  have ht : t ≫ w = F.map w ≫ V.obj.str.hom := by
    apply (cancel_epi (F.mapBiproduct U).inv).1
    simp only [t, Category.assoc, Iso.inv_hom_id_assoc]
    rw [Functor.mapBiproduct_inv]
    apply biproduct.hom_ext'
    intro a
    simpa [w, ← F.map_comp_assoc] using hu a
  have htm : Mono t := by
    have : Mono (t ≫ w) := by rw [ht]; infer_instance
    exact mono_of_mono t w
  obtain ⟨y⟩ := (inferInstance : Nonempty (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y
  have htiso : IsIso t :=
    (isAdicLisseSheaf_frobeniusPullback_obj hW).isIso_of_mono_of_finrank_eq hW t s
      (finrank_geometricStalkFunctor_frobeniusPullback_obj hW s)
  let G : WeilSheaf k₀ l X :=
    ⟨Endofunctor.IsoAlgebra.mk W (asIso t), hW.isAdicConstructibleSheaf⟩
  let g : G ⟶ V := ObjectProperty.homMk (ObjectProperty.homMk ⟨w, ht.symm⟩)
  have hg : Mono g := by
    have : Mono ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).map g) := hw
    exact (ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).mono_of_mono_map this
  have hG0 : ¬ IsZero G := by
    intro hz
    have hzW : IsZero W := isZero_iff_isZero_carrier.1 hz
    exact (hU ⟨0, hd⟩).2.1 (IsZero.of_mono (biproduct.ι U ⟨0, hd⟩) hzW)
  have hgiso : IsIso g := (hV.2.2 G g hg hW).resolve_left hG0
  have hwiso : IsIso w := inferInstanceAs
    (IsIso ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).map g))
  exact distinct_of_iso_biproduct T U hT hU hdist (vT.symm ≪≫ (asIso w).symm)

end AlgebraicGeometry.WeilSheaf
