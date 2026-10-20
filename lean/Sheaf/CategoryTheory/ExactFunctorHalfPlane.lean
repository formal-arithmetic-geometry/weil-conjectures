/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import all WeilConjectures.CategoryTheory.FinitePageGradedQuotient
import all WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel

/-! # Transport of half-plane abutments along an exact functor -/

@[expose] public section

set_option autoImplicit false
universe u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
private theorem finite_g_factors (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ) :
    (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q) :=
  Subobject.factors_of_le _ ((L.Z_glb p q).1 ⟨r, rfl⟩)
    (X.g_factors_limitCycles L p q)
private noncomputable def finiteG (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ) :
    X.D p q ⟶ (X.pageCouple r).E p q :=
  (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q)
    (finite_g_factors X L r p q) ≫ X.cycleBoundaryTower.projection r p q
private noncomputable def finiteGCycles (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ) :
    X.D p q ⟶ kernel ((X.pageCouple r).d p q) :=
  (X.cycleBoundaryTower.Z (r + 1) p q).factorThru (X.initialG p q)
    (finite_g_factors X L (r + 1) p q) ≫ X.cycleBoundaryTower.cycleLift r p q
private theorem finiteGCycles_comm (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ) :
    finiteGCycles X L r p q ≫ kernel.ι ((X.pageCouple r).d p q) = finiteG X L r p q := by
  dsimp only [finiteGCycles, finiteG]
  rw [Category.assoc, X.cycleBoundaryTower.cycleLift_comm, ← Category.assoc]
  have h : (X.cycleBoundaryTower.Z (r + 1) p q).factorThru (X.initialG p q)
      (finite_g_factors X L (r + 1) p q) ≫
        Subobject.ofLE _ _ (X.cycleBoundaryTower.Z_decreasing r p q) =
      (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q)
        (finite_g_factors X L r p q) := by
    apply (cancel_mono (X.cycleBoundaryTower.Z r p q).arrow).mp
    simp only [Category.assoc, Subobject.ofLE_arrow, Subobject.factorThru_arrow]
  rw [h]
private theorem finiteG_succ (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ) :
    finiteG X L (r + 1) p q =
      finiteGCycles X L r p q ≫ (X.pageCouple r).derivedEProjection p q := by
  dsimp only [finiteG, finiteGCycles]
  rw [X.cycleBoundaryTower.projection_succ, Category.assoc]
private theorem finiteG_zero (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (p q : ℤ) : finiteG X L 0 p q = X.initialG p q := by
  dsimp only [finiteG]
  rw [X.cycleBoundaryTower.projection_zero, Subobject.factorThru_arrow]
private theorem stable_limits (X : BigradedExactCouple C 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ)
    (hr : (r : ℤ) + 2 > max (q - a + 1) p) :
    X.cycleBoundaryTower.Z r p q = L.Z p q ∧
      X.cycleBoundaryTower.B r p q = L.B p q := by
  let T := X.cycleBoundaryTower
  have hs (t : ℕ) (ht : r ≤ t) :
      T.Z (t + 1) p q = T.Z t p q ∧ T.B (t + 1) p q = T.B t p q := by
    apply tower_stationary X T
    · exact (page_zero X _ _ (hE _ _ (Or.inr (by omega))) t).eq_zero_of_tgt _
    · exact (page_zero X _ _ (hE _ _ (Or.inl (by omega))) t).eq_zero_of_src _
  have htail (t : ℕ) (ht : r ≤ t) :
      T.Z t p q = T.Z r p q ∧ T.B t p q = T.B r p q := by
    induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ t ht ih => exact ⟨(hs t ht).1.trans ih.1, (hs t ht).2.trans ih.2⟩
  constructor
  · apply le_antisymm
    · apply (L.Z_glb p q).2
      rintro _ ⟨t, rfl⟩
      by_cases ht : r ≤ t
      · exact le_of_eq (htail t ht).1.symm
      · exact antitone_nat_of_succ_le (f := fun s ↦ T.Z s p q)
          (fun s ↦ T.Z_decreasing s p q) (by omega)
    · exact (L.Z_glb p q).1 ⟨r, rfl⟩
  · apply le_antisymm
    · exact (L.B_lub p q).1 ⟨r, rfl⟩
    · apply (L.B_lub p q).2
      rintro _ ⟨t, rfl⟩
      by_cases ht : r ≤ t
      · exact le_of_eq (htail t ht).2
      · exact monotone_nat_of_le_succ (f := fun s ↦ T.B s p q)
          (fun s ↦ T.B_increasing s p q) (by omega)
private theorem stable_iso (X : BigradedExactCouple C 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ)
    (hr : (r : ℤ) + 2 > max (q - a + 1) p) :
    ∃ hZ : X.cycleBoundaryTower.Z r p q = L.Z p q,
    ∃ e : (X.pageCouple r).E p q ≅ X.pageInfinity L p q,
    X.cycleBoundaryTower.projection r p q ≫ e.hom =
      eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : C)) hZ) ≫
        cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
          (limitBoundary_le_cycle X L p q)) := by
  obtain ⟨hZ, hB⟩ := stable_limits X a hE L r p q hr
  have := X.cycleBoundaryTower.projection_epi r p q
  have hle : L.Z p q ≤ X.cycleBoundaryTower.Z r p q := le_of_eq hZ.symm
  obtain ⟨e, he⟩ := stabilized_quotient_comparison
    (L.B p q) (L.Z p q)
    (X.cycleBoundaryTower.B r p q) (X.cycleBoundaryTower.Z r p q)
    hB.symm hZ.symm (limitBoundary_le_cycle X L p q)
    (X.cycleBoundaryTower.B_le_Z r p q) hle
    (X.cycleBoundaryTower.projection r p q)
    (X.cycleBoundaryTower.projection_kernel r p q)
  refine ⟨hZ, e.symm, ?_⟩
  apply (cancel_mono e.hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he, ← Category.assoc]
  have ht : eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : C)) hZ) ≫
      Subobject.ofLE _ _ hle = 𝟙 _ := by
    have aux (S T : Subobject (X.E p q)) (h : S = T) (hle : T ≤ S) :
        eqToHom (congrArg (fun U : Subobject (X.E p q) ↦ (U : C)) h) ≫
          Subobject.ofLE T S hle = 𝟙 _ := by
      subst T
      simp
    exact aux _ _ hZ hle
  rw [ht, Category.id_comp]
private theorem finiteG_stable (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ)
    (hZ : X.cycleBoundaryTower.Z r p q = L.Z p q)
    (e : (X.pageCouple r).E p q ≅ X.pageInfinity L p q)
    (he : X.cycleBoundaryTower.projection r p q ≫ e.hom =
      eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : C)) hZ) ≫
        cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
          (limitBoundary_le_cycle X L p q))) :
    finiteG X L r p q ≫ e.hom = X.toPageInfinity L p q := by
  dsimp only [finiteG, toPageInfinity]
  rw [Category.assoc, he, ← Category.assoc]
  congr 1
  apply (cancel_mono (L.Z p q).arrow).mp
  simp only [Category.assoc, Subobject.arrow_congr _ _ hZ, Subobject.factorThru_arrow]

section Naturality
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
omit [Abelian C] [Abelian B] [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
theorem transport_square {F : ℤ → ℤ → C} {G : ℤ → ℤ → B}
    (t : ∀ p q, Φ.obj (F p q) ⟶ G p q)
    {p q p' q' : ℤ} (hp : p = p') (hq : q = q') :
    Φ.map (eqToHom (congrArg₂ F hp hq)) ≫ t p' q' =
      t p q ≫ eqToHom (congrArg₂ G hp hq) := by
  subst p'; subst q'; simp
omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem finiteG_natural
    (X : BigradedExactCouple C 0) (Y : BigradedExactCouple B 0)
    (LX : LimitSubobjects X) (LY : LimitSubobjects Y)
    (hD : ∀ p q, Φ.obj (X.D p q) = Y.D p q)
    (hE : ∀ p q, Φ.obj (X.E p q) = Y.E p q)
    (δ : ∀ r p q, Φ.obj ((X.pageCouple r).D p q) ≅ (Y.pageCouple r).D p q)
    (φ : ∀ r p q, Φ.obj ((X.pageCouple r).E p q) ≅ (Y.pageCouple r).E p q)
    (h0 : ∀ p q, δ 0 p q = eqToIso (hD p q) ∧ φ 0 p q = eqToIso (hE p q))
    (hg : ∀ r p q, Φ.map ((X.pageCouple r).g p q) ≫ (φ r (p + r) (q - r)).hom =
      (δ r p q).hom ≫ (Y.pageCouple r).g p q)
    (hnext : ∀ r p q,
      ∃ k : Φ.obj (kernel ((X.pageCouple r).d p q)) ⟶
        kernel ((Y.pageCouple r).d p q), IsIso k ∧
        k ≫ kernel.ι ((Y.pageCouple r).d p q) =
          Φ.map (kernel.ι ((X.pageCouple r).d p q)) ≫ (φ r p q).hom ∧
        Φ.map ((X.pageCouple r).derivedEProjection p q) ≫ (φ (r + 1) p q).hom =
          k ≫ (Y.pageCouple r).derivedEProjection p q)
    (r : ℕ) (p q : ℤ) :
    Φ.map (finiteG X LX r p q) ≫ (φ r p q).hom =
      eqToHom (hD p q) ≫ finiteG Y LY r p q := by
  induction r with
  | zero =>
    rw [finiteG_zero, finiteG_zero]
    dsimp only [initialG]
    have hg0 := hg 0 p q
    change Φ.map (X.g p q) ≫ (φ 0 (p + 0) (q - 0)).hom =
      (δ 0 p q).hom ≫ Y.g p q at hg0
    rw [Φ.map_comp, Category.assoc,
      transport_square Φ (fun p q ↦ (φ 0 p q).hom) (by omega) (by omega),
      ← Category.assoc]
    erw [hg0, (h0 p q).1]
    simp only [eqToIso.hom, Category.assoc]
  | succ r ih =>
    obtain ⟨k, hk, hki, hkπ⟩ := hnext r p q
    have hc : Φ.map (finiteGCycles X LX r p q) ≫ k =
        eqToHom (hD p q) ≫ finiteGCycles Y LY r p q := by
      apply (cancel_mono (kernel.ι ((Y.pageCouple r).d p q))).mp
      rw [Category.assoc, hki, ← Category.assoc, ← Φ.map_comp,
        finiteGCycles_comm, ih, Category.assoc, finiteGCycles_comm]
    rw [finiteG_succ, finiteG_succ, Φ.map_comp, Category.assoc, hkπ,
      ← Category.assoc, hc, Category.assoc]
end Naturality

private theorem largePage_witness (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q))
    (inc : ∀ r p q, (X.pageCouple r).D p q ⟶ X.D p q)
    (hinc0 : ∀ p q, inc 0 p q = 𝟙 _)
    (hinc : ∀ r p q, inc (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ inc r p q)
    (A : ∀ n : ℤ, AlphaColimit X n)
    (hA : ∀ n, (A n).obj = X.D 0 n)
    (hA0 : ∀ n, (A n).ι 0 ≫ eqToHom (hA n) = eqToHom (by congr 1; omega))
    (r : ℕ) (p q : ℤ) (hr : (r : ℤ) + 2 ≥ max (p + 3) (q - a + 2)) :
    ∃ lambda : (A (p + q)).obj ≅ X.D (p - r) (q + r),
    ∃ t : ((X.imageFiltration (p + q) (A (p + q))).step p : C) ≅
      (X.pageCouple r).D (p - r) (q + r),
    ∃ ψ : (X.imageFiltration (p + q) (A (p + q))).gradedPiece p ≅
      (X.pageCouple r).E p q,
    lambda.inv = eqToHom (by congr 1; omega) ≫ (A (p + q)).ι (p - r) ∧
    t.hom ≫ inc r (p - r) (q + r) =
      ((X.imageFiltration (p + q) (A (p + q))).step p).arrow ≫ lambda.hom ∧
    cokernel.π (Subobject.ofLE
      ((X.imageFiltration (p + q) (A (p + q))).step (p + 1))
      ((X.imageFiltration (p + q) (A (p + q))).step p)
      ((X.imageFiltration (p + q) (A (p + q))).antitone_step (by omega))) ≫ ψ.hom =
      t.hom ≫ (X.pageCouple r).g (p - r) (q + r) ≫
        eqToHom (by congr 1 <;> omega) := by
  classical
  let n := p + q
  let u := p - (r : ℤ)
  let v := q + (r : ℤ)
  let F := X.imageFiltration n (A n)
  let Y := X.pageCouple r
  let c : X.D u v ⟶ (A n).obj :=
    eqToHom (by congr 1; dsimp [n, u, v]; omega) ≫ (A n).ι u
  have : IsIso ((A n).ι u) :=
    cocone_iso_nonpositive X hE n (A n) (hA n) (hA0 n) u (by dsimp [u]; omega)
  have : IsIso c := by dsimp [c]; infer_instance
  let lambda : (A n).obj ≅ X.D u v := (asIso c).symm
  obtain ⟨hmono, himage⟩ := prescribed_inclusion_images X inc hinc0 hinc
  have hmap {S T U : C} (f : S ⟶ T) (m : T ⟶ U) [Mono m] :
      (Subobject.map m).obj (imageSubobject f) = imageSubobject (f ≫ m) := by
    rw [Subobject.map_obj_eq_mk]
    have : StrongEpi (factorThruImageSubobject f) := strongEpi_of_epi _
    symm
    simpa only [imageSubobject_arrow_comp_assoc] using
      Subobject.imageSubobject_eq_mk (factorThruImageSubobject f)
        ((imageSubobject f).arrow ≫ m)
  have hstep (s : ℕ) : (Subobject.map c).obj (imageSubobject (inc s u v)) =
      F.step (u + s) := by
    rw [himage, hmap]
    have hc := incomingAlphaIter_cocone X n (A n) s u v
      (by dsimp [u, v, n]; omega)
    change imageSubobject (X.incomingAlphaIter s u v ≫ c) = _
    have hh : X.incomingAlphaIter s u v ≫ c =
        eqToHom (by congr 1; dsimp [u, v, n]; omega) ≫
          (A n).ι (u + s) := hc
    simp only [hh, imageSubobject_iso_comp]
    rfl
  have : Mono (inc r u v) := hmono r u v
  have : Mono (inc (r + 1) u v) := hmono (r + 1) u v
  have him : Subobject.mk (inc r u v ≫ c) = F.step p := by
    rw [← imageSubobject_mono, ← hmap, hstep]
    congr 1
    dsimp [u]
    omega
  let t : (F.step p : C) ≅ Y.D u v :=
    Subobject.isoOfMkEqMk (F.step p).arrow (inc r u v ≫ c)
      ((Subobject.mk_arrow _).trans him.symm)
  have ht : t.hom ≫ inc r u v = (F.step p).arrow ≫ lambda.hom := by
    apply (cancel_mono c).mp
    simp [t, lambda, Category.assoc]
  let k := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have hkinc : (k ≫ t.hom) ≫ inc r u v = (F.step (p + 1)).arrow ≫ lambda.hom := by
    rw [Category.assoc, ht, ← Category.assoc]
    dsimp [k]
    rw [Subobject.ofLE_arrow]
  have himnext : imageSubobject (inc (r + 1) u v) =
      Subobject.mk ((F.step (p + 1)).arrow ≫ lambda.hom) := by
    apply Subobject.map_obj_injective c
    rw [hstep, Subobject.map_mk]
    simp only [Category.assoc, lambda, Iso.symm_hom, asIso_inv,
      IsIso.inv_hom_id, Category.comp_id, Subobject.mk_arrow]
    congr 1
    dsimp [u]
    omega
  have : Mono (Y.derivedDInclusion u v) := by
    dsimp [derivedDInclusion]
    infer_instance
  have hk : Subobject.mk (k ≫ t.hom) = kernelSubobject (Y.g u v) := by
    apply Subobject.map_obj_injective (inc r u v)
    rw [← derivedDInclusion_kernel Y u v, imageSubobject_mono]
    simp only [Subobject.map_mk, hkinc]
    rw [← himnext]
    change imageSubobject (inc (r + 1) u v) =
      Subobject.mk ((X.pageCouple r).derivedDInclusion u v ≫ inc r u v)
    simp only [← hinc, imageSubobject_mono]
  have hnext : IsZero (Y.D ((u + r) + 2) ((v - r) - 1)) :=
    pageD_zero X a hD r _ _ (by dsimp [u, v]; omega)
  have hf : Y.f (u + r) (v - r) = 0 := hnext.eq_zero_of_tgt _
  have : Epi (Y.g u v) := by
    have himg : imageSubobject (Y.g u v) = ⊤ := by
      rw [Y.exact_f, hf, kernelSubobject_zero]
    have : IsIso (imageSubobject (Y.g u v)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).mpr himg
    rw [← imageSubobject_arrow_comp (Y.g u v)]
    infer_instance
  let z : Y.E (u + r) (v - r) ⟶ Y.E p q :=
    eqToHom (by congr 1 <;> dsimp [u, v] <;> omega)
  let π := t.hom ≫ Y.g u v ≫ z
  have : Epi π := by dsimp [π, z]; infer_instance
  have hker : kernelSubobject π = Subobject.mk k := by
    have hπ : π = (t.hom ≫ Y.g u v) ≫ z := by simp only [π, Category.assoc]
    simp only [hπ, kernelSubobject_comp_mono]
    apply Subobject.map_obj_injective t.hom
    have hmapker : (Subobject.map t.hom).obj (kernelSubobject (t.hom ≫ Y.g u v)) =
        kernelSubobject (Y.g u v) := by
      conv_lhs => rw [← Subobject.mk_arrow (kernelSubobject (t.hom ≫ Y.g u v))]
      rw [Subobject.map_mk, ← Subobject.mk_arrow (kernelSubobject (Y.g u v))]
      exact Subobject.mk_eq_mk_of_comm _ _ (kernelSubobjectIsoComp t.hom (Y.g u v))
        (kernelSubobjectIsoComp_hom_arrow t.hom (Y.g u v))
    rw [hmapker, Subobject.map_mk]
    exact hk.symm
  obtain ⟨ψ, hψ⟩ := quotient_comparison (F.step (p + 1)) (F.step p)
    (F.antitone_step (by omega)) π hker
  exact ⟨lambda, t, ψ, rfl, ht, hψ⟩

/-- The limiting and explicit large-page comparisons are natural once finite-page
and image-filtration comparisons are fixed.

Source: Stacks Project, Homology, Tags 011Q, 011R, 011S, 011T, 012F and 010N;
steps 4--6 of lem-sp-exact-functor-couple.
(blueprint: lem-sp-exact-functor-half-plane)

Proof. Factor the initial g through each finite cycle object and its page projection.
The cycle-lift and next-page projection equations give its successor recurrence.
Induction, cancelling kernel inclusions, proves naturality of these finite g maps.
Half-plane vanishing makes the incoming and outgoing differentials vanish on every
sufficiently large page. The tower recurrence then makes cycles and boundaries
stationary; their infimum and supremum identify this stationary value with L.
The two cokernel presentations give the stable-page-to-infinite-page isomorphism.
The canonical infinite-page-to-graded-piece isomorphism is uniquely fixed by weak
convergence. Define the infinite-page comparison by conjugating kappa through these
isomorphisms. The image-factorization and quotient equations show naturality of the
canonical map to the graded piece, hence of the map to the infinite page. Cancel
the epimorphic finite g map to obtain compatibility with every stable page.

For the large-page witnesses put u=p-r and v=q+r. The normalized cocone map at u
is invertible by negative-first-index E vanishing; take its inverse as lambda.
The cocone equation identifies each incoming alpha iterate, followed by that cocone
map, with the cocone map at its source. The iterated D image formula therefore
identifies D_r(u,v) with filtration step p transported by lambda, giving t.
The next incoming image is similarly step p+1. Exactness identifies it with the
kernel of derived g. The lower D bound makes the following derived D term zero,
so derived g is epic. Its cokernel comparison gives psi and its defining equation.
This argument includes negative p and zero objects without a separate case.
The cocone and inclusion equations imply naturality of lambda and t by cancellation
of isomorphisms and monic D inclusions. Apply the functor to the quotient equation,
use the finite g and graded quotient squares, and cancel the mapped epimorphic
quotient to prove naturality of psi. -/
theorem exactFunctor_halfPlane
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (X : BigradedExactCouple C 0)
    (Y : BigradedExactCouple B 0)
    (hD : ∀ p q : ℤ, Φ.obj (X.D p q) = Y.D p q)
    (hE : ∀ p q : ℤ, Φ.obj (X.E p q) = Y.E p q)
    (δ : ∀ (r : ℕ) (p q : ℤ),
      Φ.obj ((X.pageCouple r).D p q) ≅ (Y.pageCouple r).D p q)
    (φ : ∀ (r : ℕ) (p q : ℤ),
      Φ.obj ((X.pageCouple r).E p q) ≅ (Y.pageCouple r).E p q)
    (iX : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
    (iY : ∀ (r : ℕ) (p q : ℤ), (Y.pageCouple r).D p q ⟶ Y.D p q)
    (H0 : ∀ p q : ℤ, δ 0 p q = eqToIso (hD p q) ∧ φ 0 p q = eqToIso (hE p q))
    (H1 : ∀ p q : ℤ, iX 0 p q = 𝟙 _ ∧ iY 0 p q = 𝟙 _)
    (H2 : ∀ (r : ℕ) (p q : ℤ),
      iX (r + 1) p q = (X.pageCouple r).derivedDInclusion p q ≫ iX r p q ∧
      iY (r + 1) p q = (Y.pageCouple r).derivedDInclusion p q ≫ iY r p q)
    (H3 : ∀ (r : ℕ) (p q : ℤ), Mono (iX r p q) ∧ Mono (iY r p q) ∧
      (δ r p q).hom ≫ iY r p q = Φ.map (iX r p q) ≫ eqToHom (hD p q))
    (H6 : ∀ (r : ℕ) (p q : ℤ),
      Φ.map ((X.pageCouple r).g p q) ≫ (φ r (p + r) (q - r)).hom =
        (δ r p q).hom ≫ (Y.pageCouple r).g p q)
    (H8 : ∀ (r : ℕ) (p q : ℤ),
      ∃ k : Φ.obj (kernel ((X.pageCouple r).d p q)) ⟶
        kernel ((Y.pageCouple r).d p q),
      IsIso k ∧
      k ≫ kernel.ι ((Y.pageCouple r).d p q) =
        Φ.map (kernel.ι ((X.pageCouple r).d p q)) ≫ (φ r p q).hom ∧
      Φ.map ((X.pageCouple r).derivedEProjection p q) ≫ (φ (r + 1) p q).hom =
        k ≫ (Y.pageCouple r).derivedEProjection p q)
    (a : ℤ)
    (hDX : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hEX : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (hDY : ∀ p q : ℤ, q < a → IsZero (Y.D p q))
    (hEY : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (Y.E p q))
    (LX : LimitSubobjects X) (LY : LimitSubobjects Y)
    (AX : ∀ n : ℤ, AlphaColimit X n) (AY : ∀ n : ℤ, AlphaColimit Y n)
    (hAX : ∀ n : ℤ, (AX n).obj = X.D 0 n)
    (hAY : ∀ n : ℤ, (AY n).obj = Y.D 0 n)
    (hAX0 : ∀ n : ℤ, (AX n).ι 0 ≫ eqToHom (hAX n) =
      eqToHom (by congr 1; omega))
    (hAY0 : ∀ n : ℤ, (AY n).ι 0 ≫ eqToHom (hAY n) =
      eqToHom (by congr 1; omega))
    (hconvX : X.ConvergesTo LX AX) (hconvY : Y.ConvergesTo LY AY)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (τ : ∀ n p : ℤ,
        Φ.obj ((X.imageFiltration n (AX n)).step p : C) ≅
          ((Y.imageFiltration n (AY n)).step p : B))
    (κ : ∀ n p : ℤ,
        Φ.obj ((X.imageFiltration n (AX n)).gradedPiece p) ≅
          (Y.imageFiltration n (AY n)).gradedPiece p)
    (hA : ∀ n p : ℤ, Φ.map ((AX n).ι p) ≫ (eA n).hom =
        eqToHom (hD p (n - p)) ≫ (AY n).ι p)
    (hτ : ∀ n p : ℤ,
        (τ n p).hom ≫ ((Y.imageFiltration n (AY n)).step p).arrow =
          Φ.map (((X.imageFiltration n (AX n)).step p).arrow) ≫ (eA n).hom)
    (hκ : ∀ n p : ℤ,
        Φ.map (cokernel.π (Subobject.ofLE
          ((X.imageFiltration n (AX n)).step (p + 1))
          ((X.imageFiltration n (AX n)).step p)
          ((X.imageFiltration n (AX n)).antitone_step (by omega)))) ≫ (κ n p).hom =
        (τ n p).hom ≫ cokernel.π (Subobject.ofLE
          ((Y.imageFiltration n (AY n)).step (p + 1))
          ((Y.imageFiltration n (AY n)).step p)
          ((Y.imageFiltration n (AY n)).antitone_step (by omega))))
    :
      (∃ φInfinity : ∀ p q : ℤ, Φ.obj (X.pageInfinity LX p q) ≅ Y.pageInfinity LY p q,
        (∀ p q : ℤ, Φ.map (X.toPageInfinity LX p q) ≫ (φInfinity p q).hom =
          eqToHom (hD p q) ≫ Y.toPageInfinity LY p q) ∧
        (∀ (r : ℕ) (p q : ℤ), (r : ℤ) + 2 > max (q - a + 1) p →
          ∃ hZX : X.cycleBoundaryTower.Z r p q = LX.Z p q,
          ∃ hZY : Y.cycleBoundaryTower.Z r p q = LY.Z p q,
          ∃ eX : (X.pageCouple r).E p q ≅ X.pageInfinity LX p q,
          ∃ eY : (Y.pageCouple r).E p q ≅ Y.pageInfinity LY p q,
          X.cycleBoundaryTower.projection r p q ≫ eX.hom =
            eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : C)) hZX) ≫
              cokernel.π (Subobject.ofLE (LX.B p q) (LX.Z p q)
                (limitBoundary_le_cycle X LX p q)) ∧
          Y.cycleBoundaryTower.projection r p q ≫ eY.hom =
            eqToHom (congrArg (fun S : Subobject (Y.E p q) ↦ (S : B)) hZY) ≫
              cokernel.π (Subobject.ofLE (LY.B p q) (LY.Z p q)
                (limitBoundary_le_cycle Y LY p q)) ∧
          Φ.map eX.hom ≫ (φInfinity p q).hom = (φ r p q).hom ≫ eY.hom) ∧
        ∀ p q : ℤ,
          ∃ ξX : X.pageInfinity LX p q ≅
            (X.imageFiltration (p + q) (AX (p + q))).gradedPiece p,
          ∃ ξY : Y.pageInfinity LY p q ≅
            (Y.imageFiltration (p + q) (AY (p + q))).gradedPiece p,
          X.toPageInfinity LX p q ≫ ξX.hom = X.toGradedPiece AX p q ∧
          Y.toPageInfinity LY p q ≫ ξY.hom = Y.toGradedPiece AY p q ∧
          Φ.map ξX.hom ≫ (κ (p + q) p).hom = (φInfinity p q).hom ≫ ξY.hom) ∧
      (∀ (r : ℕ) (p q : ℤ),
        (r : ℤ) + 2 ≥ max (p + 3) (q - a + 2) →
        ∃ lambdaX : (AX (p + q)).obj ≅ X.D (p - r) (q + r),
        ∃ lambdaY : (AY (p + q)).obj ≅ Y.D (p - r) (q + r),
        ∃ tX : ((X.imageFiltration (p + q) (AX (p + q))).step p : C) ≅
          (X.pageCouple r).D (p - r) (q + r),
        ∃ tY : ((Y.imageFiltration (p + q) (AY (p + q))).step p : B) ≅
          (Y.pageCouple r).D (p - r) (q + r),
        ∃ ψX : (X.imageFiltration (p + q) (AX (p + q))).gradedPiece p ≅
          (X.pageCouple r).E p q,
        ∃ ψY : (Y.imageFiltration (p + q) (AY (p + q))).gradedPiece p ≅
          (Y.pageCouple r).E p q,
        lambdaX.inv = eqToHom (by congr 1; omega) ≫ (AX (p + q)).ι (p - r) ∧
        lambdaY.inv = eqToHom (by congr 1; omega) ≫ (AY (p + q)).ι (p - r) ∧
        tX.hom ≫ iX r (p - r) (q + r) =
          ((X.imageFiltration (p + q) (AX (p + q))).step p).arrow ≫ lambdaX.hom ∧
        tY.hom ≫ iY r (p - r) (q + r) =
          ((Y.imageFiltration (p + q) (AY (p + q))).step p).arrow ≫ lambdaY.hom ∧
        cokernel.π (Subobject.ofLE
          ((X.imageFiltration (p + q) (AX (p + q))).step (p + 1))
          ((X.imageFiltration (p + q) (AX (p + q))).step p)
          ((X.imageFiltration (p + q) (AX (p + q))).antitone_step (by omega))) ≫
          ψX.hom = tX.hom ≫ (X.pageCouple r).g (p - r) (q + r) ≫
            eqToHom (by congr 1 <;> omega) ∧
        cokernel.π (Subobject.ofLE
          ((Y.imageFiltration (p + q) (AY (p + q))).step (p + 1))
          ((Y.imageFiltration (p + q) (AY (p + q))).step p)
          ((Y.imageFiltration (p + q) (AY (p + q))).antitone_step (by omega))) ≫
          ψY.hom = tY.hom ≫ (Y.pageCouple r).g (p - r) (q + r) ≫
            eqToHom (by congr 1 <;> omega) ∧
        Φ.map ψX.hom ≫ (φ r p q).hom = (κ (p + q) p).hom ≫ ψY.hom) := by
  classical
  have hinfinity :
          (∃ φInfinity : ∀ p q : ℤ, Φ.obj (X.pageInfinity LX p q) ≅ Y.pageInfinity LY p q,
            (∀ p q : ℤ, Φ.map (X.toPageInfinity LX p q) ≫ (φInfinity p q).hom =
              eqToHom (hD p q) ≫ Y.toPageInfinity LY p q) ∧
            (∀ (r : ℕ) (p q : ℤ), (r : ℤ) + 2 > max (q - a + 1) p →
              ∃ hZX : X.cycleBoundaryTower.Z r p q = LX.Z p q,
              ∃ hZY : Y.cycleBoundaryTower.Z r p q = LY.Z p q,
              ∃ eX : (X.pageCouple r).E p q ≅ X.pageInfinity LX p q,
              ∃ eY : (Y.pageCouple r).E p q ≅ Y.pageInfinity LY p q,
              X.cycleBoundaryTower.projection r p q ≫ eX.hom =
                eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : C)) hZX) ≫
                  cokernel.π (Subobject.ofLE (LX.B p q) (LX.Z p q)
                    (limitBoundary_le_cycle X LX p q)) ∧
              Y.cycleBoundaryTower.projection r p q ≫ eY.hom =
                eqToHom (congrArg (fun S : Subobject (Y.E p q) ↦ (S : B)) hZY) ≫
                  cokernel.π (Subobject.ofLE (LY.B p q) (LY.Z p q)
                    (limitBoundary_le_cycle Y LY p q)) ∧
              Φ.map eX.hom ≫ (φInfinity p q).hom = (φ r p q).hom ≫ eY.hom) ∧
            ∀ p q : ℤ,
              ∃ ξX : X.pageInfinity LX p q ≅
                (X.imageFiltration (p + q) (AX (p + q))).gradedPiece p,
              ∃ ξY : Y.pageInfinity LY p q ≅
                (Y.imageFiltration (p + q) (AY (p + q))).gradedPiece p,
              X.toPageInfinity LX p q ≫ ξX.hom = X.toGradedPiece AX p q ∧
              Y.toPageInfinity LY p q ≫ ξY.hom = Y.toGradedPiece AY p q ∧
              Φ.map ξX.hom ≫ (κ (p + q) p).hom = (φInfinity p q).hom ≫ ξY.hom) := by
    classical
    have hgraded (p q : ℤ) :
        Φ.map (X.toGradedPiece AX p q) ≫ (κ (p + q) p).hom =
          eqToHom (hD p q) ≫ Y.toGradedPiece AY p q := by
      have hf : Φ.map (factorThruImageSubobject ((AX (p + q)).ι p)) ≫
          (τ (p + q) p).hom = eqToHom (hD p (p + q - p)) ≫
            factorThruImageSubobject ((AY (p + q)).ι p) := by
        apply (cancel_mono (imageSubobject ((AY (p + q)).ι p)).arrow).mp
        rw [Category.assoc]
        erw [hτ]
        rw [← Category.assoc, ← Φ.map_comp]
        erw [imageSubobject_arrow_comp]
        rw [hA, Category.assoc, imageSubobject_arrow_comp]
      dsimp only [toGradedPiece]
      simp only [Φ.map_comp, Category.assoc]
      rw [hκ, ← Category.assoc (Φ.map (factorThruImageSubobject _)) (τ _ _).hom _, hf]
      simp only [Category.assoc]
      rw [← Category.assoc (Φ.map (eqToHom _)) (eqToHom (hD p (p + q - p))) _,
        transport_square Φ (fun p q ↦ eqToHom (hD p q)) rfl (by omega), Category.assoc]
    have hx (p q : ℤ) := X.weakConvergence_comparison LX AX hconvX.2.1.1 p q
    have hy (p q : ℤ) := Y.weakConvergence_comparison LY AY hconvY.2.1.1 p q
    let ξX := fun p q ↦ (hx p q).choose
    let ξY := fun p q ↦ (hy p q).choose
    have hξX (p q : ℤ) : X.toPageInfinity LX p q ≫ (ξX p q).hom =
        X.toGradedPiece AX p q := (hx p q).choose_spec.1
    have hξY (p q : ℤ) : Y.toPageInfinity LY p q ≫ (ξY p q).hom =
        Y.toGradedPiece AY p q := (hy p q).choose_spec.1
    let φInfinity := fun p q ↦ Φ.mapIso (ξX p q) ≪≫ κ (p + q) p ≪≫ (ξY p q).symm
    have hInf (p q : ℤ) : Φ.map (X.toPageInfinity LX p q) ≫ (φInfinity p q).hom =
        eqToHom (hD p q) ≫ Y.toPageInfinity LY p q := by
      apply (cancel_mono (ξY p q).hom).mp
      simp only [φInfinity, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← Φ.map_comp_assoc, hξX, hgraded, hξY]
    refine ⟨φInfinity, hInf, ?_, ?_⟩
    · intro r p q hr
      obtain ⟨hZX, eX, heX⟩ := stable_iso X a hEX LX r p q hr
      obtain ⟨hZY, eY, heY⟩ := stable_iso Y a hEY LY r p q hr
      have hgX := finiteG_stable X LX r p q hZX eX heX
      have hgY := finiteG_stable Y LY r p q hZY eY heY
      have : Epi (X.toPageInfinity LX p q) := (hconvX.2.1.1 p q).1
      have hepi : Epi (finiteG X LX r p q) := by
        have hfac : X.toPageInfinity LX p q ≫ eX.inv = finiteG X LX r p q := by
          rw [← hgX, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        have h : Epi (X.toPageInfinity LX p q ≫ eX.inv) := inferInstance
        rwa [hfac] at h
      have := hepi
      refine ⟨hZX, hZY, eX, eY, heX, heY, ?_⟩
      apply (cancel_epi (Φ.map (finiteG X LX r p q))).mp
      rw [← Φ.map_comp_assoc, hgX, hInf,
        ← Category.assoc, finiteG_natural Φ X Y LX LY hD hE δ φ H0 H6 H8,
        Category.assoc, hgY]
    · intro p q
      refine ⟨ξX p q, ξY p q, hξX p q, hξY p q, ?_⟩
      simp [φInfinity]
  refine ⟨hinfinity, ?_⟩
  intro r p q hr
  obtain ⟨lambdaX, tX, ψX, hlX, htX, hψX⟩ := largePage_witness X a hDX
    (fun i j hi ↦ hEX i j (Or.inl hi)) iX (fun i j ↦ (H1 i j).1)
    (fun s i j ↦ (H2 s i j).1) AX hAX hAX0 r p q hr
  obtain ⟨lambdaY, tY, ψY, hlY, htY, hψY⟩ := largePage_witness Y a hDY
    (fun i j hi ↦ hEY i j (Or.inl hi)) iY (fun i j ↦ (H1 i j).2)
    (fun s i j ↦ (H2 s i j).2) AY hAY hAY0 r p q hr
  have hlInv : Φ.map lambdaX.inv ≫ (eA (p + q)).hom =
      eqToHom (hD (p - r) (q + r)) ≫ lambdaY.inv := by
    rw [hlX, hlY, Φ.map_comp, Category.assoc, hA,
      ← Category.assoc, transport_square Φ (fun i j ↦ eqToHom (hD i j)) rfl (by omega),
      Category.assoc]
  have hl : Φ.map lambdaX.hom ≫ eqToHom (hD (p - r) (q + r)) =
      (eA (p + q)).hom ≫ lambdaY.hom := by
    apply (cancel_epi (Φ.map lambdaX.inv)).mp
    rw [← Φ.map_comp_assoc, Iso.inv_hom_id, Φ.map_id, Category.id_comp,
      ← Category.assoc, hlInv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ht : Φ.map tX.hom ≫ (δ r (p - r) (q + r)).hom =
      (τ (p + q) p).hom ≫ tY.hom := by
    have := (H3 r (p - r) (q + r)).2.1
    apply (cancel_mono (iY r (p - r) (q + r))).mp
    rw [Category.assoc, (H3 r (p - r) (q + r)).2.2,
      ← Category.assoc, ← Φ.map_comp, htX, Φ.map_comp, Category.assoc, hl,
      ← Category.assoc, ← hτ]
    simp only [Category.assoc]
    rw [htY]
  refine ⟨lambdaX, lambdaY, tX, tY, ψX, ψY, hlX, hlY, htX, htY, hψX, hψY, ?_⟩
  apply (cancel_epi (Φ.map (cokernel.π (Subobject.ofLE
    ((X.imageFiltration (p + q) (AX (p + q))).step (p + 1))
    ((X.imageFiltration (p + q) (AX (p + q))).step p)
    ((X.imageFiltration (p + q) (AX (p + q))).antitone_step (by omega)))))).mp
  rw [← Φ.map_comp_assoc, hψX, Φ.map_comp, Φ.map_comp, Category.assoc, Category.assoc,
    transport_square Φ (fun i j ↦ (φ r i j).hom) (by omega) (by omega),
    ← Category.assoc (Φ.map ((X.pageCouple r).g _ _)), H6]
  simp only [Category.assoc]
  rw [← Category.assoc (Φ.map tX.hom) (δ r (p - r) (q + r)).hom _, ht]
  simp only [Category.assoc]
  rw [← hψY, ← Category.assoc, ← hκ, Category.assoc]
end CategoryTheory.BigradedExactCouple
