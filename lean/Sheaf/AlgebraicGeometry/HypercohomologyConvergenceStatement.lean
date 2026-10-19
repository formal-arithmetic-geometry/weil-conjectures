/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Iso
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
import all Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.AbutmentImageFiltration

/-!
# Half-plane convergence of the hypercohomology spectral sequences

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, order 1376;
Stacks Project, Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem couple_D
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (K : CochainComplex.Plus A) (p q : ℤ) :
    (hypercohomologyCouple F K).D p q = hypercohomologyD F K p q := by
  unfold hypercohomologyCouple
  rcases hypercohomology_maps_exact F K with ⟨_, _, _, _, _, _⟩
  rfl

private theorem couple_E
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (K : CochainComplex.Plus A) (p q : ℤ) :
    (hypercohomologyCouple F K).E p q = hypercohomologyE F K p q := by
  unfold hypercohomologyCouple
  rcases hypercohomology_maps_exact F K with ⟨_, _, _, _, _, _⟩
  rfl

private theorem couple_alpha
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (K : CochainComplex.Plus A) (p q : ℤ) :
    (hypercohomologyCouple F K).alpha p q =
      eqToHom (couple_D F K p q) ≫ hypercohomologyAlpha F K p q ≫
        eqToHom (couple_D F K (p - 1) (q + 1)).symm := by
  generalize_proofs
  unfold hypercohomologyCouple at *
  generalize hx : hypercohomology_maps_exact F K = h at *
  rcases h with ⟨_, _, _, _, _, _⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem canonical_abutment
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (K : CochainComplex.Plus A) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (hypercohomologyD F K p q))
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (hypercohomologyE F K p q))
    (hiso : ∀ n : ℤ, IsIso (hypercohomologyAbutmentMap F K n n)) :
    ∃ Z : (hypercohomologyCouple F K).LimitSubobjects,
      ∃ T : ∀ n : ℤ, (hypercohomologyCouple F K).AlphaColimit n,
      ∃ hT : ∀ n : ℤ, (T n).obj =
        (DerivedCategory.homologyFunctor B n).obj (F.obj (DerivedCategory.Q.obj K.obj)),
      ∃ hD' : ∀ n p : ℤ, (hypercohomologyCouple F K).D p (n - p) =
        (DerivedCategory.homologyFunctor B n).obj
          (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K (n - p)).obj)),
      (hypercohomologyCouple F K).ConvergesTo Z T ∧
      (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
        eqToHom (hD' n p) ≫ hypercohomologyAbutmentMap F K n (n - p)) ∧
      (∀ n : ℤ, ((hypercohomologyCouple F K).imageFiltration n (T n)).IsFinite) ∧
      (∀ n p : ℤ, (Subobject.«exists» (eqToHom (hT n))).obj
        (((hypercohomologyCouple F K).imageFiltration n (T n)).step p) =
          imageSubobject (hypercohomologyAbutmentMap F K n (n - p))) := by
  let X := hypercohomologyCouple F K
  let H (n : ℤ) := (DerivedCategory.homologyFunctor B n).obj
    (F.obj (DerivedCategory.Q.obj K.obj))
  let j (n q : ℤ) : X.D (n - q) q ⟶ H n :=
    eqToHom (by rw [couple_D]; unfold hypercohomologyD; congr 2; omega) ≫
      hypercohomologyAbutmentMap F K n q
  let c (n : ℤ) : X.D 0 n ⟶ H n :=
    eqToHom (by congr 1; omega) ≫ j n n
  have hco (n p : ℤ) : X.alphaDiagonal n p ≫
      eqToHom (by congr 1; omega) ≫ j n (n - p) =
        eqToHom (by congr 1; omega) ≫ j n (n - (p + 1)) := by
    have ha (p q n t : ℤ) (hn : p + q = n) (ht : q + 1 = t) :
        hypercohomologyAlpha F K p q =
          eqToHom (by unfold hypercohomologyD; rw [hn]; rfl) ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.map (DerivedCategory.Q.map
              (eqToHom (congrArg (fun r : ℤ ↦ K.obj.truncLE r)
                (by omega : q = t - 1)) ≫ TruncationCouple.transition K t))) ≫
          eqToHom (by unfold hypercohomologyD; rw [← ht, ← hn]; congr 2; omega) := by
      subst n
      subst t
      simp only [eqToHom_refl, Category.id_comp]
      rfl
    dsimp only [BigradedExactCouple.alphaDiagonal]
    dsimp only [X]
    rw [couple_alpha]
    simp only [Category.assoc]
    rw [ha (p + 1) (n - (p + 1)) n (n - p) (by omega) (by omega)]
    simp only [j, hypercohomologyAbutmentMap, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    have hq : n - (p + 1) = n - p - 1 := by omega
    simp only [Category.assoc, TruncationCouple.transition_comp_ιTruncLE]
    have hι := eqToHom_naturality (fun r : ℤ ↦ K.obj.ιTruncLE r) hq
    simp only [eqToHom_refl, Category.comp_id] at hι
    rw [hι]
  have hn : ∀ (n p : ℤ) (_ : 0 ≤ p), eqToHom (by congr 1 <;> omega) ≫ j n (n - p) =
      X.incomingAlphaIter p.toNat 0 n ≫ c n := by
    let k (n p : ℤ) : X.D p (n - p) ⟶ H n :=
      eqToHom (by congr 1; omega) ≫ j n (n - p)
    have hk (n p : ℤ) : X.alphaDiagonal n p ≫ k n p = k n (p + 1) := hco n p
    have hi (n : ℤ) (r : ℕ) (p q : ℤ) (hn : p + q = n) :
        X.alphaIter r p q ≫ eqToHom (by congr 1; omega) ≫ k n (p - r) =
          eqToHom (by congr 1; omega) ≫ k n p := by
      induction r generalizing p q with
      | zero =>
        simp only [BigradedExactCouple.alphaIter, eqToHom_trans_assoc]
        have he := eqToHom_naturality (k n) (by omega : p - (↑(0 : ℕ) : ℤ) = p)
        simp only [eqToHom_refl, Category.comp_id] at he
        rw [he, eqToHom_trans_assoc]
      | succ r ih =>
        simp only [BigradedExactCouple.alphaIter, Category.assoc, eqToHom_trans_assoc]
        have he := ih (p - 1) (q + 1) (by omega)
        have hidx : p - ↑(r + 1 : ℕ) = p - 1 - ↑r := by omega
        have hcast := eqToHom_naturality (k n) hidx
        simp only [eqToHom_refl, Category.comp_id] at hcast
        rw [hcast, eqToHom_trans_assoc, he]
        have hq : q = n - p := by omega
        subst q
        have he' := hk n (p - 1)
        simp only [BigradedExactCouple.alphaDiagonal, Category.assoc] at he'
        dsimp only [k] at he' ⊢
        simp only [eqToHom_trans_assoc] at he' ⊢
        convert! he' using 1 <;> congr! 4 <;> omega
    intro n p hp
    lift p to ℕ using hp
    have he := hi n p (p : ℤ) (n - p) (by omega)
    have hend := eqToHom_naturality (k n) (by omega : (p : ℤ) - p = 0)
    simp only [eqToHom_refl, Category.comp_id] at hend
    rw [hend, eqToHom_trans_assoc] at he
    simp only [k, eqToHom_trans_assoc] at he
    simp only [Int.toNat_natCast, BigradedExactCouple.incomingAlphaIter, c,
      Category.assoc, eqToHom_trans_assoc]
    convert! he.symm using 1 <;> congr! 4 <;> omega
  have hc (n : ℤ) : IsIso (c n) := by
    dsimp [c, j]
    infer_instance
  have hDX : ∀ p q : ℤ, q < a → IsZero (X.D p q) := by
    simpa only [X, couple_D] using hD
  have hEX : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q) := by
    simpa only [X, couple_E] using hE
  obtain ⟨Z, T₀, hT₀, hT₀ι, hsupport, _⟩ :=
    BigradedExactCouple.halfPlaneConvergence X a hDX hEX
  obtain ⟨FA, FH, hFA, hFA0, hFH, hj, htop, hbot, hfinite, hneg, T, hT, hι, hconv⟩ :=
    abutment_image_filtration X a hDX hEX Z H j c (fun _ ↦ rfl) hc hco hn
  let hD' (n p : ℤ) : X.D p (n - p) =
      (DerivedCategory.homologyFunctor B n).obj
        (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K (n - p)).obj)) := by
    rw [couple_D]
    unfold hypercohomologyD
    congr 2
    omega
  have hι' (n p : ℤ) : (T n).ι p ≫ eqToHom (hT n) =
      eqToHom (hD' n p) ≫ hypercohomologyAbutmentMap F K n (n - p) := by
    simpa only [j, Category.assoc, eqToHom_trans_assoc] using hι n p
  have himage (n p : ℤ) : (Subobject.«exists» (eqToHom (hT n))).obj
      ((X.imageFiltration n (T n)).step p) =
        imageSubobject (hypercohomologyAbutmentMap F K n (n - p)) := by
    rw [Subobject.exists_obj_eq_imageSubobject]
    change imageSubobject ((imageSubobject ((T n).ι p)).arrow ≫ eqToHom (hT n)) = _
    rw [← imageSubobject_comp_of_epi (factorThruImageSubobject ((T n).ι p)),
      ← Category.assoc, imageSubobject_arrow_comp, hι', imageSubobject_iso_comp]
  refine ⟨Z, T, hT, hD', hconv, hι', ?_, himage⟩
  intro n
  have hstep (p : ℤ) : (Subobject.map (eqToHom (hT n))).obj
      ((X.imageFiltration n (T n)).step p) = (FH n).step p := by
    rw [← Subobject.exists_iso_map, himage, hj]
    dsimp only [j]
    rw [imageSubobject_iso_comp]
  obtain ⟨l, r, hl, hr⟩ := (hfinite n).1
  refine ⟨l, r, ?_, ?_⟩
  · apply Subobject.map_obj_injective (eqToHom (hT n))
    rw [hstep, hl, Subobject.map_top, Subobject.mk_eq_top_of_isIso]
  · apply Subobject.map_obj_injective (eqToHom (hT n))
    rw [hstep, hr, Subobject.map_bot]

private theorem page_vanishing
    {B : Type v} [Category.{u'} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (r : ℕ) (p q : ℤ) (h : p < 0 ∨ q < a) :
    IsZero ((X.pageCouple r).E p q) := by
  induction r with
  | zero => exact hE p q h
  | succ r ih =>
    have : Epi ((X.pageCouple r).derivedEProjection p q) := by
      dsimp [BigradedExactCouple.derivedEProjection, BigradedExactCouple.derivedE]
      infer_instance
    exact IsZero.of_epi ((X.pageCouple r).derivedEProjection p q)
      (IsZero.of_mono (kernel.ι ((X.pageCouple r).d p q)) ih)

end CategoryTheory

namespace AlgebraicGeometry.Etale

open CategoryTheory

set_option linter.unusedVariables false in
/--
The two canonical truncation spectral sequences of a torsion bounded-below étale
complex are half-plane spectral sequences.  In each total degree their image
filtration is finite, exhaustive, separated, and convergent without a derived
inverse-limit condition.

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, order 1376;
Stacks Project, Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).

Proof: apply the right-derived negative-vanishing theorem to the truncation
couples for `f` and `f'` (and exactness of inverse image for the base-change
comparison), obtaining the bounds `p ≥ 0` and `q ≥ a`.  On a fixed diagonal
`p + q = n` these bounds give the finite interval `a ≤ q ≤ n`.  The finite
image filtrations from the truncation tower are therefore exhaustive and
separated, and the half-plane convergence theorem identifies their associated
graded pieces with the stabilized page; the quotient tower is eventually
constant, so no derived inverse-limit hypothesis is required.

Rendering: for each sequence the abutment `Hⁿ` is an `AlphaColimit` whose object is
the actual derived homology `Hⁿ(F K)` and whose cocone maps are the recorded
`hypercohomologyAbutmentMap`s.  Its image filtration [def-sp-filtration] is finite
(`IsFinite`: a whole step and a zero step, hence exhaustive and separated); transported
to `Hⁿ(F K)` its steps are `FᵖHⁿ = im(Hⁿ(F τ≤(n-p) K) → Hⁿ(F K))`, the defining steps
of `hypercohomologyFiltration` [def-weil-pbc-hypercohomology-filtrations]; and the
couple `ConvergesTo` it [def-sp-convergence].  The page index `r` is the page `E_(r+2)`.
-/
theorem hypercohomology_convergence_statement
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : ChosenCartesianSquare g' f' f g)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ) (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ (r : ℕ) (p q : ℤ), (p < 0 ∨ q < a) →
      IsZero (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n →
      ¬ IsZero (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple r).E p q) →
      a ≤ q ∧ q ≤ n) ∧
    (∀ (r : ℕ) (p q : ℤ), (p < 0 ∨ q < a) →
      IsZero (((hypercohomologyCouple
        (hypercohomologySecondFunctor f' g') K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n →
      ¬ IsZero (((hypercohomologyCouple
        (hypercohomologySecondFunctor f' g') K).pageCouple r).E p q) →
      a ≤ q ∧ q ≤ n) ∧
    (∃ Z₁ : (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).LimitSubobjects,
      ∃ A₁ : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).AlphaColimit n,
      ∃ hA₁ : ∀ n : ℤ, (A₁ n).obj =
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj)),
      ∃ hD₁ : ∀ n p : ℤ,
        (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).D p (n - p) =
          (DerivedCategory.homologyFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K (n - p)).obj)),
      (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).ConvergesTo Z₁ A₁ ∧
      (∀ n p : ℤ, (A₁ n).ι p ≫ eqToHom (hA₁ n) =
        eqToHom (hD₁ n p) ≫
          hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)) ∧
      (∀ n : ℤ,
        ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n
          (A₁ n)).IsFinite) ∧
      (∀ n p : ℤ,
        (Subobject.«exists» (eqToHom (hA₁ n))).obj
          (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n
            (A₁ n)).step p) =
          imageSubobject
            (hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)))) ∧
    (∃ Z₂ : (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).LimitSubobjects,
      ∃ A₂ : ∀ n : ℤ,
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).AlphaColimit n,
      ∃ hA₂ : ∀ n : ℤ, (A₂ n).obj =
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj)),
      ∃ hD₂ : ∀ n p : ℤ,
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).D p (n - p) =
          (DerivedCategory.homologyFunctor
            (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K (n - p)).obj)),
      (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).ConvergesTo Z₂ A₂ ∧
      (∀ n p : ℤ, (A₂ n).ι p ≫ eqToHom (hA₂ n) =
        eqToHom (hD₂ n p) ≫
          hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)) ∧
      (∀ n : ℤ,
        ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n
          (A₂ n)).IsFinite) ∧
      (∀ n p : ℤ,
        (Subobject.«exists» (eqToHom (hA₂ n))).obj
          (((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n
            (A₂ n)).step p) =
          imageSubobject
            (hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)))) := by
  have haK (q : ℤ) (hq : q < a) : IsZero (K.obj.homology q) :=
    (ha q hq).of_iso
      (((DerivedCategory.homologyFunctorFactors _ q).app K.obj).symm ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e)
  have hF₁ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologyFirstFunctor f).obj M).IsGE n :=
    rightDerived_preserves_isGE _ M n
  have hF₂ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologySecondFunctor f' g').obj M).IsGE n := by
    have := Functor.isGE_mapDerivedCategory_obj
      (upperStar AddCommGrpCat.{u + 1} g') M n
    exact rightDerived_preserves_isGE _ _ n
  obtain ⟨hD₁, hE₁, hi₁⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologyFirstFunctor f) K a haK hF₁
  obtain ⟨hD₂, hE₂, hi₂⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologySecondFunctor f' g') K a haK hF₂
  have hz₁ := page_vanishing (hypercohomologyCouple (hypercohomologyFirstFunctor f) K) a
    (by simpa only [couple_E] using hE₁)
  have hz₂ := page_vanishing (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K) a
    (by simpa only [couple_E] using hE₂)
  refine ⟨hz₁, ?_, hz₂, ?_,
    canonical_abutment (hypercohomologyFirstFunctor f) K a hD₁ hE₁ hi₁,
    canonical_abutment (hypercohomologySecondFunctor f' g') K a hD₂ hE₂ hi₂⟩
  all_goals
    intro r n p q hn hne
    have hq : a ≤ q := le_of_not_gt (fun h ↦ hne (by
      first
      | exact hz₁ r p q (Or.inr h)
      | exact hz₂ r p q (Or.inr h)))
    have hp : 0 ≤ p := le_of_not_gt (fun h ↦ hne (by
      first
      | exact hz₁ r p q (Or.inl h)
      | exact hz₂ r p q (Or.inl h)))
    exact ⟨hq, by omega⟩

end AlgebraicGeometry.Etale
