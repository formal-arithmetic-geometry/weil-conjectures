/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteFilteredTwistingAugmentationData
public import WeilConjectures.CategoryTheory.UniformFiniteFilteredLocalization
import WeilConjectures.Algebra.Homology.FiniteFilteredBoundedFlatReplacement
import WeilConjectures.Algebra.Homology.FiniteFilteredTwistingAugmentationExtension

/-! # Augmentations of finite twisting families

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, the successive
mapping-cylinder construction of filtered flat resolutions.
(blueprint: lem-trf-finite-filtered-augmented-twisting-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
attribute [local instance] hasSheafifyEssentiallySmallSite
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

private theorem augmentedTwistingFamily_base
    (a : ℤ)
    (M : FilteredObject (CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ))
    (hM : CochainComplex.minus _ M.obj) (hbottom : M.filtration.F (a + 1) = ⊥) :
    ∃ (D : FiniteTwistingFamily R a a) (A : FiniteFilteredTwistingAugmentation D M),
      (∀ (p : ↥(Finset.Icc a a)) (n : ℤ),
        SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n)) ∧
      (∀ p : ↥(Finset.Icc a a), QuasiIso (A.grade p)) := by
  classical
  let B := ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  obtain ⟨N, hN⟩ := hM
  have := hN
  have hb (n : ℤ) (hn : N < n) :
      IsZero ((M.filtration.F a : CochainComplex B ℤ).X n) :=
    IsZero.of_mono ((M.filtration.F a).arrow.f n)
      (M.obj.isZero_of_isStrictlyLE N n hn)
  obtain ⟨P, f, hP, hPB, hf⟩ := exists_finiteFiltered_boundedFlatReplacement R
    (M.filtration.F a : CochainComplex B ℤ) N hb
  have hp (p : ↥(Finset.Icc a a)) : p.val = a := by
    have := p.property
    simp only [Finset.mem_Icc] at this
    omega
  have hlt (p q : ↥(Finset.Icc a a)) (h : p.val < q.val) : False := by
    rw [hp p, hp q] at h
    omega
  let D : FiniteTwistingFamily R a a :=
    { G := fun _ ↦ P
      bounded := fun _ ↦ ⟨N, hPB⟩
      τ := fun p q h ↦ (hlt p q h).elim
      maurerCartan := fun p q h ↦ (hlt p q h).elim }
  let g (p : ↥(Finset.Icc a a)) : P ⟶
      (M.filtration.F p.val : CochainComplex B ℤ) := f ≫
    eqToHom (congrArg (fun r ↦ (M.filtration.F r : CochainComplex B ℤ)) (hp p).symm)
  let A : FiniteFilteredTwistingAugmentation D M :=
    { component := fun p n ↦ (g p).f n
      comm := fun p n ↦ by
        let : IsEmpty {q : ↥(Finset.Icc a a) // p.val < q.val} :=
          ⟨fun q ↦ hlt p q.val q.property⟩
        simp [D]
      grade := fun p ↦ g p ≫ M.filtration.complexQuotientπ p.val (p.val + 1) (by omega)
      grade_f := fun _ _ ↦ rfl }
  refine ⟨D, A, fun _ n ↦ hP n, ?_⟩
  intro p
  change QuasiIso (g p ≫ M.filtration.complexQuotientπ p.val (p.val + 1) (by omega))
  have : QuasiIso f := hf
  have : QuasiIso (g p) := by dsimp [g]; infer_instance
  let i := Subobject.ofLE (M.filtration.F (p.val + 1)) (M.filtration.F p.val)
    (M.filtration.F_succ_le p.val)
  have hbot : M.filtration.F (p.val + 1) = ⊥ := by
    rw [hp]
    exact hbottom
  have hz : IsZero (M.filtration.F (p.val + 1) : CochainComplex B ℤ) := by
    rw [hbot]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  have hi : i = 0 := hz.eq_of_src _ _
  have : IsIso (M.filtration.complexQuotientπ p.val (p.val + 1) (by omega)) := by
    change IsIso (cokernel.π i)
    rw [hi]
    infer_instance
  infer_instance

/-- Resolving successive cones produces a flat twisting family with graded quasi-isomorphic
augmentation components, without yet forming its total filtered complex.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, successive resolutions
on graded pieces by mapping cylinders; step 1 of lem-trf-finite-filtered-flat-model.
Proof: descend from the empty tail at b+1. At p form Cone(P_(p+1) -> F^p M). The previously
constructed augmentation is a quasi-isomorphism on its finitely many grades, so the cone maps
quasi-isomorphically to gr^p M. Apply the bounded flat replacement theorem to this cone. Its
components g and h obey d h + h d = 0 and d g - g d = -u h. Take the negatives of the components
of h as the new strictly increasing twisting entries. Projecting the first identity onto every
old summand gives the Maurer--Cartan equations; the second gives the displayed augmentation
identity. The cone replacement followed by the quotient is the new grade map, hence a
quasi-isomorphism; all old grades and their maps remain unchanged. Finite direct sums have a
common upper bound. This construction includes the empty tails and the one-weight interval.
(blueprint: lem-trf-finite-filtered-augmented-twisting-family). -/
theorem exists_finiteFiltered_augmentedTwistingFamily
    (a b : ℤ) (hab : a ≤ b)
    (M : UniformFilteredComplexes (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (some (a, b))
      (CochainComplex.minus (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)))) :
    ∃ (D : FiniteTwistingFamily R a b) (A : FiniteFilteredTwistingAugmentation D M.obj),
      (∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
        SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n)) ∧
      (∀ p : ↥(Finset.Icc a b), QuasiIso (A.grade p)) := by
  classical
  let Goal (c : ℤ) : Prop :=
    ∃ (D : FiniteTwistingFamily R c b) (A : FiniteFilteredTwistingAugmentation D M.obj),
      (∀ (p : ↥(Finset.Icc c b)) (n : ℤ),
        SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n)) ∧
      (∀ p : ↥(Finset.Icc c b), QuasiIso (A.grade p))
  have hi : ∀ (n : ℕ) (c : ℤ), (b - c).toNat = n → c ≤ b → Goal c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcn hcb
      by_cases hc : c = b
      · subst c
        exact augmentedTwistingFamily_base b M.obj M.property.2.2
          (M.property.2.1 a b rfl).2
      · have hlt : c < b := by omega
        have hn : (b - (c + 1)).toNat < n := by omega
        obtain ⟨D, A, hflat, hgrade⟩ := ih _ hn (c + 1) rfl (by omega)
        exact exists_finiteFiltered_twistingAugmentationExtension c b hlt M.obj
          M.property.2.2 (M.property.2.1 a b rfl).2 D A hflat hgrade
  exact hi _ a rfl hab

end CochainComplex
