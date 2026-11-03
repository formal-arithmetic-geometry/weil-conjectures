/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData

/-! The tail-factorisation part of the finite twisting comparison. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

/--
The degreewise upper-triangular map factors through every finite-totalization tail.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (step 3 of the proof of lem-trf-finite-filtered-totalization-comparison).
Proof: on the tail of weight `≥ r`, put `L^n = (tailCoordinates r n).hom ≫
biproduct.map (f p).f n ≫ (tailCoordinates' r n).inv`. By `tailInclusion` of `M` and `M'`
and `hcoord`, `L^n` commutes with the two tail inclusions, summand by summand. The target
tail inclusion is degreewise split (`degreewiseSplit`), hence degreewise mono; composing
the two chain-map squares with it and cancelling gives the chain-map equation of `L`. Then
`φ` with these lifts is a `FilteredObject.Hom`, and the coordinate equation is `hcoord`.
(blueprint: lem-trf-finite-filtered-totalization-comparison-tail)
-/
theorem exists_finiteTwistingTotalization_comparison_hom
    (D D' : FiniteTwistingFamily R a b)
    (M : FiniteTwistingTotalization D) (M' : FiniteTwistingTotalization D')
    (f : ∀ p : ↥(Finset.Icc a b), D.G p ⟶ D'.G p)
    (φ : M.P ⟶ M'.P)
    (hcoord : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
      biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
          (M.coordinates n).inv ≫ φ.f n =
        (f p).f n ≫ biproduct.ι
          (fun q : ↥(Finset.Icc a b) ↦ (D'.G q).X n) p ≫
          (M'.coordinates n).inv) :
    ∃ ψ : FilteredObject.Hom ⟨M.P, M.F⟩ ⟨M'.P, M'.F⟩,
      ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
        biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
            (M.coordinates n).inv ≫ ψ.hom.f n =
          (f p).f n ≫ biproduct.ι
            (fun q : ↥(Finset.Icc a b) ↦ (D'.G q).X n) p ≫
            (M'.coordinates n).inv := by
  classical
  -- every tail inclusion is degreewise split, hence degreewise mono
  have hmono : ∀ r n : ℤ, Mono ((M'.F.step r).arrow.f n) := fun r n ↦ by
    obtain ⟨s, hs⟩ := M'.degreewiseSplit r n
    exact mono_of_mono_fac hs
  refine ⟨⟨φ, fun r ↦ ?_⟩, hcoord⟩
  -- the tail map in tail coordinates is the direct sum of the `f p` over `r ≤ p`
  let L : ∀ n : ℤ, ((M.F.step r : CochainComplex _ ℤ).X n) ⟶
      ((M'.F.step r : CochainComplex _ ℤ).X n) := fun n ↦
    (M.tailCoordinates r n).hom ≫
      biproduct.map (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (f p.val).f n) ≫
        (M'.tailCoordinates r n).inv
  have hL : ∀ n : ℤ, L n ≫ (M'.F.step r).arrow.f n = (M.F.step r).arrow.f n ≫ φ.f n := by
    intro n
    apply (cancel_epi (M.tailCoordinates r n).inv).1
    simp only [L, Category.assoc, Iso.inv_hom_id_assoc]
    rw [M'.tailInclusion r n, ← Category.assoc ((M.tailCoordinates r n).inv),
      M.tailInclusion r n]
    apply biproduct.hom_ext'
    intro p
    simp only [biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc,
      Category.assoc]
    exact (hcoord p.val n).symm
  have hcomm : ∀ n m : ℤ, L n ≫ (Subobject.underlying.obj (M'.F.step r)).d n m =
      (Subobject.underlying.obj (M.F.step r)).d n m ≫ L m := by
    intro n m
    have := hmono r m
    apply (cancel_mono ((M'.F.step r).arrow.f m)).1
    simp only [Category.assoc]
    calc L n ≫ (Subobject.underlying.obj (M'.F.step r)).d n m ≫ (M'.F.step r).arrow.f m
        = L n ≫ (M'.F.step r).arrow.f n ≫ M'.P.d n m := by
          rw [(M'.F.step r).arrow.comm]
      _ = (M.F.step r).arrow.f n ≫ φ.f n ≫ M'.P.d n m := by rw [reassoc_of% (hL n)]
      _ = (M.F.step r).arrow.f n ≫ M.P.d n m ≫ φ.f m := by rw [φ.comm]
      _ = (Subobject.underlying.obj (M.F.step r)).d n m ≫ (M.F.step r).arrow.f m ≫ φ.f m := by
          rw [reassoc_of% ((M.F.step r).arrow.comm n m)]
      _ = (Subobject.underlying.obj (M.F.step r)).d n m ≫ L m ≫ (M'.F.step r).arrow.f m := by
          rw [hL m]
  let lift : Subobject.underlying.obj (M.F.step r) ⟶ Subobject.underlying.obj (M'.F.step r) :=
    { f := L, comm' := fun n m _ ↦ hcomm n m }
  exact ⟨lift, HomologicalComplex.hom_ext _ _ hL⟩

end CochainComplex
