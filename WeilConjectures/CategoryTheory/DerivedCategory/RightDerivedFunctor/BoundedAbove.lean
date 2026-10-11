/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Right derived functors of bounded above complexes

Let `F : C ⥤ D` be an additive functor out of a Grothendieck abelian category, and let
`RF : D(C) ⥤ D(D)` be its right derived functor on the unbounded derived categories. If `K` is
concentrated in degrees `≤ a`, then in every degree `n > a` the cohomology of `RF(K)` is that
of `RF(M[-a])` for a single object `M` of `C`
(`CategoryTheory.Functor.exists_nonempty_homology_rightDerivedFunctor_obj_iso`). Consequently, if
`F` has cohomological dimension `≤ N`, in the sense that `RF(M[0])` is concentrated in degrees
`≤ N` for every object `M`, then `RF` sends `D^{≤ a}` into `D^{≤ a + N}`
(`CategoryTheory.Functor.isLE_rightDerivedFunctor_obj`). This is the way-out argument for
unbounded below complexes; it needs no convergence of Postnikov towers.

The proof represents `K` by a K-injective complex `I` with injective components, which is
acyclic in degrees `> a`. Its stupid truncation `σ^{≥ a} I` is a bounded below complex of
injectives, hence K-injective, and it is acyclic outside degree `a`, so that it represents
`M[-a]` with `M = Z^a(I)`. The complexes `F(I)` and `F(σ^{≥ a} I)` agree in degrees `≥ a`, so
they have the same cohomology in degrees `> a`.

## Main statements

- `CochainComplex.restrictionExtendHomologyIso`: the stupid truncation `σ^{≥ a} K` has the same
  homology as `K` in degrees `> a`.
- `CategoryTheory.Functor.exists_nonempty_homology_rightDerivedFunctor_obj_iso`
- `CategoryTheory.Functor.isLE_rightDerivedFunctor_obj`
-/

@[expose] public section

universe w

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- The stupid truncation `σ^{≥ a} K = (K.restriction e).extend e`, for the embedding
`e = ComplexShape.embeddingUpIntGE a`, has the same homology as `K` in every degree `n > a`. -/
noncomputable def restrictionExtendHomologyIso (K : CochainComplex C ℤ) (a : ℤ) (k : ℕ) (n : ℤ)
    (hn : a + k + 1 = n) :
    ((K.restriction (ComplexShape.embeddingUpIntGE a)).extend
      (ComplexShape.embeddingUpIntGE a)).homology n ≅ K.homology n :=
  (K.restriction _).extendHomologyIso _ (j := k + 1)
      (show a + ((k + 1 : ℕ) : ℤ) = n by push_cast; lia) ≪≫
    K.restrictionHomologyIso (ComplexShape.embeddingUpIntGE a) k (k + 1) (k + 2)
      ((ComplexShape.up ℕ).prev_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl) rfl
      (show a + ((k + 1 : ℕ) : ℤ) = n by push_cast; lia) rfl
      ((ComplexShape.up ℤ).prev_eq' (show a + (k : ℤ) + 1 = n by lia))
      ((ComplexShape.up ℤ).next_eq' (show n + 1 = a + ((k + 2 : ℕ) : ℤ) by push_cast; lia))

end CochainComplex

namespace CategoryTheory.Functor

open DerivedCategory

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

/-- **Right derived functors of bounded above complexes.** If `K ∈ D(C)` is concentrated in
degrees `≤ a`, there is an object `M` of `C` such that in every degree `n > a` the cohomology of
`RF(K)` is that of `RF(M[-a])`. -/
theorem exists_nonempty_homology_rightDerivedFunctor_obj_iso (K : DerivedCategory C) (a : ℤ)
    [K.IsLE a] :
    ∃ M : C, ∀ n : ℤ, a < n →
      Nonempty ((homologyFunctor D n).obj (F.rightDerivedFunctor.obj K) ≅
        (homologyFunctor D n).obj (F.rightDerivedFunctor.obj ((singleFunctor C a).obj M))) := by
  -- a K-injective complex with injective components representing `K`
  let K₀ := Q.objPreimage K
  let I := (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K₀
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{w} C).app K₀) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C K₀).2
  let eI : K ≅ Q.obj I := (Q.objObjPreimageIso K).symm ≪≫
    asIso (Q.map ((CochainComplex.toKInjectiveResolution.{w} C).app K₀))
  have : I.IsLE a := by
    rw [← isLE_Q_obj_iff]
    exact TStructure.t.isLE_of_iso eI a
  -- its stupid truncation `σ^{≥ a} I`
  let e := ComplexShape.embeddingUpIntGE a
  let L := (I.restriction e).extend e
  have hL (n : ℤ) : Injective (L.X n) := by
    by_cases h : ∃ i, e.f i = n
    · obtain ⟨i, hi⟩ := h
      have : Injective (I.X (e.f i)) :=
        CochainComplex.injective_kInjectiveResolutionFunctor_obj_X.{w} K₀ _
      exact Injective.of_iso ((I.restriction e).extendXIso e hi).symm this
    · exact Injective.of_iso
        ((I.restriction e).isZero_extend_X e n (by simpa using h)).isoZero.symm inferInstance
  have : CochainComplex.IsStrictlyGE L a := inferInstanceAs (L.IsStrictlySupported e)
  have : CochainComplex.IsKInjective L := CochainComplex.isKInjective_of_injective L a
  have : CochainComplex.IsLE L a := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a + k + 1 = n := ⟨(n - a - 1).toNat, by lia⟩
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (I.isZero_of_isLE a n hn).of_iso (I.restrictionExtendHomologyIso a k n hk)
  -- `σ^{≥ a} I` is concentrated in degree `a`
  obtain ⟨M, ⟨eM⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj L) a
  refine ⟨M, fun n hn ↦ ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a + k + 1 = n := ⟨(n - a - 1).toNat, by lia⟩
  exact ⟨(homologyFunctor D n).mapIso
      (F.rightDerivedFunctor.mapIso eI ≪≫ F.rightDerivedFunctorObjQIso I) ≪≫
    (homologyFunctorFactors D n).app _ ≪≫
    (CochainComplex.restrictionExtendHomologyIso ((F.mapHomologicalComplex _).obj I) a k n
      hk).symm ≪≫
    HomologicalComplex.homologyMapIso
      (HomologicalComplex.mapHomologicalComplexObjExtendIso F (I.restriction e) e).symm n ≪≫
    ((homologyFunctorFactors D n).app _).symm ≪≫
    (homologyFunctor D n).mapIso
      ((F.rightDerivedFunctorObjQIso L).symm ≪≫ F.rightDerivedFunctor.mapIso eM)⟩

/-- **Way-out for bounded above complexes.** If `F` has cohomological dimension `≤ N`, i.e.
`RF(M[0])` is concentrated in degrees `≤ N` for every object `M`, then `RF` sends complexes
concentrated in degrees `≤ a` to complexes concentrated in degrees `≤ a + N`. -/
theorem isLE_rightDerivedFunctor_obj (N : ℕ)
    (hF : ∀ M : C, (F.rightDerivedFunctor.obj ((singleFunctor C 0).obj M)).IsLE N)
    (K : DerivedCategory C) (a : ℤ) [K.IsLE a] :
    (F.rightDerivedFunctor.obj K).IsLE (a + N) := by
  obtain ⟨M, hM⟩ := F.exists_nonempty_homology_rightDerivedFunctor_obj_iso K a
  have : (F.rightDerivedFunctor.obj ((singleFunctor C a).obj M)).IsLE (a + N) := by
    have := hF M
    have : TStructure.t.IsLE
        ((F.rightDerivedFunctor.obj ((singleFunctor C 0).obj M))⟦-a⟧) (a + N) :=
      TStructure.t.isLE_shift _ N (-a) (a + N) (by lia)
    exact TStructure.t.isLE_of_iso
      (show (F.rightDerivedFunctor.obj ((singleFunctor C 0).obj M))⟦-a⟧ ≅ _ from
        ((F.rightDerivedFunctor.commShiftIso (-a)).app _).symm ≪≫
        F.rightDerivedFunctor.mapIso (((singleFunctors C).shiftIso (-a) a 0 (by lia)).app M)) _
  rw [isLE_iff]
  intro n hn
  obtain ⟨φ⟩ := hM n (by lia)
  exact (isZero_of_isLE _ (a + N) n hn).of_iso φ

end CategoryTheory.Functor
