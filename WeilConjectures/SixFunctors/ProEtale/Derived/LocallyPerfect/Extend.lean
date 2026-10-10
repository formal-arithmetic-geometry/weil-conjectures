/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Glue
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Defs

/-!
# Extending a perfect top part by one degree

This is the inductive step of Stacks, Tag 0FPV, once the relevant subcomplex has been found.
Let `M` be a complex of pro-étale sheaves of `Λ`-modules containing the constant complex `c(E₀)`
of a bounded complex `E₀` of finite free modules vanishing below `m`, equal to `M` in degrees
`≥ m`. Let `ι : L' ⟶ M` be a subcomplex, equal to `M` in degrees `≥ m`, such that

* `Q(ι)` has a section `s : Q(M) ⟶ Q(L')` in the derived category;
* `H^m(ι)` is an isomorphism;
* the term `L'^{m-1}` is a quotient of a constant finite free sheaf `c(V₀)`, the composite
  `c(V₀) ⟶ L'^{m-1} ⟶ L'^m = c(E₀^m)` being induced by a linear map `A : V₀ ⟶ E₀^m`.

Then the constant complex `c(E₀')` of the mapping cone `E₀'` of `A : V₀[-m] ⟶ E₀` maps to `M`,
inducing isomorphisms in cohomology in degrees `≥ m` and an epimorphism in degree `m - 1`.
By the gluing lemma `CochainComplex.exists_iso_Q_obj_of_homologyMap`, `Q(M)` has a perfect top
part in degrees `≥ m - 1` (`AlgebraicGeometry.ProEtale.hasPerfectTop_sub_one`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
-- the mapping cone computations are slow
set_option maxHeartbeats 1000000 in
theorem hasPerfectTop_sub_one {Y : Scheme.{u}} [Nonempty Y] {m b : ℤ}
    (M L' : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ)
    (E₀ : CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
    (j : ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
      _).obj E₀ ⟶ M) (hj : ∀ i, Mono (j.f i)) (hj' : ∀ i, m ≤ i → IsIso (j.f i))
    [E₀.IsStrictlyGE m] [E₀.IsStrictlyLE b]
    (hfree : ∀ i, Module.Free Λ (E₀.X i) ∧ Module.Finite Λ (E₀.X i))
    (ι : L' ⟶ M) (hι : ∀ i, Mono (ι.f i)) (hι' : ∀ i, m ≤ i → IsIso (ι.f i))
    (s : DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj L')
    (hs : s ≫ DerivedCategory.Q.map ι = 𝟙 _) (hm : IsIso (HomologicalComplex.homologyMap ι m))
    (V₀ : ModuleCat.{u + 1} Λ) [Module.Free Λ V₀] [Module.Finite Λ V₀]
    (gen : (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj V₀ ⟶
      L'.X (m - 1)) [Epi gen]
    (A : V₀ ⟶ E₀.X m)
    (hA : gen ≫ L'.d (m - 1) m ≫ ι.f m =
      (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).map A ≫ j.f m) :
    HasPerfectTop (DerivedCategory.Q.obj M) (m - 1) := by
  let c := constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  let cC := c.mapHomologicalComplex (ComplexShape.up ℤ)
  have hzero (i : ℤ) (hi : i < m) : IsZero ((cC.obj E₀).X i) :=
    c.map_isZero (E₀.isZero_of_isStrictlyGE m i hi)
  -- `A` is a cycle: test after the faithful functor `c` and the monomorphism `j`
  have hA0 : A ≫ E₀.d m (m + 1) = 0 := by
    apply constantSheaf_map_injective (X := Y)
    rw [Functor.map_zero]
    have := hj (m + 1)
    apply (cancel_mono (j.f (m + 1) : c.obj (E₀.X (m + 1)) ⟶ M.X (m + 1))).1
    rw [zero_comp, Functor.map_comp, Category.assoc]
    have h₁ : c.map (E₀.d m (m + 1)) ≫ j.f (m + 1) = j.f m ≫ M.d m (m + 1) :=
      (j.comm m (m + 1)).symm
    have h₂ := ι.comm m (m + 1)
    rw [h₁, ← reassoc_of% hA, h₂, ← Category.assoc (L'.d (m - 1) m), L'.d_comp_d,
      zero_comp, comp_zero]
  let φ₀ : (HomologicalComplex.single (ModuleCat.{u + 1} Λ) (.up ℤ) m).obj V₀ ⟶ E₀ :=
    HomologicalComplex.mkHomFromSingle A (by
      rintro k hk
      obtain rfl : k = m + 1 := by simpa using hk.symm
      exact hA0)
  -- the lift `β : c(E₀) ⟶ L'` of `j` through `ι`
  let βf (i : ℤ) : (cC.obj E₀).X i ⟶ L'.X i :=
    if h : m ≤ i then (have := hι' i h; j.f i ≫ inv (ι.f i)) else 0
  have hβf (i : ℤ) : βf i ≫ ι.f i = j.f i := by
    by_cases h : m ≤ i
    · simp [βf, h]
    · exact (hzero i (by lia)).eq_of_src _ _
  let β : cC.obj E₀ ⟶ L' :=
    { f := βf
      comm' := by
        rintro i k rfl
        have := hι (i + 1)
        rw [← cancel_mono (ι.f (i + 1)), Category.assoc, ← ι.comm, reassoc_of% (hβf i),
          Category.assoc, hβf, j.comm] }
  have hβ : β ≫ ι = j := by ext i : 1; exact hβf i
  let S := cC.obj ((HomologicalComplex.single (ModuleCat.{u + 1} Λ) (.up ℤ) m).obj V₀)
  have hS (i : ℤ) (hi : i ≠ m) : IsZero (S.X i) :=
    c.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  let f₀ : S.X m ⟶ L'.X (m - 1) :=
    c.map (HomologicalComplex.singleObjXSelf (.up ℤ) m V₀).hom ≫ gen
  let α : CochainComplex.HomComplex.Cochain S L' (-1) :=
    CochainComplex.HomComplex.Cochain.single f₀ (-1)
  have eq : CochainComplex.HomComplex.δ (-1) 0 α =
      CochainComplex.HomComplex.Cochain.ofHom (cC.map φ₀ ≫ β) := by
    rw [CochainComplex.HomComplex.Cochain.δ_single f₀ (-1) 0 (by lia) (m - 1) m (by lia)
      (by lia)]
    have hSd : S.d (m - 1) m = 0 := (hS (m - 1) (by lia)).eq_of_src _ _
    rw [hSd, zero_comp, CochainComplex.HomComplex.Cochain.single_zero, smul_zero, add_zero]
    refine CochainComplex.HomComplex.Cochain.ext₀ _ _ fun p ↦ ?_
    rw [CochainComplex.HomComplex.Cochain.ofHom_v]
    by_cases hp : p = m
    · subst hp
      rw [CochainComplex.HomComplex.Cochain.single_v]
      have := hι p
      rw [← cancel_mono (ι.f p), Category.assoc, Category.assoc]
      change _ = _ ≫ βf p ≫ ι.f p
      rw [hβf]
      simp only [hA]
      (simp [cC, φ₀]; rfl)
    · rw [CochainComplex.HomComplex.Cochain.single_v_eq_zero _ _ _ _ _ hp]
      exact (hS p hp).eq_of_src _ _
  let φS : S ⟶ cC.obj E₀ := cC.map φ₀
  let δ' := CochainComplex.mappingCone.desc φS α β eq
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso φ₀ c
  let αP := e.hom ≫ δ' ≫ ι
  have hδiso (i : ℤ) (hi : m ≤ i) : IsIso (δ'.f i) := by
    have h₁ := CochainComplex.mappingCone.id_X φS i (i + 1) rfl
    rw [(hS (i + 1) (by lia)).eq_of_tgt ((CochainComplex.mappingCone.fst φS).1.v i (i + 1) rfl) 0,
      zero_comp, zero_add] at h₁
    have : IsIso ((CochainComplex.mappingCone.inr φS).f i) :=
      ⟨⟨_, CochainComplex.mappingCone.inr_f_snd_v φS i, h₁⟩⟩
    have : IsIso (j.f i) := hj' i hi
    have : IsIso (ι.f i) := hι' i hi
    have : IsIso (β.f i) := by
      have : IsIso (β.f i ≫ ι.f i) := by rw [hβf]; infer_instance
      exact IsIso.of_isIso_comp_right _ (ι.f i)
    have : IsIso ((CochainComplex.mappingCone.inr φS).f i ≫ δ'.f i) := by
      rw [CochainComplex.mappingCone.inr_f_desc_f]; infer_instance
    exact IsIso.of_isIso_comp_left ((CochainComplex.mappingCone.inr φS).f i) _
  have hδepi : Epi (δ'.f (m - 1)) := by
    rw [CochainComplex.mappingCone.desc_f φS α β eq (m - 1) m (by lia),
      (hzero (m - 1) (by lia)).eq_of_src (β.f (m - 1)) 0, comp_zero, add_zero]
    have h₁ := CochainComplex.mappingCone.inl_v_fst_v φS m (m - 1) (by lia)
    have : Epi ((CochainComplex.mappingCone.fst φS).1.v (m - 1) m (by lia)) :=
      epi_of_epi_fac h₁
    have : Epi (α.v m (m - 1) (by lia)) := by
      rw [CochainComplex.HomComplex.Cochain.single_v]
      infer_instance
    infer_instance
  have heiso (i : ℤ) : IsIso (e.hom.f i) :=
    inferInstanceAs (IsIso ((HomologicalComplex.eval _ _ i).mapIso e).hom)
  have hιiso (i : ℤ) (hi : m < i) : IsIso (HomologicalComplex.homologyMap ι i) :=
    HomologicalComplex.isIso_homologyMap_of_epi_of_isIso_of_mono ι (CochainComplex.prev ℤ i)
      (CochainComplex.next ℤ i) (have := hι' (i - 1) (by lia); inferInstance) (hι' i (by lia))
      (hι (i + 1))
  have hιepi : Epi (HomologicalComplex.homologyMap ι (m - 1)) := by
    rw [← CochainComplex.epi_homologyFunctor_map_Q_map_iff]
    have h := congrArg (DerivedCategory.homologyFunctor _ (m - 1)).map hs
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact epi_of_epi_fac h
  have hδ (i : ℤ) (hi : m ≤ i) : IsIso (HomologicalComplex.homologyMap δ' i) := by
    refine HomologicalComplex.isIso_homologyMap_of_epi_of_isIso_of_mono δ'
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i) ?_ (hδiso i hi) ?_
    · by_cases h : m ≤ i - 1
      · have := hδiso (i - 1) h
        infer_instance
      · obtain rfl : i = m := by lia
        exact hδepi
    · have := hδiso (i + 1) (by lia)
      infer_instance
  have hδ' : Epi (HomologicalComplex.homologyMap δ' (m - 1)) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_mono δ' (CochainComplex.next ℤ (m - 1)) hδepi
      (have := hδiso (m - 1 + 1) (by lia); inferInstance)
  obtain ⟨M', j', hj'₁, hj'₂, ⟨eM⟩⟩ := CochainComplex.exists_iso_Q_obj_of_homologyMap αP (m - 1)
    (fun i hi ↦ by
      rw [CochainComplex.isIso_homologyFunctor_map_Q_map_iff]
      simp only [αP, HomologicalComplex.homologyMap_comp]
      have := hδ i (by lia)
      have : IsIso (HomologicalComplex.homologyMap ι i) := by
        by_cases h : i = m
        · subst h; exact hm
        · exact hιiso i (by lia)
      infer_instance)
    (by
      rw [CochainComplex.epi_homologyFunctor_map_Q_map_iff]
      simp only [αP, HomologicalComplex.homologyMap_comp]
      infer_instance)
  refine ⟨M', CochainComplex.mappingCone φ₀, j', max b m, ⟨eM.symm⟩, hj'₁,
    fun i hi ↦ hj'₂ i hi, ?_, ?_, fun i ↦ ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      E₀.isZero_of_isStrictlyGE m i (by lia)⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      E₀.isZero_of_isStrictlyLE b i (by lia)⟩
  · have hS₀ : Module.Free Λ (((HomologicalComplex.single (ModuleCat.{u + 1} Λ) (.up ℤ) m).obj
        V₀).X (i + 1)) ∧ Module.Finite Λ (((HomologicalComplex.single (ModuleCat.{u + 1} Λ)
          (.up ℤ) m).obj V₀).X (i + 1)) := by
      by_cases h : i + 1 = m
      · let e₀ := (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) m V₀ (i + 1) h).toLinearEquiv
        exact ⟨Module.Free.of_equiv e₀.symm, Module.Finite.equiv e₀.symm⟩
      · have := ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) m V₀ (i + 1) h)
        exact ⟨inferInstance, inferInstance⟩
    obtain ⟨_, _⟩ := hS₀
    obtain ⟨_, _⟩ := hfree i
    let e₁ := (HomologicalComplex.homotopyCofiber.XIsoBiprod φ₀ i (i + 1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv
    exact ⟨Module.Free.of_equiv e₁.symm, Module.Finite.equiv e₁.symm⟩

end AlgebraicGeometry.ProEtale
