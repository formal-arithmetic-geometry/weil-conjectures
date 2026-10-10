/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Morphisms to an injective and from a projective object in degree `n`

Let `C` be an abelian category and `n : ℤ`. For an injective object `I` of `C` and any object
`X` of the derived category, the functor `H^n` induces a bijection
`Hom(X, I[-n]) ≃ Hom(H^n X, H^n(I[-n])) = Hom(H^n X, I)`; dually, for a projective object `P`,
`Hom(P[-n], X) ≃ Hom(P, H^n X)`. Here `I[-n]` is `(singleFunctor C n).obj I`, the object `I`
placed in degree `n`.

## Main statements

- `DerivedCategory.homologyFunctor_map_bijective_of_injective`: `H^n` is bijective on
  `Hom(X, (singleFunctor C n).obj I)` for `I` injective.
- `DerivedCategory.homologyFunctor_map_bijective_of_projective`: `H^n` is bijective on
  `Hom((singleFunctor C n).obj P, X)` for `P` projective.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If a functor `F` is bijective on the morphisms `X' ⟶ Y'`, it is bijective on the
morphisms `X ⟶ Y` for objects `X ≅ X'` and `Y ≅ Y'`. -/
lemma _root_.CategoryTheory.Functor.map_bijective_of_iso {D : Type*} [Category* D]
    {E : Type*} [Category* E] (F : D ⥤ E) {X X' Y Y' : D} (e : X ≅ X') (e' : Y ≅ Y')
    (h : Function.Bijective (fun f : X' ⟶ Y' ↦ F.map f)) :
    Function.Bijective (fun f : X ⟶ Y ↦ F.map f) := by
  have hc : (fun f : X ⟶ Y ↦ F.map f) =
      (fun g ↦ F.map e.hom ≫ g ≫ F.map e'.inv) ∘ (fun f : X' ⟶ Y' ↦ F.map f) ∘
        (fun f ↦ e.inv ≫ f ≫ e'.hom) := by
    funext f
    simp [← Functor.map_comp]
  rw [hc]
  refine Function.Bijective.comp ?_ (h.comp ?_)
  · convert ((F.mapIso e).homCongr (F.mapIso e')).symm.bijective using 1
    funext g
    simp [Iso.homCongr]
  · exact (e.homCongr e').bijective

/-- If `Q.map` is surjective on `K ⟶ L`, and every morphism of complexes `K ⟶ L` is determined
by its effect on `H^n` (in the sense that `H^n(φ) = 0` implies `Q(φ) = 0`) and every morphism
`H^n K ⟶ H^n L` is `H^n` of a morphism of complexes, then `H^n` is bijective on
`Q(K) ⟶ Q(L)`. -/
lemma homologyFunctor_map_bijective_Q_obj {K L : CochainComplex C ℤ} (n : ℤ)
    (hQ : ∀ g : Q.obj K ⟶ Q.obj L, ∃ φ : K ⟶ L, Q.map φ = g)
    (hinj : ∀ φ : K ⟶ L, HomologicalComplex.homologyMap φ n = 0 → Q.map φ = 0)
    (hsurj : ∀ ψ : K.homology n ⟶ L.homology n,
      ∃ φ : K ⟶ L, HomologicalComplex.homologyMap φ n = ψ) :
    Function.Bijective (fun f : Q.obj K ⟶ Q.obj L ↦ (homologyFunctor C n).map f) := by
  have key (φ : K ⟶ L) : (homologyFunctor C n).map (Q.map φ) =
      (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap φ n ≫
        (homologyFunctorFactors C n).inv.app L := by
    rw [← Category.assoc, ← homologyFunctorFactors_hom_naturality, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  refine ⟨fun f₁ f₂ h ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := hQ (f₁ - f₂)
    have h0 : HomologicalComplex.homologyMap φ n = 0 := by
      have := key φ
      rw [hφ, Functor.map_sub, sub_eq_zero.2 h] at this
      simpa using this.symm
    rw [← sub_eq_zero, ← hφ, hinj φ h0]
  · obtain ⟨φ, hφ⟩ := hsurj ((homologyFunctorFactors C n).inv.app K ≫ ψ ≫
      (homologyFunctorFactors C n).hom.app L)
    exact ⟨Q.map φ, by simp [key, hφ]⟩

section Injective

variable {K : CochainComplex C ℤ} {I : C} [Injective I] (n : ℤ)

/-- A morphism of complexes `φ : K ⟶ I[-n]` to an injective object placed in degree `n` which
vanishes on `H^n` is null-homotopic, so that `Q(φ) = 0`. -/
lemma Q_map_eq_zero_of_homologyMap_eq_zero_of_injective
    (φ : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I)
    (hφ : HomologicalComplex.homologyMap φ n = 0) : Q.map φ = 0 := by
  let f : K.X n ⟶ I := φ.f n ≫ (HomologicalComplex.singleObjXSelf _ n I).hom
  -- `f` vanishes on the cycles
  have hc : K.iCycles n ≫ f = 0 := by
    have h1 : HomologicalComplex.cyclesMap φ n = 0 := by
      have := HomologicalComplex.homologyπ_naturality φ n
      rw [hφ, Limits.comp_zero] at this
      rw [← cancel_mono (HomologicalComplex.singleObjCyclesSelfIso _ n I).hom,
        ← HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom, ← Category.assoc,
        ← this]
      simp
    simp only [f, ← Category.assoc, ← HomologicalComplex.cyclesMap_i, h1, Limits.zero_comp]
  have hS : (ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (by simp)).Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    exact K.cyclesIsKernel n (n + 1) (by simp)
  let h : K.X (n + 1) ⟶ I := hS.descToInjective f hc
  have hh : K.d n (n + 1) ≫ h = f := hS.comp_descToInjective f hc
  have hom : Homotopy φ 0 := (CochainComplex.HomComplex.Cochain.equivHomotopy φ 0).symm
    ⟨CochainComplex.HomComplex.Cochain.toSingleMk h (show n + 1 + (-1) = n by lia), by
      rw [CochainComplex.HomComplex.Cochain.δ_toSingleMk _ _ 0 n (by lia)]
      ext p
      by_cases hp : p = n
      · subst hp
        simp [CochainComplex.HomComplex.Cochain.toSingleMk_v, hh, f]
      · exact IsZero.eq_of_tgt (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp) _ _⟩
  rw [Q_map_eq_of_homotopy (h := hom), Functor.map_zero]

omit [HasDerivedCategory C] in
/-- Every morphism `H^n K ⟶ H^n(I[-n])` to the cohomology of an injective object placed in
degree `n` is `H^n` of a morphism of complexes `K ⟶ I[-n]`. -/
lemma exists_homologyMap_eq_of_injective
    (ψ : K.homology n ⟶ ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I).homology n) :
    ∃ φ : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I,
      HomologicalComplex.homologyMap φ n = ψ := by
  let ψ' : K.homology n ⟶ I := ψ ≫ (HomologicalComplex.singleObjHomologySelfIso _ n I).hom
  let ψ'' : K.opcycles n ⟶ I := Injective.factorThru ψ' (K.homologyι n)
  let f : K.X n ⟶ I := K.pOpcycles n ≫ ψ''
  have hf : ∀ i, (ComplexShape.up ℤ).Rel i n → K.d i n ≫ f = 0 := by
    intro i _
    simp [f]
  refine ⟨HomologicalComplex.mkHomToSingle f hf, ?_⟩
  rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso _ n I).hom,
    ← cancel_epi (K.homologyπ n)]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.mkHomToSingle_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, f, ψ'']
  rw [← HomologicalComplex.homology_π_ι_assoc, Injective.comp_factorThru]

/-- For an injective object `I` and any object `X` of the derived category, `H^n` is bijective
on the morphisms `X ⟶ I[-n]` to `I` placed in degree `n`:
`Hom(X, I[-n]) ≃ Hom(H^n X, H^n(I[-n]))`, and `H^n(I[-n]) = I`. -/
lemma homologyFunctor_map_bijective_of_injective (X : DerivedCategory C) :
    Function.Bijective (fun f : X ⟶ (singleFunctor C n).obj I ↦ (homologyFunctor C n).map f) := by
  have : CochainComplex.IsStrictlyGE
      ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I) n :=
    inferInstance
  have : ∀ p, Injective (((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I).X p) := by
    intro p
    by_cases hp : p = n
    · subst hp
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf _ p I).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).injective
  have := CochainComplex.isKInjective_of_injective
    ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I) n
  refine (homologyFunctor C n).map_bijective_of_iso (Q.objObjPreimageIso X).symm (Iso.refl _)
    (homologyFunctor_map_bijective_Q_obj (K := Q.objPreimage X)
      (L := (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I) n ?_
      (Q_map_eq_zero_of_homologyMap_eq_zero_of_injective n)
      (exists_homologyMap_eq_of_injective n))
  intro g
  obtain ⟨g', hg'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj (Q.objPreimage X))
    ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I)).2
      ((quotientCompQhIso C).hom.app _ ≫ g ≫ (quotientCompQhIso C).inv.app _)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g'
  refine ⟨φ, ?_⟩
  have h := (quotientCompQhIso C).hom.naturality φ
  dsimp at h hg'
  rw [← cancel_epi ((quotientCompQhIso C).hom.app _), ← h, hg']
  simp

end Injective

section Projective

variable {K : CochainComplex C ℤ} {P : C} [Projective P] (n : ℤ)

/-- A morphism of complexes `φ : P[-n] ⟶ K` from a projective object placed in degree `n` which
vanishes on `H^n` is null-homotopic, so that `Q(φ) = 0`. -/
lemma Q_map_eq_zero_of_homologyMap_eq_zero_of_projective
    (φ : (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P ⟶ K)
    (hφ : HomologicalComplex.homologyMap φ n = 0) : Q.map φ = 0 := by
  let f : P ⟶ K.X n := (HomologicalComplex.singleObjXSelf _ n P).inv ≫ φ.f n
  have hc : f ≫ K.pOpcycles n = 0 := by
    have h1 : HomologicalComplex.opcyclesMap φ n = 0 := by
      have := HomologicalComplex.homologyι_naturality φ n
      rw [hφ, Limits.zero_comp] at this
      rw [← cancel_epi (HomologicalComplex.singleObjOpcyclesSelfIso _ n P).hom,
        ← HomologicalComplex.singleObjHomologySelfIso_inv_homologyι,
        Category.assoc, ← this]
      simp
    simp only [f, Category.assoc, ← HomologicalComplex.p_opcyclesMap, h1, Limits.comp_zero]
  have hS : (ShortComplex.mk (K.d (n - 1) n) (K.pOpcycles n) (by simp)).Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    exact K.opcyclesIsCokernel (n - 1) n (by simp)
  let h : P ⟶ K.X (n - 1) := hS.liftFromProjective f hc
  have hh : h ≫ K.d (n - 1) n = f := hS.liftFromProjective_comp f hc
  have hom : Homotopy φ 0 := (CochainComplex.HomComplex.Cochain.equivHomotopy φ 0).symm
    ⟨CochainComplex.HomComplex.Cochain.fromSingleMk h (show n + (-1) = n - 1 by lia), by
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk _ _ 0 n (by lia)]
      ext p
      by_cases hp : p = n
      · subst hp
        simp [CochainComplex.HomComplex.Cochain.fromSingleMk_v, hh, f]
      · exact IsZero.eq_of_src (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp) _ _⟩
  rw [Q_map_eq_of_homotopy (h := hom), Functor.map_zero]

omit [HasDerivedCategory C] in
/-- Every morphism `H^n(P[-n]) ⟶ H^n K` from the cohomology of a projective object placed in
degree `n` is `H^n` of a morphism of complexes `P[-n] ⟶ K`. -/
lemma exists_homologyMap_eq_of_projective
    (ψ : ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P).homology n ⟶ K.homology n) :
    ∃ φ : (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P ⟶ K,
      HomologicalComplex.homologyMap φ n = ψ := by
  let ψ' : P ⟶ K.homology n := (HomologicalComplex.singleObjHomologySelfIso _ n P).inv ≫ ψ
  let ψ'' : P ⟶ K.cycles n := Projective.factorThru ψ' (K.homologyπ n)
  let f : P ⟶ K.X n := ψ'' ≫ K.iCycles n
  have hf : ∀ k, (ComplexShape.up ℤ).Rel n k → f ≫ K.d n k = 0 := by
    intro k _
    simp [f]
  refine ⟨HomologicalComplex.mkHomFromSingle f hf, ?_⟩
  rw [← cancel_epi (HomologicalComplex.singleObjHomologySelfIso _ n P).inv,
    ← cancel_mono (K.homologyι n)]
  rw [Category.assoc, HomologicalComplex.homologyι_naturality,
    HomologicalComplex.singleObjHomologySelfIso_inv_homologyι_assoc,
    HomologicalComplex.singleObjOpcyclesSelfIso_hom, Category.assoc,
    HomologicalComplex.p_opcyclesMap, HomologicalComplex.mkHomFromSingle_f]
  simp only [Iso.inv_hom_id_assoc, f, ψ'', Category.assoc]
  rw [← HomologicalComplex.homology_π_ι, Projective.factorThru_comp_assoc, Category.assoc]

/-- For a projective object `P` and any object `X` of the derived category, `H^n` is bijective
on the morphisms `P[-n] ⟶ X` from `P` placed in degree `n`:
`Hom(P[-n], X) ≃ Hom(H^n(P[-n]), H^n X)`, and `H^n(P[-n]) = P`. -/
lemma homologyFunctor_map_bijective_of_projective (X : DerivedCategory C) :
    Function.Bijective (fun f : (singleFunctor C n).obj P ⟶ X ↦ (homologyFunctor C n).map f) := by
  have : CochainComplex.IsStrictlyLE
      ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P) n :=
    inferInstance
  have : ∀ p, Projective (((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P).X p) := by
    intro p
    by_cases hp : p = n
    · subst hp
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf _ p P).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).projective
  have := CochainComplex.isKProjective_of_projective
    ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P) n
  exact (homologyFunctor C n).map_bijective_of_iso (Iso.refl _) (Q.objObjPreimageIso X).symm
    (homologyFunctor_map_bijective_Q_obj
      (K := (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P)
      (L := Q.objPreimage X) n
      (CochainComplex.IsKProjective.exists_Q_map_eq _ _)
      (Q_map_eq_zero_of_homologyMap_eq_zero_of_projective n)
      (exists_homologyMap_eq_of_projective n))

end Projective

end DerivedCategory
