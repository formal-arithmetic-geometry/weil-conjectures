module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! # Lifting an augmented resolution through an extension cone

Source: blueprint, six-functors basics, direct-images proof, paragraph (3), internal bar
normalization; Stacks Project, Tags 014E, 0152 and 05RU
(blueprint: lem-sfb-augmented-resolution-extension-cone-lift).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

/-- An augmentation lift through a short exact sequence determines a unique kernel cocycle
and a compatible lift to its two-term cone. There is no projectivity hypothesis.

Source: blueprint, six-functors basics, direct-images proof, paragraph (3), internal bar
normalization; Stacks Project, Tags 014E, 0152 and 05RU
(blueprint: lem-sfb-augmented-resolution-extension-cone-lift).

Proof plan:
1. The augmentation chain equation gives d_P ≫ ell ≫ p = 0. Apply the kernel universal
   property `ShortComplex.ShortExact.fIsKernel` (lem-weil-pbc-abelian-short-exact-kernel)
   to obtain the unique f with f ≫ i = d_P ≫ ell.
2. The complex identity and monicity of i give d_P ≫ f = 0. Thus f, in degree -1,
   defines the map fbar to N[1].
3. In the cone convention of def-weil-abstract-derived-category, the cone has N in
   degree -1, E in degree zero, differential i, and triangle arrow minus projection.
   The components f and ell satisfy the two nontrivial chain equations, giving kappa.
4. The single-degree image of the given sequence is degreewise short exact, hence
   short exact by lem-weil-pbc-cochain-complexes-degreewise-exact. Apply
   lem-pc-cone-short-exact-quasi-iso (`mappingCone.quasiIso_descShortComplex`). Its
   map v has component p in degree zero. Its homology is therefore X in degree zero
   and zero elsewhere, by the cohomology of single-degree complexes.
5. Componentwise comparison gives kappa ≫ v = e and kappa ≫ pr = fbar. Apply Q;
   Q(v) is invertible, so Q(kappa) = Q(e) ≫ Q(v) inverse.
-/
theorem augmentedResolution_extension_cone_lift
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (P : CochainComplex C ℤ) (hP : ∀ r : ℤ, 0 < r → IsZero (P.X r))
    (e : P ⟶ (single C (ComplexShape.up ℤ) 0).obj S.X₃) [QuasiIso e]
    (ell : P.X 0 ⟶ S.X₂)
    (hell : ell ≫ S.g = e.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₃).hom) :
    ∃ f : P.X (-1) ⟶ S.X₁,
      (f ≫ S.f = P.d (-1) 0 ≫ ell) ∧
      (∀ f' : P.X (-1) ⟶ S.X₁, f' ≫ S.f = P.d (-1) 0 ≫ ell → f' = f) ∧
      P.d (-2) (-1) ≫ f = 0 ∧
      ∃ fbar : P ⟶ ((single C (ComplexShape.up ℤ) 0).obj S.X₁)⟦(1 : ℤ)⟧,
        (fbar.f (-1) ≫
          (CochainComplex.shiftFunctorObjXIso
            ((single C (ComplexShape.up ℤ) 0).obj S.X₁) 1 (-1) 0 (by decide)).hom ≫
          (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).hom = f) ∧
        (∀ r : ℤ, r ≠ -1 → fbar.f r = 0) ∧
        ∃ kappa : P ⟶ mappingCone ((single C (ComplexShape.up ℤ) 0).map S.f),
          (kappa.f (-1) ≫
            (mappingCone.fst ((single C (ComplexShape.up ℤ) 0).map S.f)).1.v
              (-1) 0 (by decide) ≫
            (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).hom = f) ∧
          (kappa.f 0 ≫
            (mappingCone.snd ((single C (ComplexShape.up ℤ) 0).map S.f)).v
              0 0 (by decide) ≫
            (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₂).hom = ell) ∧
          (∀ r : ℤ, r ≠ -1 → r ≠ 0 → kappa.f r = 0) ∧
          kappa ≫ mappingCone.descShortComplex (S.map (single C (ComplexShape.up ℤ) 0)) =
            e ∧
          kappa ≫ (-(mappingCone.triangle
            ((single C (ComplexShape.up ℤ) 0).map S.f)).mor₃) = fbar ∧
          QuasiIso (mappingCone.descShortComplex (S.map (single C (ComplexShape.up ℤ) 0))) ∧
          (∀ r : ℤ, r ≠ 0 →
            IsZero ((mappingCone ((single C (ComplexShape.up ℤ) 0).map S.f)).homology r)) ∧
          IsIso (homologyMap
            (mappingCone.descShortComplex (S.map (single C (ComplexShape.up ℤ) 0))) 0 ≫
            (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 S.X₃).hom) ∧
          ∃ vIso : DerivedCategory.Q.obj
              (mappingCone ((single C (ComplexShape.up ℤ) 0).map S.f)) ≅
              DerivedCategory.Q.obj ((single C (ComplexShape.up ℤ) 0).obj S.X₃),
            vIso.hom = DerivedCategory.Q.map
              (mappingCone.descShortComplex (S.map (single C (ComplexShape.up ℤ) 0))) ∧
            DerivedCategory.Q.map kappa = DerivedCategory.Q.map e ≫ vIso.inv := by
  classical
  let F := single C (ComplexShape.up ℤ) 0
  let i := F.map S.f
  let v := mappingCone.descShortComplex (S.map F)
  have : Mono S.f := hS.mono_f
  have hz : (P.d (-1) 0 ≫ ell) ≫ S.g = 0 := by
    rw [Category.assoc, hell, ← Category.assoc, ← e.comm]
    simp
  obtain ⟨f, hf⟩ := hS.exact.lift' (P.d (-1) 0 ≫ ell) hz
  have hf₂ : P.d (-2) (-1) ≫ f = 0 := by
    rw [← cancel_mono S.f, Category.assoc, hf, ← Category.assoc]
    simp
  let α : HomComplex.Cocycle P (F.obj S.X₁) 1 :=
    HomComplex.Cocycle.toSingleMk f (by decide) (-2) (by decide) hf₂
  let β : HomComplex.Cochain P (F.obj S.X₂) 0 :=
    HomComplex.Cochain.toSingleMk ell (by decide)
  have hab : HomComplex.δ 0 1 β +
      α.1.comp (HomComplex.Cochain.ofHom i) (add_zero 1) = 0 := by
    change HomComplex.δ 0 1 (HomComplex.Cochain.toSingleMk ell (by decide)) +
      (HomComplex.Cochain.toSingleMk f (by decide)).comp
        (HomComplex.Cochain.ofHom ((singleFunctor C 0).map S.f)) (add_zero 1) = 0
    rw [HomComplex.Cochain.δ_toSingleMk _ _ _ (-1) (by decide),
      ← HomComplex.Cochain.toSingleMk_postcomp, hf]
    simp
  let κ : P ⟶ mappingCone i := mappingCone.lift i α β hab
  have hkf : κ.f (-1) ≫ (mappingCone.fst i).1.v (-1) 0 (by decide) ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).hom = f := by
    simp [κ, α]
  have hkl : κ.f 0 ≫ (mappingCone.snd i).v 0 0 (by decide) ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₂).hom = ell := by
    simp [κ, β]
  have hkzero (r : ℤ) (hr : r ≠ -1) (hr' : r ≠ 0) : κ.f r = 0 := by
    by_cases h : 0 < r
    · exact (hP r h).eq_of_src _ _
    · apply (mappingCone.isZero_X_iff i r).2 ?_ |>.eq_of_tgt
      exact ⟨isZero_single_obj_X _ _ _ _ (by omega), isZero_single_obj_X _ _ _ _ hr'⟩
  have hv0 : v.f 0 = (mappingCone.snd i).v 0 0 (by decide) ≫ (F.map S.g).f 0 := by
    dsimp only [v, i]
    apply mappingCone.ext_from (F.map S.f) 1 0 (by decide)
    · simp only [Int.reduceNeg, mappingCone.inl_v_snd_v_assoc, zero_comp]
      exact mappingCone.inl_v_descShortComplex_f (S.map F) 1 0 (by decide)
    · simp only [mappingCone.inr_f_snd_v_assoc]
      exact mappingCone.inr_f_descShortComplex_f (S.map F) 0
  have hkv : κ ≫ v = e := by
    apply to_single_hom_ext
    apply (cancel_mono (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₃).hom).1
    calc
      (κ ≫ v).f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₃).hom =
          (κ.f 0 ≫ (mappingCone.snd i).v 0 0 (by decide) ≫
            (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₂).hom) ≫ S.g := by
        simp [hv0, F, single_map_f_self, Category.assoc]
      _ = ell ≫ S.g := by rw [hkl]
      _ = _ := hell
  let fbar := κ ≫ (-(mappingCone.triangle i).mor₃)
  have hbar : fbar.f (-1) ≫
      (shiftFunctorObjXIso (F.obj S.X₁) 1 (-1) 0 (by decide)).hom ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).hom = f := by
    dsimp only [fbar, HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply]
    rw [mappingCone.lift_f i α β hab (-1) 0 (by decide)]
    simp only [Int.reduceNeg, shiftFunctor_obj_X', Int.reduceAdd, Preadditive.comp_neg,
      Preadditive.add_comp, Category.assoc, mappingCone.inl_v_triangle_mor₃_f,
      shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id,
      mappingCone.inr_f_triangle_mor₃_f, comp_zero, add_zero, neg_neg, Iso.refl_hom]
    change (HomComplex.Cochain.toSingleMk f (n := 1) (by decide)).v
      (-1) 0 (by decide) ≫ 𝟙 _ ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).hom = f
    simp
  have hbzero (r : ℤ) (hr : r ≠ -1) : fbar.f r = 0 := by
    apply (isZero_single_obj_X (ComplexShape.up ℤ) 0 S.X₁ (r + 1)
      (by omega)).of_iso (shiftFunctorObjXIso (F.obj S.X₁) 1 r (r + 1) rfl) |>.eq_of_tgt
  have : QuasiIso v := mappingCone.quasiIso_descShortComplex (hS.map_of_exact F)
  refine ⟨f, hf, ?_, hf₂, fbar, hbar, hbzero, κ, hkf, hkl, hkzero, hkv, rfl,
    inferInstance, ?_, inferInstance, ?_⟩
  · intro f' hf'
    exact (cancel_mono S.f).1 (hf'.trans hf.symm)
  · intro r hr
    exact (isZero_single_obj_homology (ComplexShape.up ℤ) 0 S.X₃ r hr).of_iso
      (asIso (homologyMap v r))
  · refine ⟨asIso (DerivedCategory.Q.map v), rfl, ?_⟩
    apply (Iso.eq_comp_inv (asIso (DerivedCategory.Q.map v))).2
    change DerivedCategory.Q.map κ ≫ DerivedCategory.Q.map v = DerivedCategory.Q.map e
    rw [← Functor.map_comp, hkv]

end CochainComplex
