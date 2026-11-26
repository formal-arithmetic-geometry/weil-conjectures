/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulDualComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import WeilConjectures.RingTheory.KoszulDerivedDualEvaluation
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Koszul roofs and normalized comparisons

For a Koszul-regular sequence generating `I`, every class in `Ext^r(A/I, A)` is represented by
a roof through the normalized Koszul augmentation, with an explicit signed-dual cycle class.

## Implementation details

The normalized augmentation is constructed explicitly from `I.mkQ` after `zeroEquiv`, rather
than chosen from an existence statement. The Koszul complex is K-projective, so derived maps out
of it lift to chain maps; `exists_koszul_derived_dual_evaluation` compares these with
signed-dual homology, and composing with `Ext.homLinearEquiv` and `Linear.homCongr` gives the
required equivalence. Any augmentation with the given normalization equals the constructed one.

## References

* [Stacks, Tags 0BQZ, 0BQY]
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

-- Degree-one contraction works for every module, without a chosen finite basis.
private theorem contractLeft_exterior_one_formula
    (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    (φ : M →ₗ[A] A) (x : ⋀[A]^1 M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A M)) φ
        (x : ExteriorAlgebra A M) =
      algebraMap A (ExteriorAlgebra A M) (φ (exteriorPower.oneEquiv A M x)) := by
  have he : (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A M)) φ).comp
      (⋀[A]^1 M).subtype =
      (Algebra.linearMap A (ExteriorAlgebra A M)).comp
        (φ.comp (exteriorPower.oneEquiv A M).toLinearMap) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
      Algebra.algebraMap_eq_smul_one]
  exact LinearMap.congr_fun he x

set_option backward.isDefEq.respectTransparency false in
/-- The Koszul augmentation is a quasi-isomorphism to the quotient in degree zero. -/
private theorem normalized_augmentation
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
        (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)),
      QuasiIso ε ∧
      ∀ x : ⋀[A]^0 (Fin r →₀ A),
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of A (A ⧸ I))).hom
          (ε.f 0 (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
        Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x) := by
  let K := koszulComplex A r f
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ I) :=
    ModuleCat.ofHom (I.mkQ.comp (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)
  have hq (x : K.X 0) : q x =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x) := rfl
  have hmem (v : Fin r →₀ A) : Finsupp.linearCombination A f v ∈ I := by
    rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ _
  have hz : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change I.mkQ (exteriorPower.zeroEquiv A (Fin r →₀ A)
      (koszulBoundary A r f 0 x)) = 0
    have hb : exteriorPower.zeroEquiv A (Fin r →₀ A)
        (koszulBoundary A r f 0 x) =
        Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x) := by
      apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.injective
      apply Subtype.ext
      simpa [koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
        Algebra.algebraMap_eq_smul_one] using
          contractLeft_exterior_one_formula A (Fin r →₀ A)
            (Finsupp.linearCombination A f) x
    rw [hb]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (hmem _)
  let ε₀ := (ChainComplex.toSingle₀Equiv K (ModuleCat.of A (A ⧸ I))).symm ⟨q, hz⟩
  have hε₀ : ε₀.f 0 = q := ChainComplex.toSingle₀Equiv_symm_apply_f_zero q hz
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨(exteriorPower.zeroEquiv A (Fin r →₀ A)).symm a, by simp [hq, ha]⟩
  have hex : (ShortComplex.mk (K.d 1 0) q hz).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hxI : exteriorPower.zeroEquiv A (Fin r →₀ A) x ∈ I :=
      (Submodule.Quotient.mk_eq_zero I).mp hx
    rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination] at hxI
    obtain ⟨v, hv⟩ := hxI
    refine ⟨(exteriorPower.oneEquiv A (Fin r →₀ A)).symm v, ?_⟩
    apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).injective
    change exteriorPower.zeroEquiv A (Fin r →₀ A)
      (koszulBoundary A r f 0 _) = _
    apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.injective
    apply Subtype.ext
    let x' : ⋀[A]^0 (Fin r →₀ A) := x
    have hxcoe : (exteriorPower.zeroEquiv A (Fin r →₀ A) x) •
        (1 : ExteriorAlgebra A (Fin r →₀ A)) = (x' : ExteriorAlgebra A (Fin r →₀ A)) := by
      simpa only [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul,
        exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply] using
        congrArg (fun t : ⋀[A]^0 (Fin r →₀ A) ↦ (t : ExteriorAlgebra A (Fin r →₀ A)))
          ((exteriorPower.zeroEquiv A (Fin r →₀ A)).symm_apply_apply x')
    simpa [koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
      LinearEquiv.apply_symm_apply, hv, Algebra.algebraMap_eq_smul_one, hxcoe] using
        contractLeft_exterior_one_formula A (Fin r →₀ A)
          (Finsupp.linearCombination A f) ((exteriorPower.oneEquiv A (Fin r →₀ A)).symm v)
  have hqi : QuasiIso ε₀ := by
    constructor
    intro n
    by_cases hn : n = 0
    · subst n
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_isIso_descOpcycles _ (by simp) (by simp) (by simp)]
      let S := K.sc' 1 0 0
      have : Epi q := (ModuleCat.epi_iff_surjective q).mpr hsurj
      let ei := S.isoOpcyclesOfIsColimit hex.gIsCokernel
      have heq : S.descOpcycles
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat A)
            (ComplexShape.down ℕ) 1 0 0).map ε₀).τ₂
          (by change K.d 1 0 ≫ ε₀.f 0 = 0; rw [hε₀]; exact hz) = ei.inv := by
        apply (cancel_epi S.pOpcycles).mp
        simp only [ShortComplex.p_descOpcycles,
          ShortComplex.pOpcycles_π_isoOpcyclesOfIsColimit_inv, ei]
        exact hε₀
      rw [heq]
      infer_instance
    · rw [quasiIsoAt_iff_exactAt]
      · exact HomologicalComplex.exactAt_single_obj _ _ _ _ hn
      · exact (HomologicalComplex.exactAt_iff_isZero_homology K n).mpr (hreg n hn)
  let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
    (ModuleCat.of A (A ⧸ I)) 0 (0 : ℤ) rfl
  let ε := HomologicalComplex.extendMap ε₀ ComplexShape.embeddingDownNat ≫ e.hom
  have : QuasiIso ε₀ := hqi
  refine ⟨ε, by dsimp [ε]; infer_instance, ?_⟩
  intro x
  simp only [ε, e, K, HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _ (show
    ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl),
    HomologicalComplex.extendSingleIso_hom_f, hε₀, ModuleCat.comp_apply,
    Iso.inv_hom_id_apply,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.id_comp]
  have hi (X Y : ModuleCat A) (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by
    change (e.inv ≫ e.hom) y = y
    rw [e.inv_hom_id]
    rfl
  change q ((HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat
    (i := 0) rfl).hom
      ((HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat
        (i := 0) rfl).inv x)) = _
  rw [hi]
  exact hq x

private theorem koszul_Q_map_surjective
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (r : ℕ) (f : Fin r → A) (T : CochainComplex (ModuleCat.{u} A) ℤ) :
    Function.Surjective (DerivedCategory.Q.map :
      ((koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶ T) → _) := by
  let E := (koszulComplex A r f).extend ComplexShape.embeddingDownNat
  have (n : ℕ) : Projective ((koszulComplex A r f).X n) :=
    ModuleCat.projective_of_free
      ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n)
  have : CochainComplex.IsKProjective E := inferInstance
  intro v
  let a := (DerivedCategory.quotientCompQhIso (ModuleCat A)).app E
  let b := (DerivedCategory.quotientCompQhIso (ModuleCat A)).app T
  obtain ⟨h, hh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective E
    ((HomotopyCategory.quotient _ _).obj T)).surjective (a.hom ≫ v ≫ b.inv)
  obtain ⟨z, hz⟩ := (HomotopyCategory.quotient _ _).map_surjective h
  refine ⟨z, ?_⟩
  apply (cancel_epi a.hom).mp
  have he := DerivedCategory.quotientCompQhIso_hom_naturality z
  simpa [a, b, hz, hh] using he.symm

private theorem koszul_dual_differential_above_rank_zero
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (i n : ℕ) (hn : r < n) : (koszulDualComplex A r f).d i n = 0 := by
  classical
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower
    n
  have : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun s ↦ by
    have hcard : s.val.card ≤ r := by simpa using Finset.card_le_univ s.val
    have hscard : s.val.card = n := s.property
    omega⟩
  have : Subsingleton (⋀[A]^n (Fin r →₀ A)) := b.repr.injective.subsingleton
  have : Subsingleton ((koszulComplex A r f).X n ⟶ ModuleCat.of A A) := by
    change Subsingleton
      (ModuleCat.of A (⋀[A]^n (Fin r →₀ A)) ⟶ ModuleCat.of A A)
    refine ⟨fun x y ↦ ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  have : Subsingleton ((koszulDualComplex A r f).X n) := ‹_›
  ext x
  exact Subsingleton.elim _ _

private theorem koszul_top_cycle
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (a : (koszulComplex A r f).X r ⟶ ModuleCat.of A A) :
    ∃ y : (koszulDualComplex A r f).cycles r,
      (koszulDualComplex A r f).iCycles r y = a := by
  let S := (koszulDualComplex A r f).sc r
  have hg : S.g = 0 := by
    change (koszulDualComplex A r f).d r ((ComplexShape.up ℕ).next r) = 0
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel r (r + 1) from rfl)]
    exact koszul_dual_differential_above_rank_zero A r f r (r + 1) (by omega)
  let x : LinearMap.ker S.g.hom := ⟨a, by
    change S.g a = 0
    rw [hg]
    rfl⟩
  refine ⟨S.moduleCatCyclesIso.inv x, ?_⟩
  exact S.moduleCatCyclesIso_inv_iCycles_apply x

/-- Ext classes have roof representatives with their actual signed-dual cycle class. -/
theorem exists_koszul_ext_roof_representatives
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ d : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
        (koszulDualComplex A r f).homology r,
      ∀ (ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
        [QuasiIso ε],
        (∀ x : ⋀[A]^0 (Fin r →₀ A),
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (A ⧸ I))).hom
            (ε.f 0 (((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
          Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) →
        ∀ x : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r,
          ∃ (z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
              (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj
                (ModuleCat.of A A))
            (y : (koszulDualComplex A r f).cycles r),
            x = (Abelian.Ext.homLinearEquiv (R := A)).symm
              (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
                ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
                  (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
                    (ModuleCat.of A A)) ∧
            d x = (koszulDualComplex A r f).homologyπ r y ∧
            (koszulDualComplex A r f).iCycles r y = (((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ z.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom) := by
  obtain ⟨e, he⟩ := exists_koszul_derived_dual_evaluation A r f
  obtain ⟨ε₀, hqi, hε₀⟩ := normalized_augmentation A I r f hreg hf
  have : QuasiIso ε₀ := hqi
  let s := ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
    (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).app (ModuleCat.of A A)
  let c := Linear.homCongr A (asIso (DerivedCategory.Q.map ε₀)).symm s
  let d := (Abelian.Ext.homLinearEquiv (R := A)).trans (c.trans e)
  refine ⟨d, ?_⟩
  intro ε _ hε x
  have hεeq : ε = ε₀ := by
    apply HomologicalComplex.to_single_hom_ext
    apply (cancel_epi ((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := 0) rfl).inv).mp
    apply (cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of A (A ⧸ I))).hom).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact (hε v).trans (hε₀ v).symm
  subst ε
  obtain ⟨z, hz⟩ := koszul_Q_map_surjective A r f
    ((CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (c (Abelian.Ext.homLinearEquiv (R := A) x))
  obtain ⟨y, hev⟩ := koszul_top_cycle A r f
    (((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ z.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom)
  have hy := he z y hev
  refine ⟨z, y, ?_, ?_, hev⟩
  · apply (Abelian.Ext.homLinearEquiv (R := A)).injective
    change Abelian.Ext.homLinearEquiv x = _
    rw [LinearEquiv.apply_symm_apply]
    have hx := congrArg c.symm hz
    simpa [c, Linear.homCongr_symm_apply, s] using hx.symm
  · change e (c (Abelian.Ext.homLinearEquiv (R := A) x)) = _
    rw [← hz]
    exact hy

end ExteriorAlgebra
