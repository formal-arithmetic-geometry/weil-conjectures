/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Paper.DerivedNakayamaFirstReduction
import Sheaf.Paper.IntegralResidueTensorPresentation
import Mathlib.Algebra.Homology.Double
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Reduction and derived Nakayama

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/_section.md` (blueprint: sk-lem-pe-derived-nakayama).

The perfect resolution is stated by its bounded rank-one free representative, its
specified differential, and its quasi-isomorphic augmentation to the finite coefficient.
The natural cone comparison uses the existing localized mapping-cone functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

/-- Build the two-term resolution from a short exact sequence, checking homology
in degrees -1 and 0 and using zero terms in all other degrees. -/
private theorem twoTermResolution {C : Type*} [Category C] [Abelian C]
    {A B M : C} (f : A ⟶ B) (q : B ⟶ M)
    (hw : f ≫ q = 0)
    (hex : (ShortComplex.mk f q hw).Exact) [Mono f] [Epi q] :
    ∃ (P : CochainComplex C ℤ)
      (_hge : P.IsStrictlyGE (-1)) (_hle : P.IsStrictlyLE 0),
      ∃ (em : P.X (-1) ≅ A) (e0 : P.X 0 ≅ B),
        P.d (-1) 0 = em.hom ≫ f ≫ e0.inv ∧
        ∃ ε : P ⟶ (CochainComplex.singleFunctor C 0).obj M,
          QuasiIso ε ∧
          ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = e0.hom ≫ q ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) := by
  classical
  have hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  let P : CochainComplex C ℤ := HomologicalComplex.double f hrel
  let em := HomologicalComplex.doubleXIso₀ f hrel
  let e0 := HomologicalComplex.doubleXIso₁ f hrel (by omega)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (P.X i) :=
    HomologicalComplex.isZero_double_X f hrel i hm h0
  have hge : P.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hle : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  let L := (CochainComplex.singleFunctor C 0).obj M
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
  let ε : P ⟶ L := HomologicalComplex.mkHomFromDouble hrel (by omega) 0 (q ≫ e.inv)
    (by change 0 ≫ L.d (-1) 0 = f ≫ q ≫ e.inv
        rw [zero_comp, ← Category.assoc, show f ≫ q = 0 from hw, zero_comp])
    (by intro i hi; exact (hL i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = e0.hom ≫ q := by
    simp [ε, e0]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hL i hi).eq_of_tgt _ _
  have hmono : Mono (P.d (-1) 0) := by
    dsimp [P]
    rw [HomologicalComplex.double_d f hrel (by omega)]
    infer_instance
  have hε : QuasiIso ε := by
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hz 1 (by omega) (by omega)).eq_of_tgt _ _)
        ((hL (-1) (by omega)).eq_of_src _ _)
        ((hL 1 (by omega)).eq_of_tgt _ _)).2
      have heq : P.d (-1) 0 ≫ ε.f 0 = 0 := by
        rw [← ε.comm]
        simp [hεi (-1) (by omega)]
      let S := ShortComplex.mk (P.d (-1) 0) (ε.f 0) heq
      let T := ShortComplex.mk f q hw
      let iso : S ≅ T := ShortComplex.isoMk em e0 e
        (by dsimp [S, T, P, em, e0]; rw [HomologicalComplex.double_d f hrel (by omega)]; simp)
        hε0.symm
      have hs : S.Exact := (ShortComplex.exact_iff_of_iso iso).2 hex
      have : Epi (ε.f 0) := by
        have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
        exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
      exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
    · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hm : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' P (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
        exact hmono
      · exact HomologicalComplex.ExactAt.of_isZero (hz i hm hi)
  exact ⟨P, hge, hle, em, e0, HomologicalComplex.double_d f hrel (by omega),
    ε, hε, hε0, hεi⟩

private def reductionComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n ≅
      reductionFunctor l E X (n + 1) := by
  let e : (Mod.comap (AdicCompletion.quotient l E X n)).obj
      (Mod.regular (AdicCompletion.finiteRing l E X n)) ≅
      AdicCompletion.finiteModule l E X n :=
    ((upperStarFromPoint X).mapModComapIso (reductionRing l E (n + 1))).symm.app
      (Mod.regular (quotientRing l E (n + 1)))
  exact Mod.residueDerivedTensorIso (AdicCompletion.quotient l E X n) ≪≫
    (curriedTensor (Derived l E X)).flip.mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso e)

private theorem reflectZero {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (K : DerivedCategory C) (h : IsZero (F.mapDerivedCategory.obj K)) :
    IsZero K := by
  apply (DerivedCategory.isZero_iff K).2
  intro j
  exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.homologyFunctor D j).map_isZero h)

private theorem reflectIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] {K L : DerivedCategory C} (f : K ⟶ L)
    (h : IsIso (F.mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro j
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C j).map f)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso j) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

/-- The finite coefficient has the two-term perfect resolution, derived reduction is its
natural cone, and first reduction detects zero objects and isomorphisms among complete objects.
Source: blueprint main-20261015, Reduction and derived Nakayama, statement and proof
(blueprint: sk-lem-pe-derived-nakayama).

Proof:
1. Apply lem-weil-pbc-standard-quotients-perfect with the chosen uniformizer pi_E.
   The exact inverse image from the point gives the coefficient exact sequence of
   det-pe-derived-nakayama-resolution. Put its two regular modules in degrees -1 and 0,
   and augment by the quotient map. The kernel and cokernel calculation shows that the
   augmentation is a quasi-isomorphism. The terms are free of rank one in those degrees
   and zero elsewhere. This is a perfect resolution: the identity covering and the
   identity rank-one splittings give def-weil-pbc-strict-perfect-coefficient-package.
   The natural cone identification is det-pe-derived-nakayama-resolution, computed by
   tensoring this bounded flat resolution with a K-flat representative of K.
2. If K_1 vanishes, use the quotient-power triangles with m=1 inductively to show all
   positive reductions vanish. Completeness identifies K with their derived inverse
   limit, which is zero (det-pe-derived-nakayama-first-reduction, Vanishing).
3. Complete complexes are closed under cones: reduction and the derived inverse limit
   are exact, and their canonical comparison is natural. The cone of f therefore is
   complete and its first reduction is zero when f_1 is invertible. Step 2 kills the
   cone, so f is invertible (det-pe-derived-nakayama-first-reduction, Isomorphisms).
No boundedness or constructibility of K or L, or invertibility of l on X, is required. -/
theorem reduction_and_derived_nakayama (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∃ d : End (Mod.regular (integerRing l E)),
      (∀ (S : Profinite.{u}ᵒᵖ) (f : (integerRing l E).obj.obj S) (s : S.unop),
        ((d.hom.hom.app S) f).down s =
          Padic.coefficientExtensionUniformizer l E * f.down s) ∧
      ∀ (X : Scheme.{u}) (n : ℕ),
        (∃ (P : CochainComplex (AdicCompletion.Modules l E X) ℤ),
          P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0 ∧
          ∃ (em : P.X (-1) ≅ Mod.regular (AdicCompletion.ring l E X))
            (e0 : P.X 0 ≅ Mod.regular (AdicCompletion.ring l E X)),
            P.d (-1) 0 = em.hom ≫ (regularPullbackIso l E X).inv ≫
              (pullback l E X).map (d ^ (n + 1)) ≫
                (regularPullbackIso l E X).hom ≫ e0.inv ∧
            ∃ ε : P ⟶ (CochainComplex.singleFunctor (AdicCompletion.Modules l E X) 0).obj
                (AdicCompletion.finiteModule l E X n),
              QuasiIso ε ∧ ε.f 0 = e0.hom ≫ AdicCompletion.finiteUnit l E X n) ∧
        Nonempty (DerivedCategory.Q ⋙ reductionFunctor l E X (n + 1) ≅
          coneFunctor l E X (d ^ (n + 1)))) ∧
    (∀ (X : Scheme.{u}) (K : Derived l E X),
      IsDerivedComplete l E X K →
      IsZero ((reductionFunctor l E X 1).obj K) → IsZero K) ∧
    (∀ (X : Scheme.{u}) (K L : Derived l E X) (f : K ⟶ L),
      IsDerivedComplete l E X K → IsDerivedComplete l E X L →
      IsIso ((reductionFunctor l E X 1).map f) → IsIso f) := by
  obtain ⟨d, hd, r, hr, i, q, hi, hq, hseq⟩ := derived_nakayama_resolution l E
  refine ⟨⟨d, hd, ?_⟩, ?_, ?_⟩
  · intro X n
    obtain ⟨⟨hw, hs⟩, hc, _⟩ := hseq X (n + 1) (by omega)
    refine ⟨?_, hc⟩
    have hr' : r (n + 1) = AdicCompletion.quotientUnit l E n := by
      apply (Mod.forget _).map_injective
      exact hr (n + 1)
    let a := (regularPullbackIso l E X).inv ≫
      (pullback l E X).map (d ^ (n + 1)) ≫ (regularPullbackIso l E X).hom
    let b := AdicCompletion.finiteUnit l E X n
    have hab : a ≫ b = 0 := by
      dsimp [a, b, AdicCompletion.finiteUnit]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← hr', hw, comp_zero]
    let S := ShortComplex.mk a b hab
    let T := ShortComplex.mk _ _ hw
    let e : S ≅ T := ShortComplex.isoMk
      (regularPullbackIso l E X).symm (regularPullbackIso l E X).symm
      (Iso.refl _) (by simp [S, T, a]) (by simp [S, T, b, AdicCompletion.finiteUnit, hr'])
    have hsS : S.ShortExact := (ShortComplex.shortExact_iff_of_iso e).2 hs
    have : Mono a := hsS.mono_f
    have : Epi b := hsS.epi_g
    obtain ⟨P, hge, hle, em, e0, hdP, ε, hε, hε0, _⟩ :=
      twoTermResolution a b hab hsS.exact
    refine ⟨P, hge, hle, em, e0, hdP, ε, hε, ?_⟩
    change ε.f 0 = e0.hom ≫ b
    change ε.f 0 ≫ 𝟙 _ = e0.hom ≫ b at hε0
    simpa only [Category.comp_id] using hε0
  · intro X K hK hzero
    apply ((derived_nakayama_first_reduction l E X).1 K hK ?_).2
    apply reflectZero (Mod.comap (AdicCompletion.quotient l E X 0))
    exact hzero.of_iso ((reductionComparison l E X 0).app K)
  · intro X K L f hK hL hf
    apply (derived_nakayama_first_reduction l E X).2.2.2 K L f hK hL
    have : (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.quotient l E X 0)).ReflectsIsomorphisms := by
      constructor
      intro A B g hg
      have : IsIso ((Mod.forget (AdicCompletion.ring l E X)).map
          ((Mod.comap (AdicCompletion.quotient l E X 0)).map g)) := inferInstance
      have : IsIso ((Mod.forget (AdicCompletion.finiteRing l E X 0)).map g) :=
        ‹IsIso ((Mod.forget (AdicCompletion.ring l E X)).map
          ((Mod.comap (AdicCompletion.quotient l E X 0)).map g))›
      exact isIso_of_reflects_iso g (Mod.forget (AdicCompletion.finiteRing l E X 0))
    apply reflectIso (Mod.comap (AdicCompletion.quotient l E X 0))
    exact (NatIso.isIso_map_iff (reductionComparison l E X 0) f).mpr hf

end AlgebraicGeometry.ProEtale.DerivedNakayama
