/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import Sheaf.Paper.DerivedNakayamaResolution
import Mathlib.Algebra.Homology.Double
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Sheaf.Paper.DerivedNakayamaFirstReduction

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

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite HomologicalComplex
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

/-- A short exact presentation gives a two-term resolution with its specified augmentation.
Source: blueprint resolution, On X, and Mathlib's `HomologicalComplex.double`.
The only nonzero homology is the cokernel in degree zero; injectivity kills degree -1.
(blueprint: sk-lem-pe-derived-nakayama). -/
private theorem twoTermResolution {C : Type*} [Category C] [Abelian C]
    {A B M : C} (f : A ⟶ B) (q : B ⟶ M) (hw : f ≫ q = 0)
    (hex : (ShortComplex.mk f q hw).ShortExact) :
    ∃ P : CochainComplex C ℤ,
      P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0 ∧
      ∃ (em : P.X (-1) ≅ A) (e0 : P.X 0 ≅ B),
        P.d (-1) 0 = em.hom ≫ f ≫ e0.inv ∧
        ∃ ε : P ⟶ (CochainComplex.singleFunctor C 0).obj M,
          QuasiIso ε ∧ ε.f 0 = e0.hom ≫ q := by
  classical
  have hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  let P : CochainComplex C ℤ := double f hrel
  let em := doubleXIso₀ f hrel
  let e0 := doubleXIso₁ f hrel (by omega)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (P.X i) :=
    isZero_double_X f hrel i hm h0
  have hge : P.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hle : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  let L := (CochainComplex.singleFunctor C 0).obj M
  let e := singleObjXSelf (.up ℤ) 0 M
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    isZero_single_obj_X (.up ℤ) 0 M i hi
  let ε : P ⟶ L := mkHomFromDouble hrel (by omega) 0 (q ≫ e.inv)
    (by change 0 ≫ L.d (-1) 0 = f ≫ q ≫ e.inv
        rw [zero_comp, ← Category.assoc, hw, zero_comp])
    (by intro i hi; exact (hL i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = e0.hom ≫ q := by simp [ε, e0]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hL i hi).eq_of_tgt _ _
  have hmono : Mono (P.d (-1) 0) := by
    have : Mono f := hex.mono_f
    dsimp [P]
    rw [double_d f hrel (by omega)]
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
        (by dsimp [S, T, P, em, e0]; rw [double_d f hrel (by omega)]; simp)
        hε0.symm
      have hs : S.Exact := (ShortComplex.exact_iff_of_iso iso).2 hex.exact
      have : Epi (ε.f 0) := by
        have : Epi q := hex.epi_g
        have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
        exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
      exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
    · have hLex : L.ExactAt i := ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hm : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' P (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
        exact hmono
      · exact ExactAt.of_isZero (hz i hm hi)
  refine ⟨P, hge, hle, em, e0, double_d f hrel (by omega), ε, hε, ?_⟩
  change ε.f 0 ≫ 𝟙 M = e0.hom ≫ q at hε0
  exact (Category.comp_id (ε.f 0)).symm.trans hε0

/-- Vanishing of tensor reduction implies vanishing of derived scalar extension.
Source: blueprint resolution, On X, computing derived reduction on a K-flat representative.
Pullback commutes with restriction of scalars and preserves the regular module. On a
K-flat representative the tensor model and scalar extension have isomorphic underlying
complexes by `Mod.extendForgetTensorIso`. Exact faithful forgetting detects acyclicity;
the derived counit on that representative then identifies derived scalar extension.
(blueprint: sk-lem-pe-derived-nakayama). -/
private theorem isZero_derivedReduction_of_isZero_tensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : Derived l E X)
    (hz : IsZero ((reductionFunctor l E X 1).obj K)) :
    IsZero ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  classical
  let R := AdicCompletion.ring l E X
  let S := AdicCompletion.finiteRing l E X 0
  let q := AdicCompletion.quotient l E X 0
  let B := (Mod.comap q).obj (Mod.regular S)
  let eS : ((upperStarFromPoint X).mapMod (quotientRing l E 1)).obj
      (Mod.regular (quotientRing l E 1)) ≅ Mod.regular S :=
    Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  let eB : AdicCompletion.finiteModule l E X 0 ≅ B :=
    ((upperStarFromPoint X).mapModComapIso (reductionRing l E 1)).app
      (Mod.regular (quotientRing l E 1)) ≪≫ (Mod.comap q).mapIso eS
  have (Z : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj Z) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Z)
      (NatIso.ofComponents (fun Y ↦ β_ Z Y) (by intros; simp [curriedTensor]))
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P).1 hP
  let eP : DerivedCategory.Q.obj P ≅ K :=
    (DerivedCategory.quotientCompQhIso _).symm.app P ≪≫ e
  have hzP : IsZero ((reductionFunctor l E X 1).obj (DerivedCategory.Q.obj P)) :=
    hz.of_iso ((reductionFunctor l E X 1).mapIso eP)
  have hzB : IsZero (DerivedCategory.Q.obj P ⊗
      (DerivedCategory.singleFunctor _ 0).obj B) :=
    hzP.of_iso (whiskerLeftIso (DerivedCategory.Q.obj P)
      ((DerivedCategory.singleFunctor _ 0).mapIso eB)).symm
  have hright : (((tensorRight B).mapHomologicalComplex (.up ℤ)).obj P).Acyclic :=
    (DerivedCategory.isZero_Q_obj_iff _).1 (hzB.of_iso
      (DerivedCategory.QObjTensorSingleFunctorObjIso P hP' B).symm)
  have hleft : (((tensorLeft B).mapHomologicalComplex (.up ℤ)).obj P).Acyclic :=
    hright.of_iso ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight B) (.up ℤ)).app P).symm
  have hforget := hleft.map (Mod.forget R)
  have hextforget := hforget.of_iso
    ((NatIso.mapHomologicalComplex (Mod.extendForgetTensorIso q) (.up ℤ)).app P).symm
  have hext : (((Mod.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ (Mod.forget S)).1 (hextforget n)
  have hzext := (DerivedCategory.isZero_Q_obj_iff _).2 hext
  let ext := Mod.extendScalars q
  let ε := ext.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)
  have : IsIso ε := ext.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP'
  have hzLP : IsZero (ext.leftDerivedFunctor.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) :=
    (hzext.of_iso ((DerivedCategory.quotientCompQhIso _).app _)).of_iso (asIso ε)
  exact hzLP.of_iso (ext.leftDerivedFunctor.mapIso e.symm)

/-- The finite coefficient has the two-term perfect resolution, derived reduction is its
natural cone, and first reduction detects zero objects and isomorphisms among complete objects.
Source: blueprint main-20261015, Reduction and derived Nakayama, statement and proof
(blueprint: sk-lem-pe-derived-nakayama).

Proof:
1. Use the short exact sequence and natural cone comparison of
   det-pe-derived-nakayama-resolution. Transport the two regular terms along
   regularPullbackIso and identify its quotient arrow with finiteUnit by extensionality.
   Put the transported differential in degrees -1 and 0 using double. Its augmentation
   is quasi-isomorphic: short exactness computes degree zero, injectivity gives vanishing
   in degree -1, and all other terms vanish. The terms in those two degrees have the
   displayed rank-one identifications, as required for the finite free resolution.
2. Identify the pulled-back quotient module with the quotient ring's regular module
   restricted to integral scalars. On a K-flat representative, tensor reduction is zero
   exactly when its termwise tensor complex is acyclic. The underlying scalar-extension
   complex is isomorphic to that tensor complex; faithful exact forgetting detects its
   acyclicity. The derived counit is invertible on the representative. Apply the vanishing
   clause of det-pe-derived-nakayama-first-reduction to this derived scalar extension.
3. Complete f to a distinguished triangle. The cone is complete by
   det-pe-derived-nakayama-first-reduction. Tensor reduction is triangulated, so an
   invertible reduced f makes its reduced cone zero. Step 2 and the same vanishing
   clause kill the cone. The zero-cone criterion makes f invertible.
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
  classical
  obtain ⟨d, hd, r, hr, i, q, hi, hq, hres⟩ := derived_nakayama_resolution l E
  refine ⟨⟨d, hd, ?_⟩, ?_, ?_⟩
  · intro X n
    obtain ⟨⟨hw, hs⟩, hc, _⟩ := hres X (n + 1) (by omega)
    refine ⟨?_, hc⟩
    let e := regularPullbackIso l E X
    have hrn : r (n + 1) = AdicCompletion.quotientUnit l E n := by
      apply Mod.hom_ext
      exact hr (n + 1)
    have hw' : (e.inv ≫ (pullback l E X).map (d ^ (n + 1)) ≫ e.hom) ≫
        AdicCompletion.finiteUnit l E X n = 0 := by
      dsimp only [AdicCompletion.finiteUnit]
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
        ← hrn, hw, comp_zero]
    have hs' : (ShortComplex.mk _ _ hw').ShortExact := by
      let iso : ShortComplex.mk _ _ hw' ≅ ShortComplex.mk _ _ hw :=
        ShortComplex.isoMk e.symm e.symm (Iso.refl _)
          (by simp [e]) (by simp [AdicCompletion.finiteUnit, e, hrn])
      exact (ShortComplex.shortExact_iff_of_iso iso).2 hs
    obtain ⟨P, hge, hle, em, e0, hdiff, ε, hε, hε0⟩ :=
      twoTermResolution _ _ hw' hs'
    exact ⟨P, hge, hle, em, e0, hdiff, ε, hε, hε0⟩
  · intro X K hK hz
    exact ((derived_nakayama_first_reduction l E X).1 K hK
      (isZero_derivedReduction_of_isZero_tensor l E X K hz)).2
  · intro X K L f hK hL hf
    obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    let T := Pretriangulated.Triangle.mk f g h
    have hC : IsDerivedComplete l E X C :=
      (derived_nakayama_first_reduction l E X).2.1 T hT hK hL
    let B := (DerivedCategory.singleFunctor (AdicCompletion.Modules l E X) 0).obj
      (AdicCompletion.finiteModule l E X 0)
    let F := (curriedTensor (Derived l E X)).flip.obj B
    let : F.CommShift ℤ := DerivedCategory.commShiftTensorRight (AdicCompletion.Modules l E X) B
    have : F.IsTriangulated :=
      DerivedCategory.isTriangulated_tensorRight (AdicCompletion.Modules l E X) B
    have hred : IsZero ((reductionFunctor l E X 1).obj C) :=
      (F.mapTriangle.obj T).isZero₃_of_isIso₁
        (F.map_distinguished T hT) hf
    have hzC := ((derived_nakayama_first_reduction l E X).1 C hC
      (isZero_derivedReduction_of_isZero_tensor l E X C hred)).2
    exact (T.isZero₃_iff_isIso₁ hT).1 hzC

end AlgebraicGeometry.ProEtale.DerivedNakayama
