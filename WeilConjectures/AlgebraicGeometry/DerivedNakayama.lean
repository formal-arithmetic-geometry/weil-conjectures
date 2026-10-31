/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaFirstReduction
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealizationSupplement
import Mathlib.Algebra.Homology.Double

/-! # Reduction and derived Nakayama

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
`sk-lem-pe-derived-nakayama/_section.md` (blueprint: sk-lem-pe-derived-nakayama).

The finite coefficient has its explicit rank-one resolution in degrees -1 and 0.
Derived reduction is naturally the cone of the uniformizer power. On unbounded
complexes with continuous pulled-back coefficients, the first reduction detects
zero objects and isomorphisms when the complexes are derived complete.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

/-- The explicit perfect coefficient resolution, the natural reduction cone, and
vanishing and isomorphism detection by first reduction for derived complete complexes.

Source: blueprint latest, sec-proetale-coefficients, the statement and proof of
`sk-lem-pe-derived-nakayama/_section.md` (blueprint: sk-lem-pe-derived-nakayama).
The natural index n here represents the positive exponent n+1.

Proof plan:
1. Take the sectionwise uniformizer endomorphism d and pulled-back short exact
   coefficient sequence from det-pe-derived-nakayama-resolution at exponent n+1.
   Conjugate by regularPullbackIso to obtain the multiplication differential between
   two regular modules. The double complex in degrees -1 and 0, augmented by finiteUnit,
   is a quasi-isomorphism to the quotient in degree zero: injectivity kills degree -1
   homology, exactness and surjectivity identify degree 0, and all other degrees vanish.
   Its terms are rank-one free modules. The same dependency gives the natural cone iso.
2. Use lem-pe-principal-tensor-scalar-extension to identify restricted derived scalar
   extension with reductionFunctor. Exact faithful restriction reflects zero objects,
   by comparison of homology. Vanishing of the first tensor reduction therefore gives
   vanishing of the first finite-coefficient reduction. Apply the vanishing conclusion
   of det-pe-derived-nakayama-first-reduction, which proves every reduction zero by
   the successive quotient triangles and then identifies K with its zero derived limit.
3. Naturality of the same scalar-tensor comparison transfers invertibility of first
   tensor reduction to invertibility after restriction. Exact restriction reflects
   derived isomorphisms by homology. Apply the isomorphism-detection conclusion of
   det-pe-derived-nakayama-first-reduction: the cone is complete with zero first
   reduction, hence is zero, and its original morphism is invertible.
-/
theorem reduction_and_derived_nakayama
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∃ d : End (Mod.regular (integerRing l E)),
      (∀ (S : Profinite.{u}ᵒᵖ) (f : (integerRing l E).obj.obj S) (s : S.unop),
        ((d.hom.hom.app S) f).down s =
          Padic.coefficientExtensionUniformizer l E * f.down s) ∧
      ∀ (X : Scheme.{u}) (n : ℕ),
        (∃ P : CochainComplex (AdicCompletion.Modules l E X) ℤ,
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
    obtain ⟨⟨hz, hs⟩, hc, _⟩ := hres X (n + 1) (by omega)
    refine ⟨?_, hc⟩
    let A := AdicCompletion.Modules l E X
    let f := (pullback l E X).map (d ^ (n + 1))
    let g := (pullback l E X).map (r (n + 1))
    have hr' : r (n + 1) = AdicCompletion.quotientUnit l E n := by
      apply Mod.hom_ext
      exact hr (n + 1)
    let P : CochainComplex A ℤ := HomologicalComplex.double f
      (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)
    let em' : P.X (-1) ≅ _ := HomologicalComplex.doubleXIso₀ f _
    let e0' : P.X 0 ≅ _ := HomologicalComplex.doubleXIso₁ f _ (by decide)
    have hdP : P.d (-1) 0 = em'.hom ≫ f ≫ e0'.inv :=
      HomologicalComplex.double_d f _ (by decide)
    have haug : ∀ j, (ComplexShape.up ℤ).Rel j 0 →
        P.d j 0 ≫ (e0'.hom ≫ g) = 0 := by
      intro j hj
      have : j = -1 := by change j + 1 = 0 at hj; omega
      subst j
      rw [hdP]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [show f ≫ g = 0 from hz, comp_zero]
    let ε := HomologicalComplex.mkHomToSingle (e0'.hom ≫ g) haug
    have hε : ε.f 0 = e0'.hom ≫ g := by
      rw [HomologicalComplex.mkHomToSingle_f]
      change (e0'.hom ≫ g) ≫ 𝟙 _ = e0'.hom ≫ g
      exact Category.comp_id _
    have hs' : (ShortComplex.mk (P.d (-1) 0) (ε.f 0)
        (by rw [hε]; exact haug (-1) (by decide))).ShortExact := by
      apply ShortComplex.shortExact_of_iso
        (ShortComplex.isoMk (S₁ := ShortComplex.mk f g hz)
          (S₂ := ShortComplex.mk (P.d (-1) 0) (ε.f 0)
            (by rw [hε]; exact haug (-1) (by decide)))
          em'.symm e0'.symm (Iso.refl _) ?_ ?_) hs
      · simp [hdP]
      · simp [hε]
    have hqi : QuasiIso ε := by
      rw [quasiIso_iff]
      intro j
      by_cases hj : j = 0
      · subst j
        rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
        rw [ShortComplex.quasiIso_iff_of_zeros' _
          (HomologicalComplex.double_d_eq_zero₀ f
            (show (ComplexShape.up ℤ).Rel (-1) 0 by decide) 0 1 (by decide)) rfl rfl]
        exact ⟨hs'.exact, hs'.epi_g⟩
      · have hL : ((HomologicalComplex.single A (.up ℤ) 0).obj
            (AdicCompletion.finiteModule l E X n)).ExactAt j :=
          HomologicalComplex.ExactAt.of_isZero
            (HomologicalComplex.isZero_single_obj_X _ _ _ _ hj)
        rw [quasiIsoAt_iff_exactAt' ε j hL]
        by_cases hm : j = -1
        · subst j
          rw [HomologicalComplex.exactAt_iff' P (-2) (-1) 0 (by simp) (by simp)]
          rw [ShortComplex.exact_iff_mono _
            (HomologicalComplex.double_d_eq_zero₀ f
              (show (ComplexShape.up ℤ).Rel (-1) 0 by decide) (-2) (-1) (by decide))]
          exact hs'.mono_f
        · exact HomologicalComplex.ExactAt.of_isZero
            (HomologicalComplex.isZero_double_X f _ j hm hj)
    refine ⟨P, ?_, ?_, em' ≪≫ regularPullbackIso l E X,
      e0' ≪≫ regularPullbackIso l E X, ?_, ε, hqi, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro j hj
      exact HomologicalComplex.isZero_double_X f _ j (by omega) (by omega)
    · rw [CochainComplex.isStrictlyLE_iff]
      intro j hj
      exact HomologicalComplex.isZero_double_X f _ j (by omega) (by omega)
    · simpa only [Iso.trans_hom, Iso.trans_inv, Category.assoc,
        Iso.hom_inv_id_assoc] using hdP
    · change ε.f 0 = e0'.hom ≫ (regularPullbackIso l E X).hom ≫
          (regularPullbackIso l E X).inv ≫
            (pullback l E X).map (AdicCompletion.quotientUnit l E n)
      rw [hε]
      dsimp only [g]
      rw [hr']
      simp only [Iso.hom_inv_id_assoc]
  · intro X K hK hzero
    obtain ⟨e, _⟩ := PrincipalNormalization.principal_tensor_scalar_extension l E X
    let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.quotient l E X 0)
    have hV : V.ReflectsIsomorphisms := by
      refine ⟨fun f hf ↦ ?_⟩
      have : IsIso ((Mod.forget (AdicCompletion.finiteRing l E X 0)).map f) := by
        change IsIso ((Mod.forget (AdicCompletion.ring l E X)).map (V.map f))
        infer_instance
      exact isIso_of_reflects_iso f (Mod.forget (AdicCompletion.finiteRing l E X 0))
    have hDV : V.mapDerivedCategory.ReflectsIsomorphisms := by
      refine ⟨fun f _ ↦ ?_⟩
      rw [DerivedCategory.isIso_iff]
      intro j
      have : IsIso (V.map ((DerivedCategory.homologyFunctor _ j).map f)) :=
        (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso j) f).2
          (by rw [Functor.comp_map]; infer_instance)
      exact isIso_of_reflects_iso _ V
    let B := (AdicCompletion.derivedReduction l E X 0).obj K
    have hz : IsZero (V.mapDerivedCategory.obj B) := (e 0).app K |>.isZero_iff.mp hzero
    have : IsIso (V.mapDerivedCategory.map (0 : B ⟶ B)) := by
      rw [Functor.map_zero]
      exact hz.isIso hz _
    have : IsIso (0 : B ⟶ B) := isIso_of_reflects_iso _ V.mapDerivedCategory
    exact ((derived_nakayama_first_reduction l E X).1 K hK
      (IsZero.of_mono_zero B B)).2
  · intro X K L f hK hL hf
    obtain ⟨e, _⟩ := PrincipalNormalization.principal_tensor_scalar_extension l E X
    let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.quotient l E X 0)
    have hV : V.ReflectsIsomorphisms := by
      refine ⟨fun g hg ↦ ?_⟩
      have : IsIso ((Mod.forget (AdicCompletion.finiteRing l E X 0)).map g) := by
        change IsIso ((Mod.forget (AdicCompletion.ring l E X)).map (V.map g))
        infer_instance
      exact isIso_of_reflects_iso g (Mod.forget (AdicCompletion.finiteRing l E X 0))
    have hDV : V.mapDerivedCategory.ReflectsIsomorphisms := by
      refine ⟨fun g _ ↦ ?_⟩
      rw [DerivedCategory.isIso_iff]
      intro j
      have : IsIso (V.map ((DerivedCategory.homologyFunctor _ j).map g)) :=
        (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso j) g).2
          (by rw [Functor.comp_map]; infer_instance)
      exact isIso_of_reflects_iso _ V
    have : IsIso (V.mapDerivedCategory.map
        ((AdicCompletion.derivedReduction l E X 0).map f)) :=
      (NatIso.isIso_map_iff (e 0) f).1 hf
    exact (derived_nakayama_first_reduction l E X).2.2.2 K L f hK hL
      (isIso_of_reflects_iso _ V.mapDerivedCategory)

end AlgebraicGeometry.ProEtale.DerivedNakayama
