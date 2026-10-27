/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.FiniteConstructibleComplexHeartPresentations
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.Paper.NoetherianScalarConstructibleHeart
import Sheaf.Paper.NoetherianScalarConstructibleFp2
import Sheaf.CategoryTheory.FP2IndRealization
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.ChgUniv
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Noetherian finite-complex heart filtered-colimit closure

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, paragraph (2), first paragraph;
sk-prop-ind-heart/sk-prop-ind-heart.proof.md, the Noetherian heart argument
(blueprint: lem-sfb-qcqs-finite-complex-heart-filtered-closure).

The finite complexes and their replete filtered-colimit class are the existing
finite constant scalar-model constructions. The six coefficient cases are explicit:
the localizing-admissibility predicate also allows a different algebraic-closure
coefficient object with finite-subextension-valued sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

private theorem prop_homology {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    (K : CochainComplex C ℤ) (hK : ∀ n, P (K.X n)) : P (K.homology 0) := by
  exact P.prop_of_isColimit_cokernelCofork (K.homologyIsCokernel (i := -1) (j := 0)
      ((ComplexShape.up ℤ).prev_eq' (by decide)))
    (hK (-1)) (P.prop_of_isLimit_kernelFork
      (K.cyclesIsKernel (i := 0) (j := 1)
        ((ComplexShape.up ℤ).next_eq' (by decide))) (hK 0) (hK 1))

namespace AlgebraicGeometry.ProEtale

/-- On a Noetherian scheme the replete class of small filtered colimits of H^0 of
finite constant scalar-model constructible complexes contains zero and every
constructible module, and is closed under ambient kernels, cokernels, extensions
and small coproducts. Diagram arrows are arbitrary module maps, and extensions
are arbitrary ambient short exact sequences, without finite-stage lifts.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, paragraph (2),
first paragraph, with the Noetherian heart argument of sk-prop-ind-heart.proof.md
(blueprint: lem-sfb-qcqs-finite-complex-heart-filtered-closure).

Proof plan, following the node's four steps:
1. Apply lem-cbc-sieve-module-sheaves-grothendieck on the small pro-etale site
   with scalar Z. The closed symmetric monoidal additive sheaf tensor of
   sk-def-sfb-sheaf-tensor and lem-sfb-modobj-grothendieck make the actual
   internal module category Grothendieck abelian, with exact filtered colimits.
2. Apply lem-sfb-noetherian-scalar-constructible-heart for these six continuous
   coefficient rings. The finite constant scalar-model constructibles are an
   essentially small replete class containing zero and closed under ambient
   kernels, cokernels and extensions, including integral torsion scalar models.
3. For a finite complex K, form Z = ker d^0, T = ker d^-1 and
   B = coker(T -> K^-1) = im d^-1. These are constructible by step 2.
   The complex identity induces B -> Z with cokernel H^0(K), also constructible.
   Conversely C[0] realizes every constructible C. Thus the finite-stage
   classes agree up to isomorphism, as do their filtered-colimit hulls.
   All diagram arrows are module maps; no chain-map lift is needed.
4. The theorem lem-sfb-noetherian-scalar-constructible-fp2 gives both Hom and
   Yoneda Ext1 continuity on all small filtered ambient module diagrams.
   Apply lem-sfb-fp2-ind-realization using steps 1 and 2. Its hull agrees with
   the present class by step 3, giving all six conclusions in the same indexing
   universe. Extension closure uses no supplied finite-stage lift. The empty
   scheme and zero coefficient ring are included in the cited heart theorem.
-/
theorem noetherian_finite_complex_heart_filtered_closure
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    (indFiniteConstructibleComplexHearts Λ X).ContainsZero ∧
    IsConstantModelConstructible Λ X ≤ indFiniteConstructibleComplexHearts Λ X ∧
    (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderKernels ∧
    (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderCokernels ∧
    (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderExtensions ∧
    ∀ I : Type (u + 1),
      (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderColimitsOfShape (Discrete I) := by
  classical
  let B := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let P : ObjectProperty B := IsConstantModelConstructible Λ X
  have : IsGrothendieckAbelian.{u + 1} (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  have : IsGrothendieckAbelian.{u + 1} B := Mod.isGrothendieckAbelian.{u + 1} (condensedRingObj Λ X)
  have : HasColimitsOfSize.{u + 1, u + 1} B := IsGrothendieckAbelian.hasColimits B
  obtain ⟨hsmall, hiso, hzero, hker, hcoker, hext, _⟩ :=
    noetherian_scalar_constructible_heart ℓ Λ hΛ X
  let : EssentiallySmall.{u + 1} P.FullSubcategory := hsmall
  let : P.IsClosedUnderIsomorphisms := hiso
  let : P.ContainsZero := hzero
  let : P.IsClosedUnderKernels := hker
  let : P.IsClosedUnderCokernels := hcoker
  let : P.IsClosedUnderExtensions := hext
  have hstages : finiteConstructibleComplexHearts Λ X = P := by
    funext N
    apply propext
    constructor
    · rintro ⟨K, hK, ⟨e⟩⟩
      apply P.prop_of_iso e.symm
      exact prop_homology P K hK.2
    · intro hN
      refine ⟨(HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj N, ⟨?_, ?_⟩,
        ⟨(HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 N).symm⟩⟩
      · refine ⟨{0}, fun n hn ↦ ?_⟩
        exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simpa using hn)
      · intro n
        by_cases hn : n = 0
        · subst n
          exact P.prop_of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm hN
        · exact P.prop_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hhull : indFiniteConstructibleComplexHearts Λ X = ObjectProperty.ind.{u + 1} P := by
    unfold indFiniteConstructibleComplexHearts
    rw [hstages]
  have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} B := by
    intro C hC
    apply isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr
    have hpre : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
        (preadditiveCoyoneda.obj (Opposite.op C)) := by
      constructor
      intro I _ _
      constructor
      intro M
      have := (noetherian_scalar_constructible_fp2 ℓ Λ hΛ X C hC M).1
      exact preservesColimit_of_isIso_post _ M
    exact inferInstanceAs (PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (preadditiveCoyoneda.obj (Opposite.op C) ⋙ forget Ab))
  have hExt (C : B) (hC : P C) :
      PreservesFilteredColimitsOfSize.{u + 1, u + 1} (Abelian.extFunctorObj.{u + 1} C 1) := by
    let := HasExt.standard B
    obtain ⟨c⟩ := nonempty_yonedaDerivedExtComparison B
    let e : c.yonedaExtOneFunctor C ≅
        Abelian.extFunctorObj.{u + 1} C 1 ⋙ AddCommGrpCat.uliftFunctor.{u + 2} :=
      NatIso.ofComponents (fun M ↦ by
        let := c.classGroup M C 0
        exact ((c.comparison M C 0).trans
          ((Abelian.Ext.chgUnivAddEquiv.{u + 1, u + 2} C M 1).trans
            AddEquiv.ulift.symm)).toAddCommGrpIso) (by
        intro M N f
        let := c.classGroup M C 0
        let := c.classGroup N C 0
        ext x
        change ULift.up (Abelian.Ext.chgUniv.{u + 1}
            ((c.comparison N C 0) ((c.comparison N C 0).symm
              ((Abelian.extFunctorObj.{u + 2} C 1).map f (c.comparison M C 0 x))))) = _
        simp only [AddEquiv.apply_symm_apply]
        congr 1
        change Abelian.Ext.chgUniv.{u + 1}
            ((c.comparison M C 0 x).comp (Abelian.Ext.mk₀ f) (add_zero 1)) =
          (Abelian.Ext.chgUniv.{u + 1} (c.comparison M C 0 x)).comp
            (Abelian.Ext.mk₀ f) (add_zero 1)
        simpa only [Abelian.Ext.chgUniv_mk₀] using
          (Abelian.Ext.chgUniv_comp.{u + 1} (c.comparison M C 0 x)
            (Abelian.Ext.mk₀ f) (add_zero 1)))
    have hp : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
        (c.yonedaExtOneFunctor C) := by
      constructor
      intro I _ _
      constructor
      intro M
      have := (noetherian_scalar_constructible_fp2 ℓ Λ hΛ X C hC M).2 c
      exact preservesColimit_of_isIso_post _ M
    constructor
    intro I _ _
    have : PreservesColimitsOfShape I
        (Abelian.extFunctorObj.{u + 1} C 1 ⋙ AddCommGrpCat.uliftFunctor.{u + 2}) :=
      preservesColimitsOfShape_of_natIso e
    exact preservesColimitsOfShape_of_reflects_of_preserves _ AddCommGrpCat.uliftFunctor
  obtain ⟨hz, hp, _, hsums, hk, hc, he⟩ := ObjectProperty.fp2_ind_realization B P hfp hExt
  rw [hhull]
  exact ⟨hz, hp, hk, hc, he, hsums⟩

end AlgebraicGeometry.ProEtale
