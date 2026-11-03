/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroRepresentativeData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleRepresentative
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleSurjective
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
public import WeilConjectures.SixFunctors.CoefficientHomZeroClosedTransposeCompatibility

/-! The representative-input transpose step for H-zero scalar normalization.
Source: Stacks 03CZ, 079P and 08JA.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-representative)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem uncurry_precomp {X Y : B} (f : X ⟶ Y) (K N : B)
    (q : Y ⟶ I.obj (op K, N)) :
    (T.transpose X K N).symm (f ≫ q) =
      T.tensor.map (Prod.mkHom f (𝟙 K)) ≫ (T.transpose Y K N).symm q := by
  let := T.monoidal
  have h := (T.adjunction K).homEquiv_naturality_left_symm f q
  change (T.transpose X K N).symm (f ≫ q) =
    (f ▷ K) ≫ (T.transpose Y K N).symm q at h
  rw [show T.tensor.map (Prod.mkHom f (𝟙 K)) = (f ▷ K) by
    exact MonoidalCategory.tensorHom_id f K]
  exact h

/-- Closed scalar transposition at the monoidal unit follows from the five Hom
bijections and the left-unit coherence square. -/
private theorem scalar_unit_transpose
    (hunit : ∀ K : A,
      (μ.app (S.monoidal.tensorUnit, K)).hom ≫
          T.tensor.map (Prod.mkHom e.hom (𝟙 (F.obj K))) ≫
          (T.monoidal.leftUnitor (F.obj K)).hom =
        F.map (S.monoidal.leftUnitor K).hom)
    (K : A) (N : B) (q : S.monoidal.tensorUnit ⟶ H.obj (op K, U.obj N)) :
    (T.monoidal.leftUnitor (F.obj K)).inv ≫
        (T.transpose T.monoidal.tensorUnit (F.obj K) N).symm
          (e.inv ≫ (adj.homEquiv S.monoidal.tensorUnit _).symm
            (q ≫ (iso S T adj μ).inv.app (op K, N))) =
      (adj.homEquiv K N).symm
        ((S.monoidal.leftUnitor K).inv ≫
          (S.transpose S.monoidal.tensorUnit K (U.obj N)).symm q) := by
  let :=  S.monoidal
  let :=  T.monoidal
  let t := q ≫ (iso S T adj μ).inv.app (op K, N)
  have ht : bijection S T adj μ S.monoidal.tensorUnit K N t = q := by
    rw [representing]
    simp [t]
  have hc : (μ.app (S.monoidal.tensorUnit, K)).hom ≫
      (T.transpose (F.obj S.monoidal.tensorUnit) (F.obj K) N).symm
        ((adj.homEquiv S.monoidal.tensorUnit _).symm t) =
      (adj.homEquiv _ N).symm
        ((S.transpose S.monoidal.tensorUnit K (U.obj N)).symm q) := by
    apply (adj.homEquiv _ N).injective
    apply (S.transpose S.monoidal.tensorUnit K (U.obj N)).injective
    simpa only [bijection, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
      Iso.symm_inv, Iso.refl_hom, Category.comp_id, Equiv.apply_symm_apply] using ht
  have hu : F.map (S.monoidal.leftUnitor K).inv ≫
        (μ.app (S.monoidal.tensorUnit, K)).hom =
      (T.monoidal.leftUnitor (F.obj K)).inv ≫
        T.tensor.map (Prod.mkHom e.inv (𝟙 (F.obj K))) := by
    have : IsIso (Prod.mkHom e.hom (𝟙 (F.obj K))) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    apply (cancel_mono (T.tensor.map (Prod.mkHom e.hom (𝟙 (F.obj K))) ≫
      (T.monoidal.leftUnitor (F.obj K)).hom)).mp
    simp only [Category.assoc, hunit]
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
    have hc : T.tensor.map (Prod.mkHom e.inv (𝟙 (F.obj K))) ≫
        T.tensor.map (Prod.mkHom e.hom (𝟙 (F.obj K))) = 𝟙 _ := by
      rw [← T.tensor.map_comp]
      simp
    rw [← Category.assoc (T.tensor.map _) (T.tensor.map _), hc]
    simp
  rw [uncurry_precomp]
  rw [← Category.assoc, ← hu, Category.assoc, hc]
  exact (adj.homEquiv_naturality_left_symm (S.monoidal.leftUnitor K).inv
    ((S.transpose S.monoidal.tensorUnit K (U.obj N)).symm q)).symm

/-- Naturality of the specified unit-section identification follows from
naturality of the fixed Hom-zero family and of the inverse unit-Hom isomorphism.
Source: Stacks 08JA (blueprint:
lem-coef-derived-sections-normalization-scalar-hom-zero-representative). -/
private theorem coefficientHomZeroUnitEquiv_naturality_local
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, u} J A)]
    (S₀ : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    {K L : DerivedCategory (RingedDerivedNative.Modules.{c, v, u} J A)}
    (f : K ⟶ L)
    (x : (ringedSiteZerothHypercohomologyOfUniverses.{c, v, u, w} J A).obj K) :
    coefficientHomZeroUnitEquiv.{c, v, u, w} J A S₀ L
        ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, u, w} J A).map f x) =
      coefficientHomZeroUnitEquiv.{c, v, u, w} J A S₀ K x ≫ f := by
  let Γ := ringedSiteZerothHypercohomologyOfUniverses.{c, v, u, w} J A
  have hj : f ≫ (coefficientClosedUnitHomIso S₀ L).inv =
      (coefficientClosedUnitHomIso S₀ K).inv ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J A).map
          (Prod.mkHom (𝟙 (op S₀.monoidal.tensorUnit)) f) := by
    exact (Adjunction.rightAdjointUniq (S₀.adjunction S₀.monoidal.tensorUnit)
      (Adjunction.id.ofNatIsoLeft
        (@MonoidalCategory.rightUnitorNatIso _ _ S₀.monoidal).symm)).inv.naturality f
  obtain ⟨SN, hSN, TN, hTN⟩ := RingedDerivedNative.closedAdjunction.{c, v, u, w} J A
  have hn := (coefficientHomZeroClosedTransposeCompatibility J A SN hSN TN hTN).2
    S₀.monoidal.tensorUnit S₀.monoidal.tensorUnit K L (𝟙 _) f
      (Γ.map (coefficientClosedUnitHomIso S₀ K).inv x)
  change coefficientHomZeroEquiv.{u, c, v, w} J A S₀.monoidal.tensorUnit L
      (Γ.map (coefficientClosedUnitHomIso S₀ L).inv (Γ.map f x)) =
    coefficientHomZeroEquiv.{u, c, v, w} J A S₀.monoidal.tensorUnit K
      (Γ.map (coefficientClosedUnitHomIso S₀ K).inv x) ≫ f
  rw [← AddCommGrpCat.comp_apply, ← Γ.map_comp, hj, Γ.map_comp,
    AddCommGrpCat.comp_apply]
  simpa only [op_id, Category.id_comp] using hn

/-- The tensor comparison carried by the normalized scalar-extension lift.
Source: Stacks 07A4 (blueprint:
lem-coef-derived-sections-normalization-scalar-hom-zero-representative). -/
def coefficientScalarTensor : Y.closed.tensor ⋙ l.edge.left ≅
    l.edge.left.prod l.edge.left ⋙ X.closed.tensor :=
  letI := Y.closed.monoidal
  letI := X.closed.monoidal
  (@Functor.Monoidal.μNatIso Y.D _ Y.closed.monoidal
    X.D _ X.closed.monoidal l.edge.left l.monoidal.toMonoidal).symm

/-- Derived sections under scalar adjunction at the tensor unit. This uses the fixed
cycle-normalized comparison, followed by the inverse scalar unit comparison.
Source: Stacks 08JA (blueprint:
lem-coef-derived-sections-normalization-scalar-hom-zero-representative). -/
def coefficientScalarSectionsEquiv (B : X.D) :
    (ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w} Y.J Y.A).obj (l.edge.right.obj B) ≃
      (ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w} X.J X.A).obj B :=
  (coefficientHomZeroUnitEquiv Y.J Y.A Y.closed (l.edge.right.obj B)).toEquiv.trans
    ((l.edge.derivedAdjunction.homEquiv Y.closed.monoidal.tensorUnit B).symm.trans
      ((Iso.homCongr l.unit (Iso.refl B)).trans
        (coefficientHomZeroUnitEquiv X.J X.A X.closed B).toEquiv.symm))

/-- The specified H⁰ scalar-Hom comparison: inverse enriched comparison followed by
scalar adjunction at the unit, with no choice of a new Hom equivalence.
Source: Stacks 07A6 and 08JA (blueprint:
lem-coef-derived-sections-normalization-scalar-hom-zero-representative). -/
def coefficientScalarHomZero (K : Y.D) (N : X.D)
    (x : (ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w} Y.J Y.A).obj
      ((derivedInternalHomOfUniverses.{u, u, u, w} Y.J Y.A).obj
        (op K, l.edge.right.obj N))) :
    (ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w} X.J X.A).obj
      ((derivedInternalHomOfUniverses.{u, u, u, w} X.J X.A).obj
        (op (l.edge.left.obj K), N)) :=
  coefficientScalarSectionsEquiv l _
    ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w} Y.J Y.A).map
      ((ClosedScalarHom.iso Y.closed X.closed l.edge.derivedAdjunction
        (coefficientScalarTensor l)).inv.app (op K, N)) x)

/--
For a K-flat representative of the scalar input and an arbitrary complex
representing the finite input, the normalized representative transpose gives the
H-zero scalar Hom identity.  The remaining transport from arbitrary derived
objects is separate from this representative calculation.

Source: Stacks 03CZ, 079P and 08JA.  Choose the fixed K-injective replacement of
the finite complex, apply the tensor-Hom uncurrying equation from the coefficient
finite tensor normalization, and evaluate the resulting zero cycle using the
fixed representative Hom equivalences.  The ordinary scalar-section formula
identifies the transpose with the finite scalar adjunction.  This theorem is
strictly below the derived-object statement because its first input is a chosen
K-flat complex and both derived inputs are fixed quotient images.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-representative)
-/
theorem coefficientDerivedSectionsScalarHomZero_representative
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (M : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (P' : DerivedCategory (scalarReductionSource l E W))
    (M' : normalizedDVRDerived l E W n)
    (hP' : P' = DerivedCategory.Q.obj P)
    (hM' : M' = DerivedCategory.Q.obj M) :
    ∀ (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj (op P',
        (coefficientFiniteDerivedRestriction l E W n).obj M'))),
      coefficientFiniteHomEquiv l E W n _ _
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
            ((coefficientIntegralSections l E W).map
                (coefficientEnrichedAdjunctionMap R.integralClosed (R.finiteClosed n)
                  (coefficientFiniteDerivedExtension l E W n)
                  (coefficientFiniteAdjunction l E W n) (R.finiteTensor n) P' M') ≫
              (D.scalarSections n).hom.app
                ((coefficientFiniteInternalHom l E W n).obj
                  (op ((coefficientFiniteDerivedExtension l E W n).obj P'), M'))) x) =
        ((coefficientFiniteAdjunction l E W n).homEquiv P' M').symm
          (coefficientIntegralHomEquiv l E W P' _ x) := by
  classical
  subst P'
  subst M'
  intro x
  let N := DerivedCategory.Q.objPreimage
    ((coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))
  let eN := DerivedCategory.Q.objObjPreimageIso
    ((coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))
  obtain ⟨z, hz⟩ := coefficientDerivedSectionsScalarHomZero_cycle_surjective
    l E W P n M N eN x
  change coefficientFiniteHomEquiv l E W n _ _
      (coefficientDerivedSectionsScalarHomZeroMap l E W R D n
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M) x) = _
  exact coefficientDerivedSectionsScalarHomZero_cycle_representative
    l E W R hF D n P hP M N eN z x hz

end WeilConjectures
