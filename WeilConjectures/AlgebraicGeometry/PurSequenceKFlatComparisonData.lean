/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurSequenceAdjointResolutionData
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Data for quotient-sequence K-flat comparisons and coherent shifts

Source: Stacks, sites-cohomology.tex, Tags 06YY, 06YS and 0G7D; homology.tex,
Tag 012Z; blueprint `sec-six-functors/sk-thm-sf-compatibility/`
`fix-prop-coherence.proof.md`, coefficient-comparison paragraph
(blueprint: def-pur-sequence-kflat-comparison-data).

The index `n : ℕ` denotes exponent `n + 1`. All models live in the ordinary
unbounded derived category of the actual strict quotient systems.

## Main definitions

- `PurSequenceKFlatComparison`: the universal, representative-normalized comparison.
- `PurSequenceKFlatResolutionComparison`: its maps and three-resolution identities.
- `PurSequenceKFlatShiftComparison`: its prescribed coherent shift squares.
- `purSequenceTensorRight`: the existing total tensor with its first input fixed.
- `PurSequenceTensorShiftFormula`: the second-factor shift sign on tensor generators.

The existence theorem is in `PurSequenceKFlatComparisonShifts`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientFiniteReductionModel purSequenceShiftIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The universal left-derived pair and its comparison with the supplied reduction.
The representative equation uses the actual strict pullback complex and the recorded
finite comparisons and quotient transitions, through `CoefficientReductionPresentation`.
Source: Stacks 06YY, 06YS, 0G7D
(blueprint: def-pur-sequence-kflat-comparison-data). -/
structure PurSequenceKFlatComparison
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W) where
  L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W
  ε : DerivedCategory.Q ⋙ L ⟶
    O.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : L.IsLeftDerivedFunctor ε
    (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
  α : L ≅ S.reduction
  reductionCounit : DerivedCategory.Q ⋙ S.reduction ⟶
    O.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  comparison : ε = Functor.whiskerLeft DerivedCategory.Q α.hom ≫ reductionCounit
  reductionUniversal : S.reduction.IsLeftDerivedFunctor reductionCounit
    (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
  representative : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)) →
    ∃ e : S.reduction.obj (DerivedCategory.Q.obj Q) ≅
        DerivedCategory.Q.obj ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q),
      reductionCounit.app Q = e.hom ∧
      CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction Q hQ
        ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q) e
        (fun n ↦ (NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).app Q)
  unique : ∀ β : L ≅ S.reduction,
    ε = Functor.whiskerLeft DerivedCategory.Q β.hom ≫ reductionCounit → β = α

/-- The two canonical comparisons on every supplied resolution, together with naturality
for maps of resolutions and their cocycle for three resolutions of the same input.
No independent finite resolutions or transition maps are chosen.
Source: Stacks 06YY, 06YT, 0G7D
(blueprint: def-pur-sequence-kflat-comparison-data). -/
structure PurSequenceKFlatResolutionComparison
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (A : PurSequenceKFlatComparison l E W S O) where
  pullback : ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) [QuasiIso q]
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (_flatQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)),
    A.L.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q)
  reduction : ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) [QuasiIso q]
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (_flatQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)),
    S.reduction.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q)
  pullback_formula : ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) [QuasiIso q] (hQ) (flatQ),
    (pullback P Q q hQ flatQ).hom = inv (A.L.map (DerivedCategory.Q.map q)) ≫ A.ε.app Q
  reduction_formula : ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) [QuasiIso q] (hQ) (flatQ),
    (reduction P Q q hQ flatQ).hom =
      inv (S.reduction.map (DerivedCategory.Q.map q)) ≫ A.reductionCounit.app Q
  comparison : ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) [QuasiIso q] (hQ) (flatQ),
    pullback P Q q hQ flatQ = A.α.app (DerivedCategory.Q.obj P) ≪≫ reduction P Q q hQ flatQ
  maps : ∀ (P P' Q Q' : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) (q' : Q' ⟶ P') [QuasiIso q] [QuasiIso q']
    (hQ) (flatQ) (hQ') (flatQ') (v : Q ⟶ Q') (h : P ⟶ P') (_sq : v ≫ q' = q ≫ h),
    (pullback P Q q hQ flatQ).hom ≫ DerivedCategory.Q.map
        ((O.pullback.mapHomologicalComplex (.up ℤ)).map v) =
      A.L.map (DerivedCategory.Q.map h) ≫ (pullback P' Q' q' hQ' flatQ').hom ∧
    (reduction P Q q hQ flatQ).hom ≫ DerivedCategory.Q.map
        ((O.pullback.mapHomologicalComplex (.up ℤ)).map v) =
      S.reduction.map (DerivedCategory.Q.map h) ≫ (reduction P' Q' q' hQ' flatQ').hom
  finite_evaluation : ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) [QuasiIso q] (hQ) (flatQ) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map (reduction P Q q hQ flatQ).hom ≫
      (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
        ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).hom.app Q) =
    (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
      inv ((coefficientFiniteDerivedExtension l E W n).map (DerivedCategory.Q.map q)) ≫
      (coefficientFiniteReductionModel l E W Q hQ n).hom
  same_comparison : ∀ (P Q Q' : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) (q' : Q' ⟶ P) [QuasiIso q] [QuasiIso q']
    (hQ) (flatQ) (hQ') (flatQ'),
    (pullback P Q q hQ flatQ).symm ≪≫ pullback P Q' q' hQ' flatQ' =
      (reduction P Q q hQ flatQ).symm ≪≫ reduction P Q' q' hQ' flatQ'
  three : ∀ (P Q Q' Q'' : CochainComplex (scalarReductionSource l E W) ℤ)
    (q : Q ⟶ P) (q' : Q' ⟶ P) (q'' : Q'' ⟶ P)
    [QuasiIso q] [QuasiIso q'] [QuasiIso q'']
    (hQ) (flatQ) (hQ') (flatQ') (hQ'') (flatQ''),
    ((pullback P Q q hQ flatQ).symm ≪≫ pullback P Q' q' hQ' flatQ') ≪≫
        ((pullback P Q' q' hQ' flatQ').symm ≪≫ pullback P Q'' q'' hQ'' flatQ'') =
      (pullback P Q q hQ flatQ).symm ≪≫ pullback P Q'' q'' hQ'' flatQ''

/-- The existing direct-sum tensor total, as a functor in its second variable.
Source: Stacks 012Z, 06YN (blueprint: def-pur-sequence-kflat-comparison-data). -/
def purSequenceTensorRight (T : CochainComplex (scalarReductionSource l E W) ℤ) :
    CochainComplex (scalarReductionSource l E W) ℤ ⥤
      CochainComplex (scalarReductionSource l E W) ℤ :=
  (Functor.curry.obj (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W))).obj T

/-- The canonical reindexing of sections under the cochain shift.
Source: cochain shifts, Stacks 0A8D
(blueprint: def-pur-sequence-kflat-comparison-data). -/
def purSequenceShiftSection (K : CochainComplex (scalarReductionSource l E W) ℤ)
    (r i : ℤ) (V : W.ProEtᵒᵖ) (x : (K.X (i + r)).val.obj V) :
    ((K⟦r⟧).X i).val.obj V :=
  ((CochainComplex.shiftFunctorObjXIso K r i (i + r) rfl).inv).val.app V x

/-- The second-factor tensor shift is (-1)^(r*p) on the (p,q) summand.
The `CommShift` parameter includes naturality in Q and zero/addition coherence,
and therefore inverse-shift coherence. The formula uses the actual pure-tensor
summand inclusions of the unbounded direct-sum total.
Source: Stacks 012Z, explicit cochain differential calculation
(blueprint: def-pur-sequence-kflat-comparison-data). -/
def PurSequenceTensorShiftFormula
    (T : CochainComplex (scalarReductionSource l E W) ℤ)
    (s : (purSequenceTensorRight l E W T).CommShift ℤ) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r p q k : ℤ) (hpq : p + q = k)
    (V : W.ProEtᵒᵖ) (x : (T.X p).val.obj V) (y : (Q.X (q + r)).val.obj V),
    (((purSequenceShiftIso (purSequenceTensorRight l E W T) s r).hom.app Q).f k).val.app V
      (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) T (Q⟦r⟧) p q k hpq V x
        (purSequenceShiftSection l E W Q r q V y)) =
    (r * p).negOnePow • purSequenceShiftSection l E W
      ((purSequenceTensorRight l E W T).obj Q) r k V
        (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) T Q p (q + r) (k + r)
          (by omega) V x y)

/-- The specified pullback and finite scalar-extension shifts, identity on reindexed
terms, with the comparison square on every derived input. `CommShift` includes
zero and addition; setting s = -r supplies the inverse equations.
Source: Stacks 06YY and the cochain shift convention
(blueprint: def-pur-sequence-kflat-comparison-data). -/
structure PurSequenceKFlatShiftComparison
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (A : PurSequenceKFlatComparison l E W S O) where
  left_shift : A.L.CommShift ℤ
  reduction_shift : S.reduction.CommShift ℤ
  finite_shift : ∀ n : ℕ, (coefficientFiniteDerivedExtension l E W n).CommShift ℤ
  comparison : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (r : ℤ),
    (purSequenceShiftIso A.L left_shift r).hom.app P ≫ (A.α.hom.app P)⟦r⟧' =
      A.α.hom.app (P⟦r⟧) ≫ (purSequenceShiftIso S.reduction reduction_shift r).hom.app P
  left_resolution : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ),
    A.L.map ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
      (purSequenceShiftIso A.L left_shift r).hom.app (DerivedCategory.Q.obj Q) ≫
      (A.ε.app Q)⟦r⟧' =
    A.ε.app (Q⟦r⟧) ≫ DerivedCategory.Q.map
      (((O.pullback.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app Q) ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q)
  left_terms : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r i : ℤ),
    HEq ((((O.pullback.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app Q).f i)
      (𝟙 (O.pullback.obj (Q.X (i + r))))
  finite_terms : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r i : ℤ),
    HEq ((((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).commShiftIso r
      |>.hom.app Q).f i) (𝟙 ((scalarReductionExtension l E W n).obj (Q.X (i + r))))
  left_differential : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r i : ℤ),
    HEq (((O.pullback.mapHomologicalComplex (.up ℤ)).obj (Q⟦r⟧)).d i (i + 1))
      (r.negOnePow • O.pullback.map (Q.d (i + r) (i + 1 + r)))
  finite_differential : ∀ (n : ℕ)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r i : ℤ),
    HEq ((((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
      (Q⟦r⟧)).d i (i + 1))
      (r.negOnePow • (scalarReductionExtension l E W n).map (Q.d (i + r) (i + 1 + r)))
  quotient_shifts : ∀ (m n : ℕ) (h : n ≤ m)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ),
    (((scalarReductionExtension l E W m).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
        Q ≫ ((NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h)
          (.up ℤ)).app Q)⟦r⟧' =
      (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app
          (Q⟦r⟧) ≫
        ((((scalarReductionExtension l E W n ⋙ normalizedDVRModuleRes l E W h)
          |>.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app Q)
  finite_resolution : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (r : ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (hQr : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q⟦r⟧)),
    (coefficientFiniteDerivedExtension l E W n).map
        ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
      (purSequenceShiftIso (coefficientFiniteDerivedExtension l E W n)
        (finite_shift n) r).hom.app (DerivedCategory.Q.obj Q) ≫
      (coefficientFiniteReductionModel l E W Q hQ n).hom⟦r⟧' =
    (coefficientFiniteReductionModel l E W (Q⟦r⟧) hQr n).hom ≫
      DerivedCategory.Q.map
        ((((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
          Q) ≫ (DerivedCategory.Q.commShiftIso r).hom.app
            (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
  finite_evaluation : ∀ (n : ℕ) (P : DerivedCategory (scalarReductionSource l E W)) (r : ℤ),
    (S.reductionEvaluation n).hom.app (P⟦r⟧) ≫
      (purSequenceShiftIso (coefficientFiniteDerivedExtension l E W n)
        (finite_shift n) r).hom.app P =
    (coefficientSequenceDerivedEvaluation l E W n).map
      ((purSequenceShiftIso S.reduction reduction_shift r).hom.app P) ≫
      ((coefficientSequenceDerivedEvaluation l E W n).commShiftIso r).hom.app
        (S.reduction.obj P) ≫ ((S.reductionEvaluation n).hom.app P)⟦r⟧'

end WeilConjectures
