# WeilConjectures.IntegralLineReduction: shared data and equivalent power construction

## Reason

Move the data and formula predicates into IntegralLineReductionDefinitions so that
independent ordinary, derived and restriction proof modules can import them without
an import cycle. The item publicly re-exports this module. This separation follows
the mathematical argument, not a compile time limit.

Use the generic scalar tensor powers in power and finitePower. The original
coefficientTwistPower and the generic scalarTensorPower have the same zero, one,
and successor-by-tensor equations but are not definitionally equal in Lean.
Dependent comparison signatures consequently cannot use one for the other without
transports. The two new proved theorems power_eq_coefficient and
finitePower_eq_coefficient establish equality to the original objects for every
integer exponent. Their proofs include zero, one, all positive powers, and internal
duals at negative powers. No hypothesis, conclusion, or mathematical object changes.
Every other moved declaration keeps its original signature and body.

The item theorem signature is unchanged verbatim. Definitions used along the planned
target route have changed bodies, so their interpretation should be reviewed again;
the proved object equalities give the precise preservation check. No Challenge.lean
statement is edited. No adopted WeilConjectures source module is edited.

## Old

In lean/Sheaf/Paper/IntegralLineReductionRestriction.lean, under the same namespace
and parameter context:

```lean
/-- The existing ordinary reduction of a line, at exponent n+1.
Source: Stacks 03EK (blueprint: lem-pur-integral-line-reduction-restriction). -/
abbrev line (L : scalarReductionSource.{u, u} l E X) (n : ℕ) :=
  (scalarReductionExtension.{u, u} l E X n).obj L

/-- The source's signed tensor power, with internal duals at negative exponents.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
abbrev power (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :=
  coefficientTwistLine X (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L m

/-- The same signed power over the finite quotient ring.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
abbrev finitePower (L : scalarReductionSource.{u, u} l E X) (n : ℕ) (m : ℤ) :=
  coefficientTwistLine X (R := integralCoefficientCommRingSheaf.{u, u} l E X n) (line l E X L n) m

/-- Tensor on the right by the signed integral line in the recorded ordinary model.
Source: Stacks 06YU (blueprint: lem-pur-integral-line-reduction-restriction). -/
def ordinary (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    D.{u, u} l E X none ⥤ D.{u, u} l E X none :=
  Prod.sectL (D.{u, u} l E X none) (power l E X L m) ⋙ integralLineOrdinary.{u, u} l E X

/-- Tensor on the right by the signed line in the specified completed model.
Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pur-integral-line-reduction-restriction). -/
def completed (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    D.{u, u} l E X none ⥤ D.{u, u} l E X none :=
  Prod.sectL (D.{u, u} l E X none) (power l E X L m) ⋙ integralLineCompleted.{u, u} l E X

/-- The actual quotient-tower completion comparison, retaining its (c,0) normalization.
Source: Bhatt--Scholze 3.5.2
(blueprint: lem-pur-integral-line-reduction-restriction). -/
def comparison (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    ordinary l E X L m ⟶ completed l E X L m :=
  Functor.whiskerLeft (Prod.sectL (D.{u, u} l E X none) (power l E X L m))
    (integralLineComparison.{u, u} l E X)

/-- The recorded closed derived tensor model specialized to the finite quotient.
Its representative normalization determines the model up to compatible isomorphism.
Source: Stacks 06YN, 07A4 (blueprint: lem-pur-integral-line-reduction-restriction). -/
def finiteModel (n : ℕ) :
    RingedSiteDualityModel.{u + 1, u, u, u + 2}
      (ProEt.topology X) (integralCoefficientCommRingSheaf.{u, u} l E X n) :=
  Classical.choice (ringedSiteDualityMaps_exists
    (ProEt.topology X) (integralCoefficientCommRingSheaf.{u, u} l E X n))

/-- Ordinary finite derived tensor with the finite signed line in degree zero.
Source: Stacks 06YU (blueprint: lem-pur-integral-line-reduction-restriction). -/
def finiteOrdinary (L : scalarReductionSource.{u, u} l E X) (n : ℕ) (m : ℤ) :
    DerivedCategory (scalarReductionTarget.{u, u} l E X n) ⥤
      DerivedCategory (scalarReductionTarget.{u, u} l E X n) :=
  Prod.sectL (DerivedCategory (scalarReductionTarget.{u, u} l E X n))
      ((DerivedCategory.singleFunctor _ 0).obj (finitePower l E X L n m)) ⋙
    (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n)).tensor

/-- The ordinary signed-power reduction comparisons.
Source: Stacks 03EL (blueprint: lem-pur-integral-line-reduction-restriction). -/
abbrev PowerComparisons (L : scalarReductionSource.{u, u} l E X) :=
  ∀ (m : ℤ) (n : ℕ),
    (scalarReductionExtension.{u, u} l E X n).obj (power l E X L m) ≅ finitePower l E X L n m

/-- Unit, first-power, positive balancing and negative dual-evaluation formulas.
The last equation is the dual base-change formula with both quotient scalars.
Source: Stacks 03EL, blueprint proof (3)
(blueprint: lem-pur-integral-line-reduction-restriction). -/
def PowerFormula (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L) : Prop :=
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
      (x : (completedIntegralCommRingSheafUnrestricted.{u, u} l E X).obj.obj U),
    (b 0 n).hom.val.app U (sfReductionTensor.{u} l E X n (power l E X L 0) U a x) =
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n).hom.app U x * a) ∧
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U) (x : L.val.obj U),
    (b 1 n).hom.val.app U (sfReductionTensor.{u} l E X n L U a x) =
      sfReductionTensor.{u} l E X n L U a x) ∧
  (∀ (r n : ℕ) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U) (y : L.val.obj U),
    (b (Int.ofNat (r + 2)) n).hom.val.app U
        (sfReductionTensor.{u} l E X n (power l E X L (Int.ofNat (r + 2))) U a
          (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
            (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U x y)) =
      SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := integralCoefficientCommRingSheaf.{u, u} l E X n) _ _ U
        ((b (Int.ofNat (r + 1)) n).hom.val.app U
          (sfReductionTensor.{u} l E X n (power l E X L (Int.ofNat (r + 1))) U a x))
        (sfReductionTensor.{u} l E X n L U 1 y)) ∧
  ∀ (r n : ℕ) (U : X.ProEtᵒᵖ)
      (a c : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
      (φ : (power l E X L (Int.negSucc r)).val.obj U)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U),
    (((b (Int.negSucc r) n).hom.val.app U
        (sfReductionTensor.{u} l E X n (power l E X L (Int.negSucc r)) U a φ)).app
          (op (Over.mk (𝟙 U.unop))))
        ((b (Int.ofNat (r + 1)) n).hom.val.app U
          (sfReductionTensor.{u} l E X n (power l E X L (Int.ofNat (r + 1))) U c x)) =
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n).hom.app U
        ((φ.app (op (Over.mk (𝟙 U.unop)))) x) * a * c

/-- Finite locally constant reduction models, allowing varying finite modules on the cover.
Source: the hypothesis in blueprint proof (3)
(blueprint: lem-pur-integral-line-reduction-restriction). -/
def FiniteReductions (L : scalarReductionSource.{u, u} l E X) : Prop :=
  ∀ n : ℕ, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X
    (Padic.coefficientExtensionRing l E (n + 1)) (fun M ↦ Finite M)
    (line l E X L n)

/-- Ordinary termwise reduction, before restricting the finite-ring action.
Source: Stacks 06YY (blueprint: lem-pur-integral-line-reduction-restriction). -/
def reduceComplex (n : ℕ) :=
  (scalarReductionExtension.{u, u} l E X n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical universal counit, transported from homotopy complexes to complexes.
Source: Stacks 06YY (blueprint: lem-pur-integral-line-reduction-restriction). -/
def reduceCounit (n : ℕ) :
    DerivedCategory.Q ⋙ scalarReductionDerivedExtension.{u, u} l E X n ⟶
      reduceComplex l E X n ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (scalarReductionDerivedExtension.{u, u} l E X n) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (scalarReductionCounit.{u, u} l E X n) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((scalarReductionExtension.{u, u} l E X n).mapHomotopyCategoryFactors (.up ℤ)).hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso _).hom

/-- Restrict finite coefficient complexes to completed coefficients.
Source: Stacks 03CZ (blueprint: lem-pur-integral-line-reduction-restriction). -/
def restrictComplex (n : ℕ) :=
  (scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The finite tensor representative with the signed finite line in degree zero.
Source: Stacks 06YU (blueprint: lem-pur-integral-line-reduction-restriction). -/
def finiteTensorComplex (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (n : ℕ) (m : ℤ) :=
  (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf.{u, u} l E X n)).obj
      ((reduceComplex l E X n).obj P,
        (HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m))

/-- K-flat computation of finite tensor and the actual derived-reduction counit.
Source: Stacks 06YN, 06YY (blueprint: lem-pur-integral-line-reduction-restriction). -/
def finiteRepresentativeIso (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (n : ℕ) (m : ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
      (integralCoefficientCommRingSheaf.{u, u} l E X n)
      ((reduceComplex l E X n).obj P))
    (hL : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
      (integralCoefficientCommRingSheaf.{u, u} l E X n)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m)))
    (hε : IsIso ((reduceCounit l E X n).app P)) :
    DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj (finiteTensorComplex l E X P L n m) ≅
      (finiteOrdinary l E X L n m).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj
          (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P)) :=
  CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n)
        (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n))
        (RingedSiteDualityModel.models.{u + 1, u, u, u + 2} (finiteModel l E X n))
        ((reduceComplex l E X n).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m)) hP hL ≪≫
      (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n)).tensor.mapIso
        (Iso.prod (@asIso _ _ _ _ ((reduceCounit l E X n).app P) hε).symm (Iso.refl _))

/-- The finite comparison is the balancing map on total-tensor generators.
Source: Stacks 07A4 (blueprint: lem-pur-integral-line-reduction-restriction). -/
def ChainFormula (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (n : ℕ) (m : ℤ)
    (a : (reduceComplex l E X n).obj (integralLineComplex.{u, u} l E X P (power l E X L m)) ≅
      finiteTensorComplex l E X P L n m) : Prop :=
  ∀ (i : ℤ) (U : X.ProEtᵒᵖ)
    (c : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
    (x : (P.X i).val.obj U) (y : (power l E X L m).val.obj U),
    (a.hom.f i).val.app U
      (sfReductionTensor.{u} l E X n
        ((integralLineComplex.{u, u} l E X P (power l E X L m)).X i) U c
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P
          ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) i 0 i (add_zero i) U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n) ((reduceComplex l E X n).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m))
        i 0 i (add_zero i) U (sfReductionTensor.{u} l E X n (P.X i) U c x)
        ((b m n).hom.val.app U (sfReductionTensor.{u} l E X n (power l E X L m) U 1 y))

/-- The derived comparisons are the descents of these balancing maps, with a strict
quotient-transition square on each good representative. Naturality in K is encoded
by natural isomorphisms. The transition on the finite tensor is specified separately
on its generating tensors in TransitionFormula.
Source: Stacks 07A4 (blueprint: lem-pur-integral-line-reduction-restriction). -/
abbrev DerivedComparisons (L : scalarReductionSource.{u, u} l E X) :=
  ∀ (m : ℤ) (n : ℕ), ordinary l E X L m ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
    scalarReductionDerivedExtension.{u, u} l E X n ⋙ finiteOrdinary l E X L n m

/-- Evaluation isomorphisms for opposite signed lines, in the ordinary module category.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
abbrev Evaluations (L : scalarReductionSource.{u, u} l E X) :=
  ∀ m : ℤ,
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L (-m))).obj
        (power l E X L m) ≅ SheafOfModules.unit _

/-- Ordinary evaluation means multiplication at zero and functional evaluation in both
orders for a positive power and its dual. This fixes the maps rather than merely
asserting that the tensor of two lines is isomorphic to the coefficient ring.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
def EvaluationFormula (L : scalarReductionSource.{u, u} l E X) (e : Evaluations l E X L) : Prop :=
  (∀ (U : X.ProEtᵒᵖ)
      (a c : (completedIntegralCommRingSheafUnrestricted.{u, u} l E X).obj.obj U),
    (e 0).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U a c) = a * c) ∧
  (∀ (r : ℕ) (U : X.ProEtᵒᵖ)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U)
      (φ : (power l E X L (Int.negSucc r)).val.obj U),
    (e (Int.ofNat (r + 1))).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U x φ) =
      φ.app (op (Over.mk (𝟙 U.unop))) x) ∧
  ∀ (r : ℕ) (U : X.ProEtᵒᵖ)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U)
      (φ : (power l E X L (Int.negSucc r)).val.obj U),
    (e (Int.negSucc r)).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U φ x) =
      φ.app (op (Over.mk (𝟙 U.unop))) x

/-- The quotient transition on finite signed powers, transported from the actual
ordinary reduction tower by the normalized comparisons.
Source: Stacks 03EL (blueprint: lem-pur-integral-line-reduction-restriction). -/
def powerTransition (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (m : ℤ) (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E X (n + 1)).obj (finitePower l E X L (n + 1) m) ⟶
      (scalarReductionRestriction.{u, u} l E X n).obj (finitePower l E X L n m) :=
  (scalarReductionRestriction.{u, u} l E X (n + 1)).map (b m (n + 1)).inv ≫
    (sfReductionTransition.{u} l E X n).app (power l E X L m) ≫
    (scalarReductionRestriction.{u, u} l E X n).map (b m n).hom

/-- The quotient transition on the target finite tensors acts on both factors by
quotient reduction; the signed-line transition uses the comparisons already fixed.
Source: Stacks 07A4 (blueprint: lem-pur-integral-line-reduction-restriction). -/
def TransitionFormula (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (n : ℕ) (m : ℤ)
    (τ : (restrictComplex l E X (n + 1)).obj (finiteTensorComplex l E X P L (n + 1) m) ⟶
      (restrictComplex l E X n).obj (finiteTensorComplex l E X P L n m)) : Prop :=
  ∀ (i : ℤ) (U : X.ProEtᵒᵖ)
      (x : (((reduceComplex l E X (n + 1)).obj P).X i).val.obj U)
      (y : (finitePower l E X L (n + 1) m).val.obj U),
    (τ.f i).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X (n + 1))
        ((reduceComplex l E X (n + 1)).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L (n + 1) m))
        i 0 i (add_zero i) U x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n) ((reduceComplex l E X n).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m))
        i 0 i (add_zero i) U
        (((((NatTrans.mapHomologicalComplex (sfReductionTransition.{u} l E X n)
          (.up ℤ)).app P).f i).val.app U) x)
        ((powerTransition l E X L b m n).val.app U y)

/-- Simultaneous normalization of the natural derived isomorphisms on every admissible
K-flat representative, and compatibility with the strict quotient transitions.
The hypotheses inside the representative clause only select computations on which the
published model is defined; they are not hypotheses on the objects K of the theorem.
Source: Stacks 06YY, 07A4 (blueprint: lem-pur-integral-line-reduction-restriction). -/
def DerivedFormula (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (d : DerivedComparisons l E X L) : Prop :=
  ∀ (m : ℤ) (P : (Good.{u, u} l E X none).FullSubcategory)
      (hL : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
        ((integralLineSingle.{u, u} l E X).obj (power l E X L m))),
    ∃ a : ∀ n : ℕ,
        (reduceComplex l E X n).obj (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) ≅
          finiteTensorComplex l E X P.obj L n m,
      (∀ n : ℕ, ChainFormula l E X P.obj L b n m (a n)) ∧
      (∀ (n : ℕ)
          (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
            X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
            (integralCoefficientCommRingSheaf.{u, u} l E X n)
            ((reduceComplex l E X n).obj P.obj))
          (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
            X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
            (integralCoefficientCommRingSheaf.{u, u} l E X n)
            ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m)))
          (hε : IsIso ((reduceCounit l E X n).app P.obj)),
        (scalarReductionDerivedExtension.{u, u} l E X n).map
            (integralLineRepresentativeIso.{u, u} l E X P (power l E X L m) hL
              (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj) (Iso.refl _)).inv ≫
          (reduceCounit l E X n).app
            (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) ≫
          DerivedCategory.Q.{u + 2, u + 1, u + 2}.map (a n).hom ≫
          (finiteRepresentativeIso l E X P.obj L n m hP hQ hε).hom =
            (d m n).hom.app (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj)) ∧
      ∀ n : ℕ, ∃ τ :
          (restrictComplex l E X (n + 1)).obj (finiteTensorComplex l E X P.obj L (n + 1) m) ⟶
            (restrictComplex l E X n).obj (finiteTensorComplex l E X P.obj L n m),
        TransitionFormula l E X P.obj L b n m τ ∧
          (restrictComplex l E X (n + 1)).map (a (n + 1)).hom ≫ τ =
            (NatTrans.mapHomologicalComplex (sfReductionTransition.{u} l E X n) (.up ℤ)).app
                (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) ≫
              (restrictComplex l E X n).map (a n).hom

/-- Normalization of an ordinary derived opposite-line evaluation by the actual
ordinary sheaf evaluation, on all K-flat flat-term representatives.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
def DerivedEvaluationFormula (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L k)).obj
        (power l E X L m) ≅ SheafOfModules.unit _)
    (v : ordinary l E X L m ⋙ ordinary l E X L k ≅ 𝟭 (D.{u, u} l E X none)) : Prop :=
  ∀ (P : (Good.{u, u} l E X none).FullSubcategory)
      (hm : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
        ((integralLineSingle.{u, u} l E X).obj (power l E X L m)))
      (hk : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
        ((integralLineSingle.{u, u} l E X).obj (power l E X L k)))
      (hS : Good.{u, u} l E X none (integralLineComplex.{u, u} l E X P.obj (power l E X L m))),
    ∃ γ : integralLineComplex.{u, u} l E X
        (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) (power l E X L k) ≅ P.obj,
      (∀ (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U)
          (y : (power l E X L m).val.obj U) (z : (power l E X L k).val.obj U),
        (γ.hom.f i).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
            (integralLineComplex.{u, u} l E X P.obj (power l E X L m))
            ((integralLineSingle.{u, u} l E X).obj (power l E X L k)) i 0 i (add_zero i) U
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P.obj
              ((integralLineSingle.{u, u} l E X).obj (power l E X L m))
              i 0 i (add_zero i) U x y) z) =
          (e.hom.val.app U
            (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
              (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U y z)) • x) ∧
      (integralLineRepresentativeIso.{u, u} l E X
          ⟨integralLineComplex.{u, u} l E X P.obj (power l E X L m), hS⟩ (power l E X L k) hk
          ((ordinary l E X L m).obj (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj))
          (integralLineRepresentativeIso.{u, u} l E X P (power l E X L m) hm
            (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj) (Iso.refl _))).hom ≫
        v.hom.app (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj) =
          DerivedCategory.Q.{u + 2, u + 1, u + 2}.map γ.hom

/-- The evaluation with the factors reversed, transporting only the equality -(-m)=m.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
def reverseEvaluation (L : scalarReductionSource.{u, u} l E X) (e : Evaluations l E X L) (m : ℤ) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L m)).obj
        (power l E X L (-m)) ≅ SheafOfModules.unit _ :=
  eqToIso (congrArg
    (fun T ↦ (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) T).obj (power l E X L (-m)))
    (congrArg (power l E X L) (neg_neg m)).symm) ≪≫ e (-m)

/-- Restriction of the ordinary inverse equivalences: both underlying functors and
both evaluation maps are identified through the full inclusion.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
def OrdinaryRestriction (L : scalarReductionSource.{u, u} l E X) (m : ℤ)
    (v : ordinary l E X L m ⋙ ordinary l E X L (-m) ≅ 𝟭 (D.{u, u} l E X none))
    (w : ordinary l E X L (-m) ⋙ ordinary l E X L m ≅ 𝟭 (D.{u, u} l E X none)) : Prop :=
  ∃ (F : sfIntegralConstructibleCategory l E X ≌ sfIntegralConstructibleCategory l E X)
      (a : F.functor ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L m)
      (b : F.inverse ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L (-m)),
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.unitIso.inv.app K) =
        b.hom.app (F.functor.obj K) ≫ (ordinary l E X L (-m)).map (a.hom.app K) ≫
          v.hom.app K.obj) ∧
    ∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.counitIso.hom.app K) =
        a.hom.app (F.inverse.obj K) ≫ (ordinary l E X L m).map (b.hom.app K) ≫
          w.hom.app K.obj

/-- Membership of ordinary and completed twists in the integral full subcategory.
Source: Bhatt--Scholze 3.5.2 and blueprint proof (3)
(blueprint: lem-pur-integral-line-reduction-restriction). -/
abbrev PreservesIntegral (L : scalarReductionSource.{u, u} l E X) :=
  ∀ (m : ℤ) (K : sfIntegralConstructibleCategory l E X),
    sfIntegralConstructible l E X ((ordinary l E X L m).obj K.obj) ∧
      sfIntegralConstructible l E X ((completed l E X L m).obj K.obj)

/-- The completed inverse equivalence has the prescribed underlying functors.
Its evaluations are the ordinary ones conjugated by the specified completion
comparisons, in both orders. The equivalence structure includes both triangle identities.
Source: blueprint proof (3) (blueprint: lem-pur-integral-line-reduction-restriction). -/
def CompletedRestriction (L : scalarReductionSource.{u, u} l E X)
    (h : PreservesIntegral l E X L)
    (c : ∀ m : ℤ, (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L m ≅
      (sfIntegralConstructible l E X).ι ⋙ completed l E X L m)
    (m : ℤ)
    (v : ordinary l E X L m ⋙ ordinary l E X L (-m) ≅ 𝟭 (D.{u, u} l E X none))
    (w : ordinary l E X L (-m) ⋙ ordinary l E X L m ≅ 𝟭 (D.{u, u} l E X none)) : Prop :=
  ∃ (F : sfIntegralConstructibleCategory l E X ≌ sfIntegralConstructibleCategory l E X)
      (a : F.functor ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ completed l E X L m)
      (b : F.inverse ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ completed l E X L (-m)),
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.unitIso.inv.app K) =
        b.hom.app (F.functor.obj K) ≫ (completed l E X L (-m)).map (a.hom.app K) ≫
          (c (-m)).inv.app ⟨(completed l E X L m).obj K.obj, (h m K).2⟩ ≫
          (ordinary l E X L (-m)).map ((c m).inv.app K) ≫ v.hom.app K.obj) ∧
    ∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.counitIso.hom.app K) =
        a.hom.app (F.inverse.obj K) ≫ (completed l E X L m).map (b.hom.app K) ≫
          (c m).inv.app ⟨(completed l E X L (-m)).obj K.obj, (h (-m) K).2⟩ ≫
          (ordinary l E X L m).map ((c (-m)).inv.app K) ≫ w.hom.app K.obj

/-- All membership, full-subcategory and inverse-equivalence clauses, with the actual
completion comparison rather than an arbitrary comparison between the two tensor models.
Source: Bhatt--Scholze 3.5.2; blueprint proof (3)
(blueprint: lem-pur-integral-line-reduction-restriction). -/
def Restrictions (L : scalarReductionSource.{u, u} l E X) (e : Evaluations l E X L) : Prop :=
  ∃ (h : PreservesIntegral l E X L)
      (c : ∀ m : ℤ, (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L m ≅
        (sfIntegralConstructible l E X).ι ⋙ completed l E X L m),
    (∀ m : ℤ, (c m).hom =
      Functor.whiskerLeft (sfIntegralConstructible l E X).ι (comparison l E X L m)) ∧
    ∀ m : ℤ,
      ∃ (v : ordinary l E X L m ⋙ ordinary l E X L (-m) ≅ 𝟭 (D.{u, u} l E X none))
        (w : ordinary l E X L (-m) ⋙ ordinary l E X L m ≅ 𝟭 (D.{u, u} l E X none)),
        DerivedEvaluationFormula l E X L m (-m) (e m) v ∧
        DerivedEvaluationFormula l E X L (-m) m (reverseEvaluation l E X L e m) w ∧
        OrdinaryRestriction l E X L m v w ∧ CompletedRestriction l E X L h c m v w
```

## New

In lean/Sheaf/Paper/IntegralLineReductionDefinitions.lean, publicly re-exported by
the original module, under the same namespace and parameter context:

```lean
/-- The existing ordinary reduction of a line, at exponent n+1.
Source: Stacks 03EK (blueprint: def-pur-integral-line-reduction-data). -/
abbrev line (L : scalarReductionSource.{u, u} l E X) (n : ℕ) :=
  (scalarReductionExtension.{u, u} l E X n).obj L

/-- The source's signed tensor power, with internal duals at negative exponents.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
abbrev power (L : scalarReductionSource.{u, u} l E X) :
    ℤ → scalarReductionSource.{u, u} l E X
  | .ofNat n => SheafOfModules.scalarTensorPower.{u + 1, u, u + 1}
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L n
  | .negSucc n => SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
      (SheafOfModules.scalarTensorPower.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L (n + 1))
      (SheafOfModules.unit _)

/-- The same signed power over the finite quotient ring.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
abbrev finitePower (L : scalarReductionSource.{u, u} l E X) (n : ℕ) :
    ℤ → scalarReductionTarget.{u, u} l E X n
  | .ofNat r => SheafOfModules.scalarTensorPower.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf.{u, u} l E X n) (line l E X L n) r
  | .negSucc r => SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
      (SheafOfModules.scalarTensorPower.{u + 1, u, u + 1}
        (integralCoefficientCommRingSheaf.{u, u} l E X n) (line l E X L n) (r + 1))
      (SheafOfModules.unit _)

private theorem scalar_power_eq
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (n : ℕ) :
    SheafOfModules.scalarTensorPower.{u + 1, u, u + 1} R M n =
      coefficientTwistPower.{u} X (R := R) M n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih =>
    simp only [SheafOfModules.scalarTensorPower, coefficientTwistPower, ih]

/-- The generic signed powers equal the original coefficient powers, as objects.
Source: the two recursive definitions
(blueprint: def-pur-integral-line-reduction-data). -/
theorem power_eq_coefficient (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    power l E X L m = coefficientTwistLine X
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) L m := by
  cases m <;> simp only [power, coefficientTwistLine, scalar_power_eq]

/-- The generic finite powers equal the original finite coefficient powers, as objects.
Source: the two recursive definitions
(blueprint: def-pur-integral-line-reduction-data). -/
theorem finitePower_eq_coefficient
    (L : scalarReductionSource.{u, u} l E X) (n : ℕ) (m : ℤ) :
    finitePower l E X L n m = coefficientTwistLine X
      (R := integralCoefficientCommRingSheaf.{u, u} l E X n) (line l E X L n) m := by
  cases m <;> simp only [finitePower, coefficientTwistLine, scalar_power_eq]
  rfl

/-- Tensor on the right by the signed integral line in the recorded ordinary model.
Source: Stacks 06YU (blueprint: def-pur-integral-line-reduction-data). -/
def ordinary (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    D.{u, u} l E X none ⥤ D.{u, u} l E X none :=
  Prod.sectL (D.{u, u} l E X none) (power l E X L m) ⋙ integralLineOrdinary.{u, u} l E X

/-- Tensor on the right by the signed line in the specified completed model.
Source: Bhatt--Scholze 3.4.10
(blueprint: def-pur-integral-line-reduction-data). -/
def completed (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    D.{u, u} l E X none ⥤ D.{u, u} l E X none :=
  Prod.sectL (D.{u, u} l E X none) (power l E X L m) ⋙ integralLineCompleted.{u, u} l E X

/-- The actual quotient-tower completion comparison, retaining its (c,0) normalization.
Source: Bhatt--Scholze 3.5.2
(blueprint: def-pur-integral-line-reduction-data). -/
def comparison (L : scalarReductionSource.{u, u} l E X) (m : ℤ) :
    ordinary l E X L m ⟶ completed l E X L m :=
  Functor.whiskerLeft (Prod.sectL (D.{u, u} l E X none) (power l E X L m))
    (integralLineComparison.{u, u} l E X)

/-- The recorded closed derived tensor model specialized to the finite quotient.
Its representative normalization determines the model up to compatible isomorphism.
Source: Stacks 06YN, 07A4 (blueprint: def-pur-integral-line-reduction-data). -/
def finiteModel (n : ℕ) :
    RingedSiteDualityModel.{u + 1, u, u, u + 2}
      (ProEt.topology X) (integralCoefficientCommRingSheaf.{u, u} l E X n) :=
  Classical.choice (ringedSiteDualityMaps_exists
    (ProEt.topology X) (integralCoefficientCommRingSheaf.{u, u} l E X n))

/-- Ordinary finite derived tensor with the finite signed line in degree zero.
Source: Stacks 06YU (blueprint: def-pur-integral-line-reduction-data). -/
def finiteOrdinary (L : scalarReductionSource.{u, u} l E X) (n : ℕ) (m : ℤ) :
    DerivedCategory (scalarReductionTarget.{u, u} l E X n) ⥤
      DerivedCategory (scalarReductionTarget.{u, u} l E X n) :=
  Prod.sectL (DerivedCategory (scalarReductionTarget.{u, u} l E X n))
      ((DerivedCategory.singleFunctor _ 0).obj (finitePower l E X L n m)) ⋙
    (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n)).tensor

/-- The ordinary signed-power reduction comparisons.
Source: Stacks 03EL (blueprint: def-pur-integral-line-reduction-data). -/
abbrev PowerComparisons (L : scalarReductionSource.{u, u} l E X) :=
  ∀ (m : ℤ) (n : ℕ),
    (scalarReductionExtension.{u, u} l E X n).obj (power l E X L m) ≅ finitePower l E X L n m

/-- Unit, first-power, positive balancing and negative dual-evaluation formulas.
The last equation is the dual base-change formula with both quotient scalars.
Source: Stacks 03EL, blueprint proof (3)
(blueprint: def-pur-integral-line-reduction-data). -/
def PowerFormula (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L) : Prop :=
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
      (x : (completedIntegralCommRingSheafUnrestricted.{u, u} l E X).obj.obj U),
    (b 0 n).hom.val.app U (sfReductionTensor.{u} l E X n (power l E X L 0) U a x) =
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n).hom.app U x * a) ∧
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U) (x : L.val.obj U),
    (b 1 n).hom.val.app U (sfReductionTensor.{u} l E X n L U a x) =
      sfReductionTensor.{u} l E X n L U a x) ∧
  (∀ (r n : ℕ) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U) (y : L.val.obj U),
    (b (Int.ofNat (r + 2)) n).hom.val.app U
        (sfReductionTensor.{u} l E X n (power l E X L (Int.ofNat (r + 2))) U a
          (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
            (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U x y)) =
      SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := integralCoefficientCommRingSheaf.{u, u} l E X n) _ _ U
        ((b (Int.ofNat (r + 1)) n).hom.val.app U
          (sfReductionTensor.{u} l E X n (power l E X L (Int.ofNat (r + 1))) U a x))
        (sfReductionTensor.{u} l E X n L U 1 y)) ∧
  ∀ (r n : ℕ) (U : X.ProEtᵒᵖ)
      (a c : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
      (φ : (power l E X L (Int.negSucc r)).val.obj U)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U),
    (((b (Int.negSucc r) n).hom.val.app U
        (sfReductionTensor.{u} l E X n (power l E X L (Int.negSucc r)) U a φ)).app
          (op (Over.mk (𝟙 U.unop))))
        ((b (Int.ofNat (r + 1)) n).hom.val.app U
          (sfReductionTensor.{u} l E X n (power l E X L (Int.ofNat (r + 1))) U c x)) =
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n).hom.app U
        ((φ.app (op (Over.mk (𝟙 U.unop)))) x) * a * c

/-- Finite locally constant reduction models, allowing varying finite modules on the cover.
Source: the hypothesis in blueprint proof (3)
(blueprint: def-pur-integral-line-reduction-data). -/
def FiniteReductions (L : scalarReductionSource.{u, u} l E X) : Prop :=
  ∀ n : ℕ, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X
    (Padic.coefficientExtensionRing l E (n + 1)) (fun M ↦ Finite M)
    (line l E X L n)

/-- Ordinary termwise reduction, before restricting the finite-ring action.
Source: Stacks 06YY (blueprint: def-pur-integral-line-reduction-data). -/
def reduceComplex (n : ℕ) :=
  (scalarReductionExtension.{u, u} l E X n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical universal counit, transported from homotopy complexes to complexes.
Source: Stacks 06YY (blueprint: def-pur-integral-line-reduction-data). -/
def reduceCounit (n : ℕ) :
    DerivedCategory.Q ⋙ scalarReductionDerivedExtension.{u, u} l E X n ⟶
      reduceComplex l E X n ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (scalarReductionDerivedExtension.{u, u} l E X n) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (scalarReductionCounit.{u, u} l E X n) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((scalarReductionExtension.{u, u} l E X n).mapHomotopyCategoryFactors (.up ℤ)).hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso _).hom

/-- Restrict finite coefficient complexes to completed coefficients.
Source: Stacks 03CZ (blueprint: def-pur-integral-line-reduction-data). -/
def restrictComplex (n : ℕ) :=
  (scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The finite tensor representative with the signed finite line in degree zero.
Source: Stacks 06YU (blueprint: def-pur-integral-line-reduction-data). -/
def finiteTensorComplex (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (n : ℕ) (m : ℤ) :=
  (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf.{u, u} l E X n)).obj
      ((reduceComplex l E X n).obj P,
        (HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m))

/-- K-flat computation of finite tensor and the actual derived-reduction counit.
Source: Stacks 06YN, 06YY (blueprint: def-pur-integral-line-reduction-data). -/
def finiteRepresentativeIso (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (n : ℕ) (m : ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
      (integralCoefficientCommRingSheaf.{u, u} l E X n)
      ((reduceComplex l E X n).obj P))
    (hL : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
      (integralCoefficientCommRingSheaf.{u, u} l E X n)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m)))
    (hε : IsIso ((reduceCounit l E X n).app P)) :
    DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj (finiteTensorComplex l E X P L n m) ≅
      (finiteOrdinary l E X L n m).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj
          (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P)) :=
  CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n)
        (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n))
        (RingedSiteDualityModel.models.{u + 1, u, u, u + 2} (finiteModel l E X n))
        ((reduceComplex l E X n).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m)) hP hL ≪≫
      (RingedSiteDualityModel.closed.{u + 1, u, u, u + 2} (finiteModel l E X n)).tensor.mapIso
        (Iso.prod (@asIso _ _ _ _ ((reduceCounit l E X n).app P) hε).symm (Iso.refl _))

/-- The finite comparison is the balancing map on total-tensor generators.
Source: Stacks 07A4 (blueprint: def-pur-integral-line-reduction-data). -/
def ChainFormula (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (n : ℕ) (m : ℤ)
    (a : (reduceComplex l E X n).obj (integralLineComplex.{u, u} l E X P (power l E X L m)) ≅
      finiteTensorComplex l E X P L n m) : Prop :=
  ∀ (i : ℤ) (U : X.ProEtᵒᵖ)
    (c : (integralCoefficientCommRingSheaf.{u, u} l E X n).obj.obj U)
    (x : (P.X i).val.obj U) (y : (power l E X L m).val.obj U),
    (a.hom.f i).val.app U
      (sfReductionTensor.{u} l E X n
        ((integralLineComplex.{u, u} l E X P (power l E X L m)).X i) U c
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P
          ((integralLineSingle.{u, u} l E X).obj (power l E X L m)) i 0 i (add_zero i) U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n) ((reduceComplex l E X n).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m))
        i 0 i (add_zero i) U (sfReductionTensor.{u} l E X n (P.X i) U c x)
        ((b m n).hom.val.app U (sfReductionTensor.{u} l E X n (power l E X L m) U 1 y))

/-- The derived comparisons are the descents of these balancing maps, with a strict
quotient-transition square on each good representative. Naturality in K is encoded
by natural isomorphisms. The transition on the finite tensor is specified separately
on its generating tensors in TransitionFormula.
Source: Stacks 07A4 (blueprint: def-pur-integral-line-reduction-data). -/
abbrev DerivedComparisons (L : scalarReductionSource.{u, u} l E X) :=
  ∀ (m : ℤ) (n : ℕ), ordinary l E X L m ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
    scalarReductionDerivedExtension.{u, u} l E X n ⋙ finiteOrdinary l E X L n m

/-- Evaluation isomorphisms for opposite signed lines, in the ordinary module category.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
abbrev Evaluations (L : scalarReductionSource.{u, u} l E X) :=
  ∀ m : ℤ,
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L (-m))).obj
        (power l E X L m) ≅ SheafOfModules.unit _

/-- Ordinary evaluation means multiplication at zero and functional evaluation in both
orders for a positive power and its dual. This fixes the maps rather than merely
asserting that the tensor of two lines is isomorphic to the coefficient ring.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
def EvaluationFormula (L : scalarReductionSource.{u, u} l E X) (e : Evaluations l E X L) : Prop :=
  (∀ (U : X.ProEtᵒᵖ)
      (a c : (completedIntegralCommRingSheafUnrestricted.{u, u} l E X).obj.obj U),
    (e 0).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U a c) = a * c) ∧
  (∀ (r : ℕ) (U : X.ProEtᵒᵖ)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U)
      (φ : (power l E X L (Int.negSucc r)).val.obj U),
    (e (Int.ofNat (r + 1))).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U x φ) =
      φ.app (op (Over.mk (𝟙 U.unop))) x) ∧
  ∀ (r : ℕ) (U : X.ProEtᵒᵖ)
      (x : (power l E X L (Int.ofNat (r + 1))).val.obj U)
      (φ : (power l E X L (Int.negSucc r)).val.obj U),
    (e (Int.negSucc r)).hom.val.app U
      (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U φ x) =
      φ.app (op (Over.mk (𝟙 U.unop))) x

/-- The quotient transition on finite signed powers, transported from the actual
ordinary reduction tower by the normalized comparisons.
Source: Stacks 03EL (blueprint: def-pur-integral-line-reduction-data). -/
def powerTransition (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (m : ℤ) (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E X (n + 1)).obj (finitePower l E X L (n + 1) m) ⟶
      (scalarReductionRestriction.{u, u} l E X n).obj (finitePower l E X L n m) :=
  (scalarReductionRestriction.{u, u} l E X (n + 1)).map (b m (n + 1)).inv ≫
    (sfReductionTransition.{u} l E X n).app (power l E X L m) ≫
    (scalarReductionRestriction.{u, u} l E X n).map (b m n).hom

/-- The quotient transition on the target finite tensors acts on both factors by
quotient reduction; the signed-line transition uses the comparisons already fixed.
Source: Stacks 07A4 (blueprint: def-pur-integral-line-reduction-data). -/
def TransitionFormula (P : Cx.{u, u} l E X none) (L : scalarReductionSource.{u, u} l E X)
    (b : PowerComparisons l E X L) (n : ℕ) (m : ℤ)
    (τ : (restrictComplex l E X (n + 1)).obj (finiteTensorComplex l E X P L (n + 1) m) ⟶
      (restrictComplex l E X n).obj (finiteTensorComplex l E X P L n m)) : Prop :=
  ∀ (i : ℤ) (U : X.ProEtᵒᵖ)
      (x : (((reduceComplex l E X (n + 1)).obj P).X i).val.obj U)
      (y : (finitePower l E X L (n + 1) m).val.obj U),
    (τ.f i).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X (n + 1))
        ((reduceComplex l E X (n + 1)).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L (n + 1) m))
        i 0 i (add_zero i) U x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf.{u, u} l E X n) ((reduceComplex l E X n).obj P)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m))
        i 0 i (add_zero i) U
        (((((NatTrans.mapHomologicalComplex (sfReductionTransition.{u} l E X n)
          (.up ℤ)).app P).f i).val.app U) x)
        ((powerTransition l E X L b m n).val.app U y)

/-- Simultaneous normalization of the natural derived isomorphisms on every admissible
K-flat representative, and compatibility with the strict quotient transitions.
The hypotheses inside the representative clause only select computations on which the
published model is defined; they are not hypotheses on the objects K of the theorem.
Source: Stacks 06YY, 07A4 (blueprint: def-pur-integral-line-reduction-data). -/
def DerivedFormula (L : scalarReductionSource.{u, u} l E X) (b : PowerComparisons l E X L)
    (d : DerivedComparisons l E X L) : Prop :=
  ∀ (m : ℤ) (P : (Good.{u, u} l E X none).FullSubcategory)
      (hL : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
        ((integralLineSingle.{u, u} l E X).obj (power l E X L m))),
    ∃ a : ∀ n : ℕ,
        (reduceComplex l E X n).obj (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) ≅
          finiteTensorComplex l E X P.obj L n m,
      (∀ n : ℕ, ChainFormula l E X P.obj L b n m (a n)) ∧
      (∀ (n : ℕ)
          (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
            X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
            (integralCoefficientCommRingSheaf.{u, u} l E X n)
            ((reduceComplex l E X n).obj P.obj))
          (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
            X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
            (integralCoefficientCommRingSheaf.{u, u} l E X n)
            ((HomologicalComplex.single _ (.up ℤ) 0).obj (finitePower l E X L n m)))
          (hε : IsIso ((reduceCounit l E X n).app P.obj)),
        (scalarReductionDerivedExtension.{u, u} l E X n).map
            (integralLineRepresentativeIso.{u, u} l E X P (power l E X L m) hL
              (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj) (Iso.refl _)).inv ≫
          (reduceCounit l E X n).app
            (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) ≫
          DerivedCategory.Q.{u + 2, u + 1, u + 2}.map (a n).hom ≫
          (finiteRepresentativeIso l E X P.obj L n m hP hQ hε).hom =
            (d m n).hom.app (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj)) ∧
      ∀ n : ℕ, ∃ τ :
          (restrictComplex l E X (n + 1)).obj (finiteTensorComplex l E X P.obj L (n + 1) m) ⟶
            (restrictComplex l E X n).obj (finiteTensorComplex l E X P.obj L n m),
        TransitionFormula l E X P.obj L b n m τ ∧
          (restrictComplex l E X (n + 1)).map (a (n + 1)).hom ≫ τ =
            (NatTrans.mapHomologicalComplex (sfReductionTransition.{u} l E X n) (.up ℤ)).app
                (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) ≫
              (restrictComplex l E X n).map (a n).hom

/-- Normalization of an ordinary derived opposite-line evaluation by the actual
ordinary sheaf evaluation, on all K-flat flat-term representatives.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
def DerivedEvaluationFormula (L : scalarReductionSource.{u, u} l E X) (m k : ℤ)
    (e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L k)).obj
        (power l E X L m) ≅ SheafOfModules.unit _)
    (v : ordinary l E X L m ⋙ ordinary l E X L k ≅ 𝟭 (D.{u, u} l E X none)) : Prop :=
  ∀ (P : (Good.{u, u} l E X none).FullSubcategory)
      (hm : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
        ((integralLineSingle.{u, u} l E X).obj (power l E X L m)))
      (hk : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (scalarReductionSiteSmall.{u, u} X) (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
        ((integralLineSingle.{u, u} l E X).obj (power l E X L k)))
      (hS : Good.{u, u} l E X none (integralLineComplex.{u, u} l E X P.obj (power l E X L m))),
    ∃ γ : integralLineComplex.{u, u} l E X
        (integralLineComplex.{u, u} l E X P.obj (power l E X L m)) (power l E X L k) ≅ P.obj,
      (∀ (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U)
          (y : (power l E X L m).val.obj U) (z : (power l E X L k).val.obj U),
        (γ.hom.f i).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
            (integralLineComplex.{u, u} l E X P.obj (power l E X L m))
            ((integralLineSingle.{u, u} l E X).obj (power l E X L k)) i 0 i (add_zero i) U
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P.obj
              ((integralLineSingle.{u, u} l E X).obj (power l E X L m))
              i 0 i (add_zero i) U x y) z) =
          (e.hom.val.app U
            (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
              (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) _ _ U y z)) • x) ∧
      (integralLineRepresentativeIso.{u, u} l E X
          ⟨integralLineComplex.{u, u} l E X P.obj (power l E X L m), hS⟩ (power l E X L k) hk
          ((ordinary l E X L m).obj (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj))
          (integralLineRepresentativeIso.{u, u} l E X P (power l E X L m) hm
            (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj) (Iso.refl _))).hom ≫
        v.hom.app (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj) =
          DerivedCategory.Q.{u + 2, u + 1, u + 2}.map γ.hom

/-- The evaluation with the factors reversed, transporting only the equality -(-m)=m.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
def reverseEvaluation (L : scalarReductionSource.{u, u} l E X) (e : Evaluations l E X L) (m : ℤ) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) (power l E X L m)).obj
        (power l E X L (-m)) ≅ SheafOfModules.unit _ :=
  eqToIso (congrArg
    (fun T ↦ (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) T).obj (power l E X L (-m)))
    (congrArg (power l E X L) (neg_neg m)).symm) ≪≫ e (-m)

/-- Restriction of the ordinary inverse equivalences: both underlying functors and
both evaluation maps are identified through the full inclusion.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
def OrdinaryRestriction (L : scalarReductionSource.{u, u} l E X) (m : ℤ)
    (v : ordinary l E X L m ⋙ ordinary l E X L (-m) ≅ 𝟭 (D.{u, u} l E X none))
    (w : ordinary l E X L (-m) ⋙ ordinary l E X L m ≅ 𝟭 (D.{u, u} l E X none)) : Prop :=
  ∃ (F : sfIntegralConstructibleCategory l E X ≌ sfIntegralConstructibleCategory l E X)
      (a : F.functor ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L m)
      (b : F.inverse ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L (-m)),
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.unitIso.inv.app K) =
        b.hom.app (F.functor.obj K) ≫ (ordinary l E X L (-m)).map (a.hom.app K) ≫
          v.hom.app K.obj) ∧
    ∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.counitIso.hom.app K) =
        a.hom.app (F.inverse.obj K) ≫ (ordinary l E X L m).map (b.hom.app K) ≫
          w.hom.app K.obj

/-- Membership of ordinary and completed twists in the integral full subcategory.
Source: Bhatt--Scholze 3.5.2 and blueprint proof (3)
(blueprint: def-pur-integral-line-reduction-data). -/
abbrev PreservesIntegral (L : scalarReductionSource.{u, u} l E X) :=
  ∀ (m : ℤ) (K : sfIntegralConstructibleCategory l E X),
    sfIntegralConstructible l E X ((ordinary l E X L m).obj K.obj) ∧
      sfIntegralConstructible l E X ((completed l E X L m).obj K.obj)

/-- The completed inverse equivalence has the prescribed underlying functors.
Its evaluations are the ordinary ones conjugated by the specified completion
comparisons, in both orders. The equivalence structure includes both triangle identities.
Source: blueprint proof (3) (blueprint: def-pur-integral-line-reduction-data). -/
def CompletedRestriction (L : scalarReductionSource.{u, u} l E X)
    (h : PreservesIntegral l E X L)
    (c : ∀ m : ℤ, (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L m ≅
      (sfIntegralConstructible l E X).ι ⋙ completed l E X L m)
    (m : ℤ)
    (v : ordinary l E X L m ⋙ ordinary l E X L (-m) ≅ 𝟭 (D.{u, u} l E X none))
    (w : ordinary l E X L (-m) ⋙ ordinary l E X L m ≅ 𝟭 (D.{u, u} l E X none)) : Prop :=
  ∃ (F : sfIntegralConstructibleCategory l E X ≌ sfIntegralConstructibleCategory l E X)
      (a : F.functor ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ completed l E X L m)
      (b : F.inverse ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ completed l E X L (-m)),
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.unitIso.inv.app K) =
        b.hom.app (F.functor.obj K) ≫ (completed l E X L (-m)).map (a.hom.app K) ≫
          (c (-m)).inv.app ⟨(completed l E X L m).obj K.obj, (h m K).2⟩ ≫
          (ordinary l E X L (-m)).map ((c m).inv.app K) ≫ v.hom.app K.obj) ∧
    ∀ K : sfIntegralConstructibleCategory l E X,
      (sfIntegralConstructible l E X).ι.map (F.counitIso.hom.app K) =
        a.hom.app (F.inverse.obj K) ≫ (completed l E X L m).map (b.hom.app K) ≫
          (c m).inv.app ⟨(completed l E X L (-m)).obj K.obj, (h (-m) K).2⟩ ≫
          (ordinary l E X L m).map ((c (-m)).inv.app K) ≫ w.hom.app K.obj

/-- All membership, full-subcategory and inverse-equivalence clauses, with the actual
completion comparison rather than an arbitrary comparison between the two tensor models.
Source: Bhatt--Scholze 3.5.2; blueprint proof (3)
(blueprint: def-pur-integral-line-reduction-data). -/
def Restrictions (L : scalarReductionSource.{u, u} l E X) (e : Evaluations l E X L) : Prop :=
  ∃ (h : PreservesIntegral l E X L)
      (c : ∀ m : ℤ, (sfIntegralConstructible l E X).ι ⋙ ordinary l E X L m ≅
        (sfIntegralConstructible l E X).ι ⋙ completed l E X L m),
    (∀ m : ℤ, (c m).hom =
      Functor.whiskerLeft (sfIntegralConstructible l E X).ι (comparison l E X L m)) ∧
    ∀ m : ℤ,
      ∃ (v : ordinary l E X L m ⋙ ordinary l E X L (-m) ≅ 𝟭 (D.{u, u} l E X none))
        (w : ordinary l E X L (-m) ⋙ ordinary l E X L m ≅ 𝟭 (D.{u, u} l E X none)),
        DerivedEvaluationFormula l E X L m (-m) (e m) v ∧
        DerivedEvaluationFormula l E X L (-m) m (reverseEvaluation l E X L e m) w ∧
        OrdinaryRestriction l E X L m v w ∧ CompletedRestriction l E X L h c m v w
```

## Users

The repository downstream scan lists no Lean importer of the original module.
Its unfinished DAG parents still need it; none is withdrawn. The following modules
are in this delivery and use the shared definitions:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralLineReductionRestriction | J8 | Re-export shared data and assemble the separate proof parts. |
| Sheaf.Paper.IntegralLineReductionDefinitions | J8, new | Move data; generic powers with proved equality to original powers. |
| Sheaf.Paper.IntegralLinePowerComparisons | J8, new | Use generic power comparison and prove evaluation formulas. |
| Sheaf.Paper.IntegralLineDerivedComparisons | J8, new | State normalized derived reduction and support obligation. |
| Sheaf.Paper.IntegralLineRestrictions | J8, new | State completeness and normalized restriction obligation. |

No module held by another group is adapted. Public definition names and their
mathematical interpretations are preserved. Only the two power abbreviations change
construction; the remaining bodies are copied from the original file.

## Status

landed 20261021T152321-L-1870640 2026-10-21 (merge of deliver/J8/Sheaf.Paper.IntegralLineReductionRestriction)
