# WeilConjectures.IntegralVerdier models

## Reason

Move the model definitions out of the theorem module so finite-level geometric
and coefficient-compatibility lemmas can refer to them without importing the theorem
they prove. The original module publicly imports the new model module, preserving the
full existing public interface. No target or definition changes meaning.

## Old

Location: lean/Sheaf/SixFunctors/IntegralVerdier.lean. The declaration block is verbatim:

```lean
structure SignedSymmetry (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) where
  swap : ∀ K L : IntegralHom.Derived.{u, u} X R,
    a.tensor.obj (K, L) ≅ a.tensor.obj (L, K)
  representative : ∀ (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : IntegralHom.flat.{u, u} X R P) (hQ : IntegralHom.flat.{u, u} X R Q),
    ∃ s : ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ⟶
        ((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P,
      (∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) =
          (i * j).negOnePow •
            (eqToHom (congrArg
              (fun k : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P).X k)
                (add_comm j i))).val.app U
                  (IntegralHom.totalPair.{u, u} X R Q P j i U y x)) ∧
      a.representative.inv.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫ DerivedCategory.Q.map s ≫
        a.representative.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) =
          (swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The unchanged completed-coefficient derived category.
Source: blueprint order 2146 (blueprint: thm-coef-integral-verdier). -/
abbrev Ambient := DerivedCategory (scalarReductionSource.{u, u} l E X)

/-- Ambient Verdier duality is RHom into the supplied integral dualizing object.
Source: blueprint order 2146, first display (blueprint: thm-coef-integral-verdier). -/
def dual (ω : Ambient l E X) : (Ambient l E X)ᵒᵖ ⥤ Ambient l E X :=
  (Functor.curry.obj (IntegralHom.hom.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X))).flip.obj ω

/-- The actual finite dual with the specified finite dualizing object.
Source: blueprint order 2146, finite dual (blueprint: thm-coef-integral-verdier). -/
def finiteDual (n : ℕ) (ω : DerivedCategory (scalarReductionTarget l E X n)) :
    (DerivedCategory (scalarReductionTarget l E X n))ᵒᵖ ⥤
      DerivedCategory (scalarReductionTarget l E X n) :=
  (Functor.curry.obj (IntegralHom.hom.{u, u} X
    (integralCoefficientCommRingSheaf l E X n))).flip.obj ω

/-- The double-dual map is the transpose of evaluation with its factors interchanged.
The symmetry is the signed representative symmetry above.
Source: blueprint order 2146, proof step 5; Stacks 08J9
(blueprint: thm-coef-integral-verdier). -/
def delta {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R) (s : SignedSymmetry X R a)
    (ω K : IntegralHom.Derived.{u, u} X R) :
    K ⟶ (IntegralHom.hom.{u, u} X R).obj
      (op ((IntegralHom.hom.{u, u} X R).obj (op K, ω)), ω) :=
  restrictionDualDelta (Functor.curry.obj a.tensor)
    (Functor.curry.obj (IntegralHom.hom.{u, u} X R)) a.adjunction s.swap ω K

/-- Restriction of the actual dual functor, using the preservation clause as a proof.
Source: blueprint order 2146, anti-equivalence (blueprint: thm-coef-integral-verdier). -/
def restrictedDual (ω : Ambient l E X)
    (h : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E X ((dual l E X ω).obj (op K.obj))) :
    (sfIntegralConstructibleCategory l E X)ᵒᵖ ⥤ sfIntegralConstructibleCategory l E X :=
  ObjectProperty.lift (sfIntegralConstructible l E X)
    ((sfIntegralConstructible l E X).ι.op ⋙ dual l E X ω) (fun K ↦ h K.unop)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The evaluation-defined comparison, followed by the specified dualizing reduction.
Source: blueprint order 2146, first comparison; lem-coef-integral-hom-reduction
(blueprint: thm-coef-integral-verdier). -/
def comparison
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    {n : ℕ} (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) (K : Ambient l E X) :
    (scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K)) ⟶
      (finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
        (op ((scalarReductionDerivedExtension l E X n).obj K)) :=
  IntegralHom.comparison.{u, u, u} l E X D hl m K ω.obj ≫
    (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
      (Prod.mkHom (𝟙 (op ((scalarReductionDerivedExtension l E X n).obj K)))
        (r n).hom)

/-- The finite dual terms in one ambient category, using actual restriction of scalars.
Source: blueprint order 2146, second display (blueprint: thm-coef-integral-verdier). -/
def finiteTerms (K : Ambient l E X) (n : ℕ) : Ambient l E X :=
  (scalarReductionDerivedRestriction l E X n).obj
    ((finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
      (op ((scalarReductionDerivedExtension l E X n).obj K)))

/-- Restrict the evaluation-defined comparison, using its asserted invertibility.
Source: blueprint order 2146, reconstruction (blueprint: thm-coef-integral-verdier). -/
def restrictedComparison
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    (sfDerivedReductionRestricted l E X n).obj ((dual l E X ω.obj).obj (op K)) ≅
      finiteTerms l E X D K n :=
  (scalarReductionDerivedRestriction l E X n).mapIso
    (@asIso _ _ _ _ (comparison l E X D hl (m n) ω r K) (h n))

/-- The finite-dual transition in the completed-coefficient category. This is the
comparison transport of the actual quotient transition, not a chosen tower on the
same objects. The evaluation and transpose equations of the theorem identify it
with the transition induced by finite evaluation and dualizing reduction.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def finiteTransition
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    finiteTerms l E X D K (n + 1) ⟶ finiteTerms l E X D K n :=
  (restrictedComparison l E X D hl m ω r K h (n + 1)).inv ≫
    (sfDerivedReductionTransition l E X n).app ((dual l E X ω.obj).obj (op K)) ≫
      (restrictedComparison l E X D hl m ω r K h n).hom

/-- The specified reduction leg to the finite dual.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def finiteLeg
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    (dual l E X ω.obj).obj (op K) ⟶ finiteTerms l E X D K n :=
  (sfDerivedReductionUnit l E X n).app ((dual l E X ω.obj).obj (op K)) ≫
    (restrictedComparison l E X D hl m ω r K h n).hom

/-- Finite evaluation, adjointed back to completed coefficients. This explicitly
uses reduction of K and the reduction/restriction counit, so it is finite evaluation
with its input reduced, rather than an evaluation on an unrelated ambient object.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def finiteEvaluation
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (K : Ambient l E X) (n : ℕ) :
    a.tensor.obj (K, finiteTerms l E X D K n) ⟶
      (scalarReductionDerivedRestriction l E X n).obj
        (integralDualizingFiniteTerm l E D X n) :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _
    ((m n).mu.hom.app (K, finiteTerms l E X D K n) ≫
      (m n).target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K))
          ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.counit.app
            ((finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
              (op ((scalarReductionDerivedExtension l E X n).obj K))))) ≫
      ((m n).target.adjunction ((scalarReductionDerivedExtension l E X n).obj K)).counit.app
        (integralDualizingFiniteTerm l E D X n))

/-- The specified finite dualizing transition transported through its reductions.
Source: blueprint order 2146, proof step 4 (blueprint: thm-coef-integral-verdier). -/
def dualizingTransition (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) (n : ℕ) :
    (scalarReductionDerivedRestriction l E X (n + 1)).obj
        (integralDualizingFiniteTerm l E D X (n + 1)) ⟶
      (scalarReductionDerivedRestriction l E X n).obj (integralDualizingFiniteTerm l E D X n) :=
  ((scalarReductionDerivedRestriction l E X (n + 1)).mapIso (r (n + 1))).inv ≫
    (sfDerivedReductionTransition l E X n).app ω.obj ≫
      ((scalarReductionDerivedRestriction l E X n).mapIso (r n)).hom

/-- Every clause of integral Verdier duality for the ambient internal Hom.
Tensor presentations and signed symmetries are supplied as part of the conclusion;
their representative normalizations fix evaluation and its transposes.
Source: blueprint order 2146 (blueprint: thm-coef-integral-verdier). -/
def Conclusion (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) : Prop :=
  ∃ (tensor : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheaf l E X D hl)),
  ∃ (symmetry : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) tensor),
  ∃ (reduction : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl tensor n),
  ∃ (finiteSymmetry : ∀ n : ℕ,
    SignedSymmetry X (integralCoefficientCommRingSheaf l E X n) (reduction n).target),
  ∃ (_categories_equal : sfIntegralConstructible l E X = finiteTorConstructibleIntegral l E X),
  ∃ (preservation : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E X ((dual l E X ω.obj).obj (op K.obj))),
  ∃ (_anti_equivalence : (restrictedDual l E X ω.obj preservation).IsEquivalence),
  ∃ (_exact : ∃ s : (dual l E X ω.obj).CommShift ℤ,
    ∀ T : CategoryTheory.Pretriangulated.Triangle (Ambient l E X)ᵒᵖ,
      sfIntegralConstructible l E X T.obj₁.unop →
      sfIntegralConstructible l E X T.obj₂.unop →
      sfIntegralConstructible l E X T.obj₃.unop →
      T ∈ distTriang (Ambient l E X)ᵒᵖ →
      CategoryTheory.Pretriangulated.Triangle.mk
        ((dual l E X ω.obj).map T.mor₁) ((dual l E X ω.obj).map T.mor₂)
        ((dual l E X ω.obj).map T.mor₃ ≫
          (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
        distTriang (Ambient l E X)),
  ∃ (comparisons : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    IsIso (comparison l E X D hl (reduction n) ω r K.obj)),
  ∃ (_evaluation : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (reduction n).target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K.obj))
          (comparison l E X D hl (reduction n) ω r K.obj)) ≫
      ((reduction n).target.adjunction
        ((scalarReductionDerivedExtension l E X n).obj K.obj)).counit.app
          (integralDualizingFiniteTerm l E D X n) =
    (reduction n).mu.inv.app (K.obj, (dual l E X ω.obj).obj (op K.obj)) ≫
      (scalarReductionDerivedExtension l E X n).map
        ((tensor.adjunction K.obj).counit.app ω.obj) ≫
          (r n).hom),
  ∃ (_transposes : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ)
    (V : Ambient l E X) (f : V ⟶ (dual l E X ω.obj).obj (op K.obj)),
    ((reduction n).target.adjunction
      ((scalarReductionDerivedExtension l E X n).obj K.obj)).homEquiv
        ((scalarReductionDerivedExtension l E X n).obj V)
        (integralDualizingFiniteTerm l E D X n)
        ((reduction n).mu.inv.app (K.obj, V) ≫
          (scalarReductionDerivedExtension l E X n).map
            (((tensor.adjunction K.obj).homEquiv V ω.obj).symm f) ≫
              (r n).hom) =
      (scalarReductionDerivedExtension l E X n).map f ≫
        comparison l E X D hl (reduction n) ω r K.obj),
  ∃ (_transition_evaluation : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    tensor.tensor.map (Prod.mkHom (𝟙 K.obj)
        (finiteTransition l E X D hl reduction ω r K.obj (comparisons K) n)) ≫
      finiteEvaluation l E X D hl reduction K.obj n =
    finiteEvaluation l E X D hl reduction K.obj (n + 1) ≫
      dualizingTransition l E X D ω r n),
  ∃ (_reconstruction : ∀ K : sfIntegralConstructibleCategory l E X,
    ∃ hprod : HasProduct (fun n : ℕ ↦ finiteTerms l E X D K.obj n),
      (fun [_productInst : HasProduct (fun n : ℕ ↦ finiteTerms l E X D K.obj n)] ↦
        ∃ δ : (∏ᶜ fun n : ℕ ↦ finiteTerms l E X D K.obj n) ⟶
            ((dual l E X ω.obj).obj (op K.obj))⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle
            (finiteTransition l E X D hl reduction ω r K.obj (comparisons K))
            ((dual l E X ω.obj).obj (op K.obj))
            (Pi.lift (finiteLeg l E X D hl reduction ω r K.obj (comparisons K))) δ)
        (_productInst := hprod)),
  ∃ (_tor_bound : ∀ (K : sfIntegralConstructibleCategory l E X) (d : ℕ),
    topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ, a ≤ b →
    (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj K.obj) a b) →
    ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K.obj)))
        (-b - 2 * (d : ℤ)) (-a)),
  ∃ (_reduction_delta : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E X n).map
        (delta X tensor symmetry ω.obj K.obj) ≫
      comparison l E X D hl (reduction n) ω r
        ((dual l E X ω.obj).obj (op K.obj)) ≫
      (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
        (Prod.mkHom
          ((@asIso _ _ _ _
            (comparison l E X D hl (reduction n) ω r K.obj) (comparisons K n)).inv.op)
          (𝟙 (integralDualizingFiniteTerm l E D X n))) =
      delta X (reduction n).target (finiteSymmetry n) (integralDualizingFiniteTerm l E D X n)
        ((scalarReductionDerivedExtension l E X n).obj K.obj)),
  ∃ (_biduality : ∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (delta X tensor symmetry ω.obj K.obj)),
  ∀ (K L : sfIntegralConstructibleCategory l E X) (f : K ⟶ L),
    f.hom ≫ delta X tensor symmetry ω.obj L.obj =
      delta X tensor symmetry ω.obj K.obj ≫
        (dual l E X ω.obj).map ((dual l E X ω.obj).map f.hom.op).op

```

## New

The declaration block above, with identical signatures, is located at
lean/Sheaf/SixFunctors/IntegralVerdierModels.lean. In the original module it is reexported by:

```lean
public import Sheaf.SixFunctors.IntegralVerdierModels
```

The blueprint tags in model docstrings now name their precise owner nodes.
All original public imports remain public imports of the model module. Every signature,
implicit parameter, universe and visibility is unchanged. Thirteen bodies are verbatim.
The body of comparison expands the original IntegralHom.comparison and uses the
scalarReductionDerivedExtension wrapper consistently:

```lean
  (m.target.adjunction ((scalarReductionDerivedExtension l E X n).obj K)).homEquiv
    ((scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K)))
    ((scalarReductionDerivedExtension l E X n).obj ω.obj)
    (m.mu.inv.app (K, (dual l E X ω.obj).obj (op K)) ≫
      (scalarReductionDerivedExtension l E X n).map ((a.adjunction K).counit.app ω.obj)) ≫
    (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
      (Prod.mkHom (𝟙 (op ((scalarReductionDerivedExtension l E X n).obj K)))
        (r n).hom)
```

The integralDerivedReduction and scalarReductionDerivedExtension wrappers reduce to
the same derived-change-of-rings construction. Thus this is the identical evaluation
transpose, with the same morphism and coefficient projection. It avoids repeated
unfolding of chosen derived models when proving evaluation compatibility. No downstream
module requires a source adaptation. Targets using these definitions retain their
exact previous meaning; the independent review checks this definitional identification.

## Users

The following is the complete transitive consumer list from tools/downstream.py, with
the item included. Its --uses checks were also run on all fourteen moved declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.FiniteTorStability | E5 | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.PointTraceReconstruction | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | S4 | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Y3 | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | H7 | Same public definitions by reexport; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | D2 | Same public definitions by reexport; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public definitions by reexport; no adaptation. |

## Status

landed 20261025T043424-L-1751131 2026-10-25 (merge of deliver/Y3/Sheaf.SixFunctors.IntegralVerdier)
