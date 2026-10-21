module
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.WfTensorCompletionFrobenius
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.SixFunctors.OpenFactorTensorModel

/-! # The representative-normalized tensor comparison for projection

Source: main-20261015, projection-formula proof step 13
(blueprint: def-sf-projection-coefficient-tensor-total).
The ordinary comparison is fixed on homogeneous local pure tensors. Derived
descent and the specified quotient-completion unit then fix its integral and
rational constructible restrictions.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ProjectionTensorCoefficient

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

/-- Termwise scalar restriction along the quotient-normalized ring isomorphism.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def complexTransport :=
  (fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ)

/-- Signed total tensor after coefficient restriction.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def totalTarget :=
  ((complexTransport l E X).prod (complexTransport l E X)) ⋙
    Functor.uncurry.obj
      ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map₂CochainComplex)

/-- The coefficient tensor comparison is fixed on local pure tensors.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: send x tensor y to the same tensor of the two restricted sections.
Restriction along the inverse ring isomorphism gives the inverse. Balancedness
and restriction compatibility descend through sheafification. Pure tensors
locally generate the tensor sheaf, proving naturality and uniqueness. -/
theorem module_existsUnique :
    ∃! mu : ∀ M N : integralTowerModules l E X,
      (fdCoefficientTransport l E X).obj
          (((constructibleTensorOrdinary l E X).obj M).obj N) ≅
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
          ((fdCoefficientTransport l E X).obj M)).obj
            ((fdCoefficientTransport l E X).obj N),
      (∀ (M M' N N' : integralTowerModules l E X) (f : M ⟶ M') (g : N ⟶ N'),
        (fdCoefficientTransport l E X).map
            (((constructibleTensorOrdinary l E X).map f).app N ≫
              ((constructibleTensorOrdinary l E X).obj M').map g) ≫ (mu M' N').hom =
          (mu M N).hom ≫
            ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map
              ((fdCoefficientTransport l E X).map f)).app
                ((fdCoefficientTransport l E X).obj N) ≫
            ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
              ((fdCoefficientTransport l E X).obj M')).map
                ((fdCoefficientTransport l E X).map g)) ∧
      ∀ (M N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (x : M.val.obj U) (y : N.val.obj U),
        (mu M N).hom.val.app U
          (proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X) M N U x y) =
        proEtaleTensorPair X (pbcAdicCompletion X (pbcIntegralDatum l E))
          ((fdCoefficientTransport l E X).obj M)
          ((fdCoefficientTransport l E X).obj N) U x y := by
  sorry

/-- The uniquely pure-tensor-normalized module comparison.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def moduleComparison (M N : integralTowerModules l E X) :
    (fdCoefficientTransport l E X).obj
        (((constructibleTensorOrdinary l E X).obj M).obj N) ≅
      ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
        ((fdCoefficientTransport l E X).obj M)).obj
          ((fdCoefficientTransport l E X).obj N) :=
  (module_existsUnique l E X).exists.choose M N

/-- Naturality of the specified ordinary coefficient tensor comparison.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: the first clause of the unique pure-tensor characterization gives this
identity; both sides send the generator x tensor y to f(x) tensor g(y). -/
theorem module_naturality
    {M M' N N' : integralTowerModules l E X} (f : M ⟶ M') (g : N ⟶ N') :
    (fdCoefficientTransport l E X).map
        (((constructibleTensorOrdinary l E X).map f).app N ≫
          ((constructibleTensorOrdinary l E X).obj M').map g) ≫
        (moduleComparison l E X M' N').hom =
      (moduleComparison l E X M N).hom ≫
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map
          ((fdCoefficientTransport l E X).map f)).app
            ((fdCoefficientTransport l E X).obj N) ≫
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
          ((fdCoefficientTransport l E X).obj M')).map
            ((fdCoefficientTransport l E X).map g) := by
  sorry

/-- Naturality in the tensorHom coordinates used by the signed-total constructor.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: tensorHom is the first-variable tensor map followed by the
second-variable map. Thus this is precisely module_naturality, with the
same specified monoidal structures on both module categories. -/
theorem module_tensorHom_naturality
    {M M' N N' : integralTowerModules l E X} (f : M ⟶ M') (g : N ⟶ N') :
    (fdCoefficientTransport l E X).map
        (@MonoidalCategoryStruct.tensorHom (integralTowerModules l E X) _
          (SheafOfModules.monoidalCategory
            (completedIntegralCommRingSheafUnrestricted l E X)).toMonoidalCategoryStruct
          M M' N N' f g) ≫ (moduleComparison l E X M' N').hom =
      (moduleComparison l E X M N).hom ≫
        @MonoidalCategoryStruct.tensorHom
          (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) _
          (SheafOfModules.monoidalCategory
            (pbcAdicCompletion X (pbcIntegralDatum l E))).toMonoidalCategoryStruct
          _ _ _ _ ((fdCoefficientTransport l E X).map f)
          ((fdCoefficientTransport l E X).map g) := by
  sorry

/-- The inverse module comparison summed over all bidegrees with the usual signs.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def total (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (totalTarget l E X).obj (P, Q) ⟶
      (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) :=
  letI : MonoidalCategory (integralTowerModules l E X) :=
    SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  letI : MonoidalPreadditive (integralTowerModules l E X) :=
    proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalPreadditive
      (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  tensorPullbackTotal (fdCoefficientTransport l E X) (moduleComparison l E X)
    (module_tensorHom_naturality l E X) P Q

/-- The signed total comparison is invertible.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: exact coefficient restriction along an isomorphism preserves direct sums;
each summand comparison is invertible. The same direct-sum formula with the
inverse summand maps is the two-sided inverse chain map. -/
theorem total_isIso (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    IsIso (total l E X P Q) := by
  sorry

/-- The signed total isomorphism with the derived-square orientation.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def totalIso (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) ≅
      (totalTarget l E X).obj (P, Q) :=
  letI := total_isIso l E X P Q
  (asIso (total l E X P Q)).symm

end WeilConjectures.ProjectionTensorCoefficient
