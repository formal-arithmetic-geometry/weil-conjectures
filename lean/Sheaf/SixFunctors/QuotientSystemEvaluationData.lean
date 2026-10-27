module

public import Sheaf.SixFunctors.QuotientSystemProjectionData
/-! # Normalized evaluation data for coefficient-system projection

Source: Stacks 0B56, equation-projection-formula-map, and 0D6E,
lemma-derived-pushforward-composition, on the small ringed diagram sites
(blueprint: def-sfb-quotient-system-evaluation-data).

## Main definitions and statements

* `coefficientEvaluation`: actual exact coefficient-linear evaluation.
* `EvaluationLift`: normalized ordinary evaluation and derived adjunction comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

universe uC vC uD vD r wY wX wTY wTX wQY wQX wLY wLX
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.CochainPullback CategoryTheory.StrictReduction
namespace CategoryTheory.QuotientProjection
universe e0 h0 e1 h1 e2 h2 e3 h3 e4 h4 e5 h5

/-- Generic evaluation comparison of adjunctions, fixed by the counit equation.
Source: Stacks 07A6 and 0D6E
(blueprint: def-sfb-quotient-system-evaluation-data). -/
structure EvaluationAdjunctionData
    {A : Type e0} [Category.{h0} A] {B : Type e1} [Category.{h1} B]
    {CY : Type e2} [Category.{h2} CY] {CX : Type e3} [Category.{h3} CX]
    (EY : A ⥤ CY) (EX : B ⥤ CX) (F : A ⥤ B) (FN : CY ⥤ CX)
    (GQ : B ⥤ A) (aQ : F ⊣ GQ) (square : EY ⋙ FN ≅ F ⋙ EX) where
  G : CX ⥤ CY
  adj : FN ⊣ G
  gamma : GQ ⋙ EY ≅ EX ⋙ G
  normalization : ∀ N : B,
    EX.map (aQ.counit.app N) = square.inv.app (GQ.obj N) ≫
      FN.map (gamma.hom.app N) ≫ adj.counit.app (EX.obj N)

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
variable (Q : ℕᵒᵖ ⥤ Modules R) [MonObj Q]
  [HasDerivedCategory.{wY} (Modules R)]
  [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{wQY} (Systems Q)]
  (f : RingedPullback R S) [f.L.Monoidal]
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
  [HasDerivedCategory.{wX} (Modules S)]
  [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ Modules S)]
  [HasDerivedCategory.{wQX} (Systems ((termwise f.L).obj Q))]
  [f.V.Additive] (k : Comparison f)
  (MY : RingedModel Q (MonObj.one (X := Q)))
  (MX : RingedModel (Q ⋙ f.L)
    (pulledUnit f.L (moduleUnit f k) Q (MonObj.one (X := Q))))
  (P : AugmentedProjectionDirectImage f.L f.V f.moduleAdj)

/-- Evaluation is strong monoidal for the pointwise tensor structure.
Source: Stacks 02MZ (blueprint: def-sfb-quotient-system-evaluation-data). -/
instance evaluationMonoidal (n : ℕᵒᵖ) :
    ((evaluation ℕᵒᵖ (Modules R)).obj n).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

/-- The actual evaluated coefficient monoid, with its image structure fixed explicitly.
Source: Stacks 02MZ and 03EK
(blueprint: def-sfb-quotient-system-evaluation-data). -/
def levelAlgebra (A : ℕᵒᵖ ⥤ Modules R) [MonObj A] (n : ℕᵒᵖ) : Mon (Modules R) :=
  { X := ((evaluation ℕᵒᵖ (Modules R)).obj n).obj A
    mon := ((evaluation ℕᵒᵖ (Modules R)).obj n).monObjObj A }

/-- Modules over the actual evaluated coefficient monoid.
Source: Stacks 03EK (blueprint: def-sfb-quotient-system-evaluation-data). -/
abbrev Level (A : ℕᵒᵖ ⥤ Modules R) [MonObj A] (n : ℕᵒᵖ) :=
  Mod (Modules R) (levelAlgebra A n).X

/-- Coefficient-linear evaluation; its underlying functor is ordinary tower evaluation.
Source: Stacks 0D6E on diagram sites
(blueprint: def-sfb-quotient-system-evaluation-data). -/
abbrev coefficientEvaluation (n : ℕᵒᵖ) : Systems Q ⥤ Level Q n :=
  ((evaluation ℕᵒᵖ (Modules R)).obj n).mapMod Q

/-- Additivity of coefficient evaluation, on the actual evaluated algebra structure.
Source: Stacks 02MZ (blueprint: def-sfb-quotient-system-evaluation-data). -/
instance coefficientEvaluationAdditive (n : ℕᵒᵖ) : (coefficientEvaluation Q n).Additive where
  map_add {_ _} _g _h := Mod.hom_ext _ _ rfl

/-- Left exactness of coefficient evaluation, inherited from actual pointwise evaluation.
Source: Stacks 02MZ (blueprint: def-sfb-quotient-system-evaluation-data). -/
instance coefficientEvaluationLimits (n : ℕᵒᵖ) :
    PreservesFiniteLimits (coefficientEvaluation Q n) :=
  inferInstanceAs
    (PreservesFiniteLimits (((evaluation ℕᵒᵖ (Modules R)).obj n).mapMod Q))

/-- Right exactness of coefficient evaluation, inherited from actual pointwise evaluation.
Source: Stacks 02MZ (blueprint: def-sfb-quotient-system-evaluation-data). -/
instance coefficientEvaluationColimits (n : ℕᵒᵖ) :
    PreservesFiniteColimits (coefficientEvaluation Q n) :=
  inferInstanceAs
    (PreservesFiniteColimits (((evaluation ℕᵒᵖ (Modules R)).obj n).mapMod Q))

/-- An ordinary presentation of the canonical pullback at a coefficient level, retaining
its scalar action and its evaluation square. The free comparison is fixed on underlying
maps by k.mu. The square is fixed by the inverse of the underlying pullback comparison.
This permits the identity coefficient transport between the two monoidal image
presentations of Q_X,n without assuming they are definitionally equal.
Source: Stacks 07A4 and 0D6D
(blueprint: def-sfb-quotient-system-evaluation-data). -/
structure EvaluationPullbackData (n : ℕᵒᵖ) where
  F : Level Q n ⥤ Level ((termwise f.L).obj Q) n
  additive : F.Additive
  limits : PreservesFiniteLimits F
  colimits : PreservesFiniteColimits F
  underlying : Mod.forget (levelAlgebra Q n).X ⋙ f.L ≅
    F ⋙ Mod.forget (levelAlgebra ((termwise f.L).obj Q) n).X
  free : Mod.free (levelAlgebra Q n).X ⋙ F ≅
    f.L ⋙ Mod.free (levelAlgebra ((termwise f.L).obj Q) n).X
  free_normalization : ∀ M : Modules R,
    underlying.hom.app ((Mod.free (levelAlgebra Q n).X).obj M) ≫ (free.hom.app M).hom =
      (k.mu (Q.obj n) M).hom
  square : coefficientEvaluation Q n ⋙ F ≅
    pullback Q f ⋙ coefficientEvaluation ((termwise f.L).obj Q) n
  square_normalization : ∀ N : Systems Q,
    (square.hom.app N).hom = underlying.inv.app ((coefficientEvaluation Q n).obj N)

attribute [instance] EvaluationPullbackData.additive EvaluationPullbackData.limits
  EvaluationPullbackData.colimits

/-- The derived evaluation square obtained from its normalized ordinary square.
Source: Stacks 0D6D (blueprint: def-sfb-quotient-system-evaluation-data). -/
def evaluationPullback (n : ℕᵒᵖ)
    [HasDerivedCategory.{wLY} (Level Q n)]
    [HasDerivedCategory.{wLX} (Level ((termwise f.L).obj Q) n)]
    (O : EvaluationPullbackData Q f k n) :
    (coefficientEvaluation Q n).mapDerivedCategory ⋙ O.F.mapDerivedCategory ≅
      (pullback Q f).mapDerivedCategory ⋙
        (coefficientEvaluation ((termwise f.L).obj Q) n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (coefficientEvaluation Q n) O.F).symm ≪≫
    Functor.mapDerivedCategoryNatIso O.square ≪≫
      Functor.mapDerivedCategoryCompIso (pullback Q f)
        (coefficientEvaluation ((termwise f.L).obj Q) n)

/-- The coefficient-linear evaluation adjunction and its right-adjoint comparison,
normalized by the actual counits. It specifies evaluation of an actual transpose.
Source: Stacks 07A6 and 0D6E on the ringed evaluation morphism
(blueprint: def-sfb-quotient-system-evaluation-data). -/
abbrev EvaluationLift (L : Lift Q f k MY MX P) (n : ℕᵒᵖ)
    [HasDerivedCategory.{wLY} (Level Q n)]
    [HasDerivedCategory.{wLX} (Level ((termwise f.L).obj Q) n)] :=
  Σ O : EvaluationPullbackData Q f k n,
    EvaluationAdjunctionData (coefficientEvaluation Q n).mapDerivedCategory
      (coefficientEvaluation ((termwise f.L).obj Q) n).mapDerivedCategory
      (pullback Q f).mapDerivedCategory O.F.mapDerivedCategory L.G L.adj
      (evaluationPullback Q f k n O)

/-- The evaluated universal scalar-extension counit, obtained by exact evaluation.
Source: Stacks 0D6D and 06YY
(blueprint: def-sfb-quotient-system-evaluation-data). -/
def evaluationCounit (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q)
    (M : RingedModel Q e) (N : ScalarModel Q e M) (n : ℕᵒᵖ)
    [HasDerivedCategory.{wLY} (Level Q n)] :
    DerivedCategory.Q ⋙ N.B ⋙ (coefficientEvaluation Q n).mapDerivedCategory ⟶
      (scalar Q).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientEvaluation Q n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight N.counit (coefficientEvaluation Q n).mapDerivedCategory ≫
    Functor.whiskerLeft ((scalar Q).mapHomologicalComplex (.up ℤ))
      (coefficientEvaluation Q n).mapDerivedCategoryFactors.hom

end CategoryTheory.QuotientProjection
