/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionRecursion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteExpression.NativeIntegralSystemExpressionDomain
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeAssemblyCoefficients.ScalarSixCoefficientCore
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

/-! # Intermediate assembly data for integral realization
Source: blueprint fix-prop-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical simultaneous models before expression realization. This records only
ambient operations, their normalized mates and open reconstruction.
Source: Stacks 0941, 07A7, 03DI; blueprint fix-prop-coherence, steps 1--2
(blueprint: def-sf-integral-system-realization-data). -/
structure AmbientModels (o : Operations l E) where
  /-- The proper/open mate, scalar restriction, and normalized pasting package. -/
  compositors : Compositors l E o
  openComparisons : OpenComparisons l E o compositors
  canonicalBridge : CanonicalBridge l E o
  properOpen : ProperOpenCoherence l E o compositors openComparisons canonicalBridge
  /-- The tensor/square identifications obey the displayed equation of
      lem-weil-pbc-ringed-exchange-tensor-coherence, before evaluation. -/
  ringedTensorCoherence : ∀ {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) (M : System l E V) (N : System l E Z),
    (IntegralSystemRealization.pull l E i).map
        (((properProjection l E o p).app M).app N) ≫
      (properExchange l E o compositors k r p i h).app
        ((calculus l E V).systemClosed.tensor.obj
          (M, (IntegralSystemRealization.pull l E p).obj N)) ≫
      (Operations.push l E o r).map
        ((pullbackTensorSystemComparison l E k).hom.app
          (M, (IntegralSystemRealization.pull l E p).obj N) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((compositors.square l E k r p i h).inv.app N))) =
    (pullbackTensorSystemComparison l E i).hom.app ((Operations.push l E o p).obj M, N) ≫
      (calculus l E W).systemClosed.tensor.map
        (Prod.mkHom ((properExchange l E o compositors k r p i h).app M) (𝟙 _)) ≫
      ((properProjection l E o r).app ((IntegralSystemRealization.pull l E k).obj M)).app
        ((IntegralSystemRealization.pull l E i).obj N)
  realizationModel : RealizationModel l E o
  /-- The open comparison is the actual reduction mate followed by the inverse
      reconstruction unit. Its displayed equation fixes it without finite evaluation. -/
  openRealization : ∀ {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (_hq : QuasiCompact j) (M : System l E U)
    (_hM : Good l E U M) (_hJ : Good l E V ((Operations.shriek l E o j).obj M)),
    (coefficientSequenceLimit l E V).obj ((Operations.shriek l E o j).obj M) ≅
      ((PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).mapDerivedCategory).obj
        ((coefficientSequenceLimit l E U).obj M)
  openNormalization : ∀ {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] [QuasiCompact j] (M : System l E U)
    (hM : Good l E U M) (hJ : Good l E V ((Operations.shriek l E o j).obj M)),
    (coefficientSequenceLimit l E V).map
      ((Operations.shriek l E o j).map ((calculus l E U).adjunction.counit.app M)) ≫
      (openRealization j inferInstance M hM hJ).hom ≫
      (calculus l E V).adjunction.unit.app
        (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapDerivedCategory).obj
          ((coefficientSequenceLimit l E U).obj M)) =
    (coefficientSequenceLimit l E V).map
      ((realizationModel.openReduction l E j).app ((coefficientSequenceLimit l E U).obj M))
  /-- Published completion-unit models fix the localized integral generators. -/
  ringedModels : RingedModels l E
  ringedOpenComparisons : RingedOpenComparisons l E ringedModels
  ringedProperOpen : RingedProperOpen l E ringedModels ringedOpenComparisons

/-- The explicit recursion equations for a given comparison family. These equations
contain neither coefficient normalization nor compatibility with canonical generator maps.
Source: blueprint fix-prop-coherence, expression-tree construction
(blueprint: def-sf-integral-system-realization-data). -/
structure RecursionLaws (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (a : AmbientModels l E o)
    (comparison : ExpressionRecursion.Comparisons l E D o) : Prop where
  /-- Variable comparisons are the inverse of the actual reconstruction unit. -/
  inputNormalization : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))} (i : I)
    (g : (Expression.var (X := X) i).geometric)
    (K : ((Expression.var (X := X) i).domain l E o).FullSubcategory),
    (calculus l E (X i).left).adjunction.unit.app (K.obj i) ≫
      (comparison (.var i) g).hom.app K = 𝟙 (K.obj i)
  /-- The proper-image comparison is the right-adjoint conjugate, recursively
      followed by proper image of the inner comparison. -/
  push : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (hp : IsProper f.left) (e : Expression _ I X U)
    (ge : e.geometric) (g : (Expression.push f hp e).geometric)
    (K : ((Expression.push f hp e).domain l E o).FullSubcategory),
    (comparison (.push f hp e) g).hom.app K =
      (a.realizationModel.push l E f.left).hom.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) ≫
      (PurCompactSupport.push (PurCompactSupport.completed l E) f.left).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Pullback comparison is fixed by the published K-flat quotient-tower model. -/
  pull : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (e : Expression _ I X V)
    (ge : e.geometric) (g : (Expression.pull f e).geometric)
    (K : ((Expression.pull f e).domain l E o).FullSubcategory),
    (coefficientSequenceLimit l E U.left).map
      ((IntegralSystemRealization.pull l E f.left).map
        ((calculus l E V.left).adjunction.counit.app
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))) ≫
      (comparison (.pull f e) g).hom.app K =
    (pullbackTensorIntegralPullbackModel l E f.left).inv.app
      ((coefficientSequenceLimit l E V.left).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) ≫
      (integralDerivedPullback l E f.left).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Open comparison uses the specified open-reduction mate and actual unit. -/
  shriek : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (j : U ⟶ V) [hj : IsOpenImmersion j.left] [hq : QuasiCompact j.left]
    (e : Expression _ I X U) (ge : e.geometric)
    (g : (Expression.shriek j hj hq e).geometric)
    (K : ((Expression.shriek j hj hq e).domain l E o).FullSubcategory),
    (comparison (.shriek j hj hq e) g).hom.app K =
      (a.openRealization j.left hq
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
        (e.admissibleGood l E o _ (by
          simpa [Expression.admissible] using K.property.2.2)) K.property.2.1).hom ≫
      ((PurCompactSupport.openExtension
        (PurCompactSupport.completed l E) j.left).mapDerivedCategory).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Tensor comparison is fixed by the canonical two-input K-flat total tensor model. -/
  tensor : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (g : (Expression.tensor e t).geometric)
    (K : ((Expression.tensor e t).domain l E o).FullSubcategory),
    (coefficientSequenceLimit l E W.left).map
      ((calculus l E W.left).systemClosed.tensor.map
        (((calculus l E W.left).adjunction.counit.app
            ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
          ((calculus l E W.left).adjunction.counit.app
            ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))))) ≫
      (comparison (.tensor e t) g).hom.app K =
    (pullbackTensorIntegralTensorModel l E W.left).inv.app
      (((coefficientSequenceLimit l E W.left).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
        ((coefficientSequenceLimit l E W.left).obj
          ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))) ≫
      (integralCompletedTensor l E W.left).map
        (Prod.mkHom
          ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩)
          ((comparison t gt).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.2⟩))
  /-- Compact support uses exactly the recursively realized J-then-S composite. -/
  supportRecursion : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (c : Compactification f.left) (e : Expression _ I X U)
    (ge : e.geometric) (g : (Expression.compactSupport f c e).geometric)
    (K : ((Expression.compactSupport f c e).domain l E o).FullSubcategory),
    (comparison (.compactSupport f c e) g).hom.app K =
      (a.realizationModel.push l E c.g).hom.app
        ((Operations.shriek l E o c.i).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) ≫
      (PurCompactSupport.push (PurCompactSupport.completed l E) c.g).map
        ((a.openRealization c.i (compactOpenQuasiCompact c g.2.2.2.2.1)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
          (e.admissibleGood l E o _ (by
            simpa [Expression.admissible] using K.property.2.2.1))
          (by simpa [Expression.admissible] using K.property.2.2.2)).hom ≫
        ((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) c.i).mapDerivedCategory).map
          ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩))

end WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ambient comparison data are the normalized scalar pullback comparisons, including
geometric composition and coefficient-tower equations. Open extension and tensor comparison
are the canonical scalar-adjunction conjugate and tensorator; proper image uses the mate of
inverse pullback comparison. No strict-system reconstruction or completion is included.
Source: latest blueprint fix-prop-coherence.proof.md, individual-map coefficient comparisons
(blueprint: def-sf-integral-realization-assembly-data). -/
abbrev AmbientModels := ScalarSixPullbackData.{u}

/-- The normalization fixes all ambient comparison data uniquely.
Source: latest blueprint fix-prop-coherence, comparisons of the individual maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: the two forward pullback maps are equal to the prescribed scalar-adjunction mate.
An isomorphism is determined by its forward map, so function extensionality identifies
the pullback comparison families. The remaining fields are proofs and agree by proof
irrelevance. This is uniqueness only, with no existence choice. -/
theorem eq (d d' : AmbientModels.{u}) : d = d' := by
  have h : @ScalarSixPullbackData.theta d = @ScalarSixPullbackData.theta d' := by
    funext Λ Γ a U V f
    apply Iso.ext
    exact (d.thetaNormalization a f).trans (d'.thetaNormalization a f).symm
  cases d
  cases d'
  cases h
  rfl

/-- The actual geometric adjunction mate, with its normalization inherited from pullback.
Source: blueprint fix-prop-coherence, units and counits
(blueprint: def-sf-integral-realization-assembly-data). -/
def push {U V : Scheme.{u}} (f : U ⟶ V) :
    moduleObjectDerivedPushforward Λ.X f ⋙ NativeAssemblyCoefficients.scalarSixChange a V ⟶
      NativeAssemblyCoefficients.scalarSixChange a U ⋙ moduleObjectDerivedPushforward Γ.X f :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ.X f)
    (derivedUpperStarLowerStarAdjunction Γ.X f)
    (TwoSquare.mk _ _ _ _ (d.pull a f).inv)).natTrans

/-- The specified scalar pullback comparison on the total left derived functors.
Source: blueprint fix-prop-coherence, adjunction comparison
(blueprint: def-sf-integral-realization-assembly-data). -/
def pull {U V : Scheme.{u}} (f : U ⟶ V) :
    moduleObjectDerivedPullback Λ.X f ⋙ NativeAssemblyCoefficients.scalarSixChange a U ≅
      NativeAssemblyCoefficients.scalarSixChange a V ⋙ moduleObjectDerivedPullback Γ.X f :=
  Functor.isoWhiskerRight (upperStar Λ.X f).leftDerivedFunctorIsoMapDerivedCategory
      (NativeAssemblyCoefficients.scalarSixChange a U) ≪≫ d.theta a f ≪≫
    Functor.isoWhiskerLeft (NativeAssemblyCoefficients.scalarSixChange a V)
      (upperStar Γ.X f).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- Change each input by the ordinary derived coefficient functor.
Source: blueprint fix-prop-coherence, substitution of coefficient comparisons
(blueprint: def-sf-integral-realization-assembly-data). -/
def expressionInputChange {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] (X : I → Over B) :
    (∀ i, ModuleDerivedCategory Λ.X (X i).left) ⥤
      (∀ i, ModuleDerivedCategory Γ.X (X i).left) where
  obj K i := (NativeAssemblyCoefficients.scalarSixChange a (X i).left).obj (K i)
  map h i := (NativeAssemblyCoefficients.scalarSixChange a (X i).left).map (h i)

/-- Primitive coefficient natural transformations composed along the finite expression tree.
Compact support is exactly open extension followed by proper image. Whiskering and the product
of the two child transformations supply naturality; no completion unit is used.
Source: latest blueprint fix-prop-coherence.proof.md, coefficient comparison sentence
(blueprint: def-sf-integral-realization-assembly-data). -/
def FiniteExpression.coefficientTransformation (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B} {W : Over B}
    (e : FiniteExpression B I X W) :
    e.evaluate Λ.X ⋙ NativeAssemblyCoefficients.scalarSixChange a W.left ⟶
      expressionInputChange a X ⋙ e.evaluate Γ.X := by
  induction e with
  | var i => exact 𝟙 _
  | pullback f e ih =>
      exact Functor.whiskerLeft (e.evaluate Λ.X) (d.pull a f.left).hom ≫
        Functor.whiskerRight ih (moduleObjectDerivedPullback Γ.X f.left)
  | properPushforward f hf e ih =>
      exact Functor.whiskerLeft (e.evaluate Λ.X) (d.push a f.left) ≫
        Functor.whiskerRight ih (moduleObjectDerivedPushforward Γ.X f.left)
  | openExtension j hj hqc e ih =>
      letI := hj
      exact Functor.whiskerLeft (e.evaluate Λ.X)
          (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Γ.X) a.hom.hom j.left).hom ≫
        Functor.whiskerRight ih (openImmersionLowerShriek Γ.X j.left).mapDerivedCategory
  | tensor e t ihe iht =>
      exact Functor.whiskerLeft ((e.evaluate Λ.X).prod' (t.evaluate Λ.X))
          (Functor.Monoidal.μNatIso (NativeAssemblyCoefficients.scalarSixChange a _)).inv ≫
        Functor.whiskerRight (NatTrans.prod' ihe iht)
          (Functor.uncurry.obj (derivedTensor Γ.X _))
  | compactSupport f c e ih =>
      exact Functor.whiskerLeft
          (e.evaluate Λ.X ⋙ (openImmersionLowerShriek Λ.X c.i).mapDerivedCategory)
          (d.push a c.g) ≫
        Functor.whiskerLeft (e.evaluate Λ.X)
          (Functor.whiskerRight
            (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Γ.X) a.hom.hom c.i).hom
            (moduleObjectDerivedPushforward Γ.X c.g)) ≫
        Functor.whiskerRight ih
          ((openImmersionLowerShriek Γ.X c.i).mapDerivedCategory ⋙
            moduleObjectDerivedPushforward Γ.X c.g)

/-- The component of the actual recursively constructed coefficient transformation.
Source: latest blueprint fix-prop-coherence, individual coefficient comparisons
(blueprint: def-sf-integral-realization-assembly-data). -/
def FiniteExpression.coefficientMap (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B} {W : Over B}
    (e : FiniteExpression B I X W) (K : ∀ i, ModuleDerivedCategory Λ.X (X i).left) :
    (NativeAssemblyCoefficients.scalarSixChange a W.left).obj ((e.evaluate Λ.X).obj K) ⟶
      (e.evaluate Γ.X).obj ((expressionInputChange a X).obj K) :=
  (e.coefficientTransformation d a).app K

/-- Naturality of the constructed family in all input morphisms.
Source: latest blueprint fix-prop-coherence, coefficient comparisons of individual maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: take the naturality equation of the recursively assembled natural transformation. -/
theorem FiniteExpression.coefficientMap_naturality (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B} {W : Over B}
    (e : FiniteExpression B I X W)
    {K L : ∀ i, ModuleDerivedCategory Λ.X (X i).left} (h : K ⟶ L) :
    (NativeAssemblyCoefficients.scalarSixChange a W.left).map ((e.evaluate Λ.X).map h) ≫ e.coefficientMap d a L =
      e.coefficientMap d a K ≫ (e.evaluate Γ.X).map ((expressionInputChange a X).map h) :=
  (e.coefficientTransformation d a).naturality h

/-- Restriction of the actual comparison to the published intermediate-object domain.
This retains all morphisms of the full subcategory and asserts no preservation or
invertibility beyond that already proved for the primitive maps on the stated domains.
Source: latest blueprint fix-prop-coherence, final sentence
(blueprint: def-sf-integral-realization-assembly-data). -/
def FiniteExpression.domainCoefficientTransformation (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B} {W : Over B}
    (e : FiniteExpression B I X W) :
    e.domainEvaluation Λ.X ⋙ NativeAssemblyCoefficients.scalarSixChange a W.left ⟶
      (e.domain Λ.X).ι ⋙ expressionInputChange a X ⋙ e.evaluate Γ.X :=
  Functor.whiskerLeft (e.domain Λ.X).ι (e.coefficientTransformation d a)

/-- A comparison family for the fixed coefficient map and input schemes, before imposing
invertibility or a constructibility condition. Its recursion laws below fix the maps.
Source: latest blueprint fix-prop-coherence, coefficient comparison sentence
(blueprint: def-sf-integral-realization-assembly-data). -/
abbrev ExpressionComparisonFamily {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] (X : I → Over B) :=
  ∀ {W : Over B} (e : FiniteExpression B I X W)
    (K : ∀ i, ModuleDerivedCategory Λ.X (X i).left),
    (NativeAssemblyCoefficients.scalarSixChange a W.left).obj ((e.evaluate Λ.X).obj K) ⟶
      (e.evaluate Γ.X).obj ((expressionInputChange a X).obj K)

/-- The six explicit recursion equations for native coefficient comparisons. They use the
prescribed pullback comparison, its proper-image mate, the canonical open conjugate and
ordinary scalar tensorator. This asserts no generator, exchange or projection coherence.
Source: latest blueprint fix-prop-coherence.proof.md, individual maps before inheritance
(blueprint: def-sf-integral-realization-assembly-data). -/
structure RecursionLaws (d : AmbientModels.{u}) {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] (X : I → Over B)
    (comparison : ExpressionComparisonFamily a X) : Prop where
  input : ∀ (i : I) K, comparison (.var i) K = 𝟙 _
  pull : ∀ {U V : Over B} (f : U ⟶ V) (e : FiniteExpression B I X V) K,
    comparison (.pullback f e) K =
      (d.pull a f.left).hom.app ((e.evaluate Λ.X).obj K) ≫
        (moduleObjectDerivedPullback Γ.X f.left).map (comparison e K)
  push : ∀ {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : FiniteExpression B I X U) K,
    comparison (.properPushforward f hf e) K =
      (d.push a f.left).app ((e.evaluate Λ.X).obj K) ≫
        (moduleObjectDerivedPushforward Γ.X f.left).map (comparison e K)
  openExtension : ∀ {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left]
      (hqc : QuasiCompact j.left) (e : FiniteExpression B I X U) K,
    comparison (.openExtension j hj hqc e) K =
      (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Γ.X) a.hom.hom j.left).hom.app
          ((e.evaluate Λ.X).obj K) ≫
        (openImmersionLowerShriek Γ.X j.left).mapDerivedCategory.map (comparison e K)
  tensor : ∀ {W : Over B} (e t : FiniteExpression B I X W) K,
    comparison (.tensor e t) K =
      (scalarSixTensorIso a W.left ((e.evaluate Λ.X).obj K)
        ((t.evaluate Λ.X).obj K)).hom ≫
        (Functor.uncurry.obj (derivedTensor Γ.X W.left)).map
          (Prod.mkHom (comparison e K) (comparison t K))
  compactSupport : ∀ {U V : Over B} (f : U ⟶ V) (c : Compactification f.left)
      (e : FiniteExpression B I X U) K,
    comparison (.compactSupport f c e) K =
      (d.push a c.g).app
          ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj
            ((e.evaluate Λ.X).obj K)) ≫
        (moduleObjectDerivedPushforward Γ.X c.g).map
          ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Γ.X) a.hom.hom c.i).hom.app
              ((e.evaluate Λ.X).obj K) ≫
            (openImmersionLowerShriek Γ.X c.i).mapDerivedCategory.map (comparison e K))

/-- The constructed family satisfies the six equations by its actual recursion.
Source: latest blueprint fix-prop-coherence, individual-map assembly
(blueprint: def-sf-integral-realization-assembly-data).
Proof: each field unfolds the corresponding branch of the finite recursion. -/
theorem coefficientMap_recursionLaws (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] (X : I → Over B) :
    RecursionLaws d a X (fun e K ↦ e.coefficientMap d a K) := by
  constructor
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros
    simp only [FiniteExpression.coefficientMap, FiniteExpression.coefficientTransformation,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.comp_map, Functor.map_comp]

/-- The recursion equations determine the comparison family without an existence choice.
Source: latest blueprint fix-prop-coherence, inheritance from individual maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: induct on the finite tree. The variable equation fixes a leaf; in each unary case
substitute the equation and the child induction hypothesis. At tensor substitute both child
hypotheses. At compact support substitute the child hypothesis in the fixed open/proper
composite. No domain preservation, coefficient flatness or completion is used. -/
theorem RecursionLaws.eq_coefficientMap (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    {comparison : ExpressionComparisonFamily a X} (h : RecursionLaws d a X comparison)
    {W : Over B} (e : FiniteExpression B I X W)
    (K : ∀ i, ModuleDerivedCategory Λ.X (X i).left) :
    comparison e K = e.coefficientMap d a K := by
  have canonical := coefficientMap_recursionLaws d a X
  induction e with
  | var i => rw [h.input, canonical.input]
  | pullback f e ih => rw [h.pull, canonical.pull, ih]
  | properPushforward f hf e ih => rw [h.push, canonical.push, ih]
  | openExtension j hj hqc e ih => rw [h.openExtension, canonical.openExtension, ih]
  | @tensor W e t ihe iht =>
      exact (h.tensor e t K).trans
        ((congrArg₂
          (fun (f : (NativeAssemblyCoefficients.scalarSixChange a W.left).obj ((e.evaluate Λ.X).obj K) ⟶
              (e.evaluate Γ.X).obj ((expressionInputChange a X).obj K))
            (g : (NativeAssemblyCoefficients.scalarSixChange a W.left).obj ((t.evaluate Λ.X).obj K) ⟶
              (t.evaluate Γ.X).obj ((expressionInputChange a X).obj K)) ↦
            (scalarSixTensorIso a W.left ((e.evaluate Λ.X).obj K)
              ((t.evaluate Λ.X).obj K)).hom ≫
                (Functor.uncurry.obj (derivedTensor Γ.X W.left)).map (Prod.mkHom f g))
          ihe iht).trans (canonical.tensor e t K).symm)
  | compactSupport f c e ih => rw [h.compactSupport, canonical.compactSupport, ih]

/-- The six component equations determine the whole comparison natural transformation.
Source: latest blueprint fix-prop-coherence, inheritance from the individual maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: apply extensionality for natural transformations. At each input, uniqueness of
the component family from the six recursion laws gives equality with the recursively
constructed component. No naturality or coherence hypothesis beyond the given natural
transformations and recursion equations is added. -/
theorem coefficientTransformation_eq_of_recursionLaws (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    (comparison : ∀ {W : Over B} (e : FiniteExpression B I X W),
      e.evaluate Λ.X ⋙ NativeAssemblyCoefficients.scalarSixChange a W.left ⟶
        expressionInputChange a X ⋙ e.evaluate Γ.X)
    (h : RecursionLaws d a X (fun e K ↦ (comparison e).app K))
    {W : Over B} (e : FiniteExpression B I X W) :
    comparison e = e.coefficientTransformation d a := by
  ext K
  simpa only [FiniteExpression.coefficientMap] using h.eq_coefficientMap d a e K

/-- The six component equations already force naturality in all input morphisms.
Source: latest blueprint fix-prop-coherence, inheritance from individual coefficient maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: recursion uniqueness identifies each component with the constructed comparison;
substitute at both ends of the naturality square and use its naturality theorem. No
naturality hypothesis on the comparison family is needed. -/
theorem RecursionLaws.naturality (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    {comparison : ExpressionComparisonFamily a X} (h : RecursionLaws d a X comparison)
    {W : Over B} (e : FiniteExpression B I X W)
    {K L : ∀ i, ModuleDerivedCategory Λ.X (X i).left} (f : K ⟶ L) :
    (NativeAssemblyCoefficients.scalarSixChange a W.left).map ((e.evaluate Λ.X).map f) ≫ comparison e L =
      comparison e K ≫ (e.evaluate Γ.X).map ((expressionInputChange a X).map f) := by
  rw [h.eq_coefficientMap d a e K, h.eq_coefficientMap d a e L]
  exact e.coefficientMap_naturality d a f

/-- Turn a component family satisfying the six equations into an actual natural
transformation, retaining its given components and deriving naturality from the equations.
Source: latest blueprint fix-prop-coherence, inheritance from individual coefficient maps
(blueprint: def-sf-integral-realization-assembly-data). -/
def RecursionLaws.toNatTrans (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    {comparison : ExpressionComparisonFamily a X} (h : RecursionLaws d a X comparison)
    {W : Over B} (e : FiniteExpression B I X W) :
    e.evaluate Λ.X ⋙ NativeAssemblyCoefficients.scalarSixChange a W.left ⟶
      expressionInputChange a X ⋙ e.evaluate Γ.X where
  app := comparison e
  naturality _ _ f := h.naturality d a e f

/-- Recovering naturality from the component equations gives the canonical transformation.
Source: latest blueprint fix-prop-coherence, inheritance from individual coefficient maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: extensionality reduces equality to each input component, where recursion uniqueness
applies. Thus deriving naturality adds no choices or extra comparison maps. -/
theorem RecursionLaws.toNatTrans_eq (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    {comparison : ExpressionComparisonFamily a X} (h : RecursionLaws d a X comparison)
    {W : Over B} (e : FiniteExpression B I X W) :
    h.toNatTrans d a e = e.coefficientTransformation d a := by
  ext K
  simpa only [RecursionLaws.toNatTrans, FiniteExpression.coefficientMap] using
    h.eq_coefficientMap d a e K

/-- The comparison on the stated domain is natural for every ambient input morphism
between admissible objects; no additional condition on morphisms is imposed.
Source: latest blueprint fix-prop-coherence, inheritance on the stated domains
(blueprint: def-sf-integral-realization-assembly-data).
Proof: apply naturality of the restricted natural transformation. -/
theorem FiniteExpression.domainCoefficientTransformation_naturality (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B} {W : Over B}
    (e : FiniteExpression B I X W)
    {K L : (e.domain Λ.X).FullSubcategory} (f : K ⟶ L) :
    (NativeAssemblyCoefficients.scalarSixChange a W.left).map ((e.domainEvaluation Λ.X).map f) ≫
        (e.domainCoefficientTransformation d a).app L =
      (e.domainCoefficientTransformation d a).app K ≫
        (e.evaluate Γ.X).map ((expressionInputChange a X).map ((e.domain Λ.X).ι.map f)) :=
  (e.domainCoefficientTransformation d a).naturality f

/-- A family specified by recursion restricts to the full intermediate-object domain
with exactly its supplied components. This requires no coefficient-domain preservation.
Source: latest blueprint fix-prop-coherence, inheritance on the stated domains
(blueprint: def-sf-integral-realization-assembly-data). -/
def RecursionLaws.toDomainNatTrans (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    {comparison : ExpressionComparisonFamily a X} (h : RecursionLaws d a X comparison)
    {W : Over B} (e : FiniteExpression B I X W) :
    e.domainEvaluation Λ.X ⋙ NativeAssemblyCoefficients.scalarSixChange a W.left ⟶
      (e.domain Λ.X).ι ⋙ expressionInputChange a X ⋙ e.evaluate Γ.X :=
  Functor.whiskerLeft (e.domain Λ.X).ι (h.toNatTrans d a e)

/-- Deriving naturality from recursion and then restricting gives the specified domain
comparison, retaining all morphisms of the full input subcategory.
Source: latest blueprint fix-prop-coherence, inheritance on the stated domains
(blueprint: def-sf-integral-realization-assembly-data).
Proof: the ambient transformation equals the canonical one by recursion uniqueness.
Apply whiskering along the domain inclusion to this equality. -/
theorem RecursionLaws.toDomainNatTrans_eq (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    {comparison : ExpressionComparisonFamily a X} (h : RecursionLaws d a X comparison)
    {W : Over B} (e : FiniteExpression B I X W) :
    h.toDomainNatTrans d a e = e.domainCoefficientTransformation d a := by
  exact congrArg (Functor.whiskerLeft (e.domain Λ.X).ι) (h.toNatTrans_eq d a e)

/-- The domain comparison is independent of the normalized ambient package.
Source: latest blueprint fix-prop-coherence, individual maps on the stated domains
(blueprint: def-sf-integral-realization-assembly-data).
Proof: whisker ambient independence by the full domain inclusion. -/
theorem FiniteExpression.domainCoefficientTransformation_independent (d d' : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B} {W : Over B}
    (e : FiniteExpression B I X W) :
    e.domainCoefficientTransformation d a = e.domainCoefficientTransformation d' a := by
  exact congrArg (Functor.whiskerLeft (e.domain Λ.X).ι)
    (e.coefficientTransformation_independent d d' a)

/-- The six equations characterize the entire component family, in both directions.
Source: latest blueprint fix-prop-coherence, inheritance from individual maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: function extensionality upgrades the pointwise recursion uniqueness to equality of
families. Conversely, substitute equality with the constructed family and apply its six
proved recursion equations. This identifies specified morphisms, without a conservativity
or invertibility argument. -/
theorem recursionLaws_iff_eq_coefficientMap (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] (X : I → Over B)
    (comparison : ExpressionComparisonFamily a X) :
    RecursionLaws d a X comparison ↔ @comparison = (fun _W e K ↦ e.coefficientMap d a K) := by
  constructor
  · intro h
    apply funext
    intro W
    apply funext
    intro e
    apply funext
    intro K
    exact h.eq_coefficientMap d a e K
  · intro h
    rw [h]
    exact coefficientMap_recursionLaws d a X

/-- There is exactly one family satisfying the prescribed component equations.
Source: latest blueprint fix-prop-coherence, coefficient comparisons of individual maps
(blueprint: def-sf-integral-realization-assembly-data).
Proof: use the recursively constructed family as the explicit witness and its proved
recursion equations. The characterization by those equations gives equality of any other
witness. No object is selected from an unproved existence statement. -/
theorem existsUnique_recursionLaws (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] (X : I → Over B) :
    ∃! comparison : ExpressionComparisonFamily a X, RecursionLaws d a X comparison := by
  refine ⟨(fun {W} e K ↦ e.coefficientMap d a K), coefficientMap_recursionLaws d a X, ?_⟩
  intro comparison h
  exact (recursionLaws_iff_eq_coefficientMap d a X comparison).mp h

/-- Restricting a family specified by the recursion laws retains its original components.
Source: latest blueprint fix-prop-coherence, inheritance on the stated domains
(blueprint: def-sf-integral-realization-assembly-data).
Proof: whiskering along the full inclusion evaluates the same ambient transformation at
the underlying object; the reconstructed transformation was defined with these components. -/
theorem RecursionLaws.toDomainNatTrans_app (d : AmbientModels.{u})
    {Λ Γ : NativeAssemblyCoefficients.ScalarSixRing.{u}} (a : Λ ⟶ Γ)
    {B : Scheme.{u}} {I : Type u} [Fintype I] {X : I → Over B}
    {comparison : ExpressionComparisonFamily a X} (h : RecursionLaws d a X comparison)
    {W : Over B} (e : FiniteExpression B I X W)
    (K : (e.domain Λ.X).FullSubcategory) :
    (h.toDomainNatTrans d a e).app K = comparison e K.obj := by
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
