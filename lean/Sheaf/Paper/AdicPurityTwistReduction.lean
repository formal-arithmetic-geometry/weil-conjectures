/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicPurityFiniteTensor
/-! # Derived reduction of the root-normalized integral twist
Source: blueprint def-coefficient-twists-detailed, finite reduction clause.
(blueprint: def-pur-adic-twist-reduction).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
section TensorRealization
universe a b c v w z
variable {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [SymmetricCategory A]
  [HasDerivedCategory.{w} A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{c} B] [Abelian B] [HasDerivedCategory.{z} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [hF : F.IsEquivalence] (G : B ⥤ B) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (L : A)
  (ordinary : F ⋙ G ≅ tensorRight L ⋙ F)


/-- The full K-flat counit equation specifying an exact tensor realization.
Source: blueprint normalized finite tensor comparison
(blueprint: def-pur-adic-twist-reduction). -/
def IsAdicPurityDerivedTensorNormalized
    (e : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      tensorRight ((DerivedCategory.singleFunctor A 0).obj L) ⋙ F.mapDerivedCategory) : Prop :=
      ∀ (P : CochainComplex A ℤ) (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P),
        e.inv.app (DerivedCategory.Q.obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) =
        F.mapDerivedCategory.map (DerivedCategory.QObjTensorSingleFunctorObjIso P hP L).hom ≫
          F.mapDerivedCategoryFactors.hom.app
            (((tensorRight L).mapHomologicalComplex (.up ℤ)).obj P)

/-- A comparison equipped with the complete K-flat counit equation, using Subtype.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
abbrev AdicPurityDerivedTensorModel :=
  Subtype (IsAdicPurityDerivedTensorNormalized F G L ordinary)

/-- Heterogeneous identification with a fully normalized comparison.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
def HasAdicPurityDerivedTensorModel {S : Type (max (max a v) z)} (e : S) : Prop :=
  ∃ e' : AdicPurityDerivedTensorModel F G L ordinary, HEq e e'.val

include hF

/-- Exact realization of tensor by a flat line is uniquely fixed by its K-flat counit
square. The equation uses abstract exact functors, so no concrete coefficient
presentation is unfolded while checking the representative normalization.
Source: blueprint finite twists, canonical tensor realization
(blueprint: def-pur-adic-twist-reduction).
Proof: on K-flat representatives compose the ordinary comparison with the exact
localization factorization maps and the specified tensor counit. Since F is an exact
equivalence and G is exact, tensor by L is exact. These maps invert quasi-isomorphisms
and descend through K-flat localization. Every derived object has such a resolution;
localization is fully faithful on natural transformations, proving uniqueness. -/
theorem adicPurityDerivedTensorGeneric_existsUnique :
    ∃! e : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      tensorRight ((DerivedCategory.singleFunctor A 0).obj L) ⋙ F.mapDerivedCategory,
      IsAdicPurityDerivedTensorNormalized F G L ordinary e := by
  sorry
end TensorRealization

section ExactSquare
universe x y z
variable {A B C D : Type x}
  [Category.{y} A] [Category.{y} B] [Category.{y} C] [Category.{y} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B]
  [HasDerivedCategory.{z} C] [HasDerivedCategory.{z} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ D) (I : D ⥤ C)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]

/-- Exact localization of an ordinary commuting square, with both factorization
comparisons retained. Source: blueprint twist/restriction comparison
(blueprint: def-pur-adic-twist-reduction). -/
def adicPurityExactSquare (e : F ⋙ G ≅ H ⋙ I) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso H I
end ExactSquare

universe x y

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})
section TwistReduction
variable [hInvert : ∀ x : T, Invertible (l : T.residueField x)]
include hInvert

/-- The exact finite twisting functor with its ordinary exactness witnesses cached.
Source: blueprint finite twists (blueprint: def-pur-adic-twist-reduction). -/
def adicPurityDerivedFiniteTwist (d : ℕ) :
    DerivedCategory (scalarReductionTarget l E T n) ⥤
      DerivedCategory (scalarReductionTarget l E T n) :=
  letI := adicPurityFiniteSheafTwist_additive l E n T d
  letI := adicPurityFiniteSheafTwist_limits l E n T d
  letI := adicPurityFiniteSheafTwist_colimits l E n T d
  (adicPurityFiniteSheafTwist l E n T d).mapDerivedCategory

/-- The cached exact functor is the recorded finite complex twist itself.
Source: blueprint finite twists, exact degree-zero tensor construction
(blueprint: def-pur-adic-twist-reduction).
Proof: unfold finiteComplexTwist, adicPurityDerivedFiniteTwist and the ordinary
adicPurityFiniteSheafTwist. Both are exact localization of the very same tensor
functor on sheaf modules. Their exactness witnesses are proofs and hence equal. -/
theorem adicPurityFiniteTwistPresentation (d : ℕ) :
    finiteComplexTwist l E T n (d : ℤ) = adicPurityDerivedFiniteTwist l E n T d := by
  sorry

/-- Cache the published additive witness at the actual finite twisting functor.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
instance (priority := 5000) adicPurityConcreteTwistAdditive (d : ℕ) :
    (adicPurityFiniteSheafTwist l E n T d).Additive :=
  adicPurityFiniteSheafTwist_additive l E n T d

/-- Cache the published finite-limit witness without a local instance in an inferred type.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
instance (priority := 5000) adicPurityConcreteTwistLimits (d : ℕ) :
    PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d) :=
  adicPurityFiniteSheafTwist_limits l E n T d

/-- Cache the published finite-colimit witness in the same presentation.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
instance (priority := 5000) adicPurityConcreteTwistColimits (d : ℕ) :
    PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d) :=
  adicPurityFiniteSheafTwist_colimits l E n T d

/-- The recorded intrinsic realization with its codomain explicitly in reduction coordinates.
This is the same functor, with no coefficient change or choice of a realization.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
def adicPurityFiniteRealization :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) ⥤
      scalarReductionTarget l E T n :=
  (sfIntrinsicModuleEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor

/-- The recorded realization is an exact additive equivalence in reduction coordinates.
Source: blueprint coefficient realization (blueprint: def-pur-adic-twist-reduction).
Proof: unfold adicPurityFiniteRealization. It is the published ordinary intrinsic
module equivalence; scalarReductionTarget and its codomain are the same constant-ring
module category. An additive equivalence preserves all finite limits and colimits. -/
theorem adicPurityFiniteRealization_properties :
    (adicPurityFiniteRealization l E n T).IsEquivalence ∧
      (adicPurityFiniteRealization l E n T).Additive ∧
      PreservesFiniteLimits (adicPurityFiniteRealization l E n T) ∧
      PreservesFiniteColimits (adicPurityFiniteRealization l E n T) := by
  sorry

/-- The equivalence witness in the explicit finite-reduction coordinates.
Source: blueprint coefficient realization (blueprint: def-pur-adic-twist-reduction). -/
instance adicPurityFiniteRealization_equivalence :
    (adicPurityFiniteRealization l E n T).IsEquivalence :=
  (adicPurityFiniteRealization_properties l E n T).1

/-- Addition is retained in the explicit finite-reduction coordinates.
Source: blueprint coefficient realization (blueprint: def-pur-adic-twist-reduction). -/
instance adicPurityFiniteRealization_additive :
    (adicPurityFiniteRealization l E n T).Additive :=
  (adicPurityFiniteRealization_properties l E n T).2.1

/-- Finite limits are retained in the explicit finite-reduction coordinates.
Source: blueprint coefficient realization (blueprint: def-pur-adic-twist-reduction). -/
instance adicPurityFiniteRealization_limits :
    PreservesFiniteLimits (adicPurityFiniteRealization l E n T) :=
  (adicPurityFiniteRealization_properties l E n T).2.2.1

/-- Finite colimits are retained in the explicit finite-reduction coordinates.
Source: blueprint coefficient realization (blueprint: def-pur-adic-twist-reduction). -/
instance adicPurityFiniteRealization_colimits :
    PreservesFiniteColimits (adicPurityFiniteRealization l E n T) :=
  (adicPurityFiniteRealization_properties l E n T).2.2.2

/-- The same scalar-unit comparison in the explicit realization coordinates.
Heterogeneous equality fixes the entire ordinary natural isomorphism.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction).
Proof: unfold the explicit realization functor. The comparison is exactly the
recorded scalar-unit-normalized ordinary comparison, in the same coefficient category.
Heterogeneous equality identifies its components and proves uniqueness. -/
theorem adicPurityFiniteRealizationTensor_existsUnique (d : ℕ) :
    ∃! e : adicPurityFiniteRealization l E n T ⋙ adicPurityFiniteSheafTwist l E n T d ≅
      tensorRight (finiteTateProSheaf l E n T d) ⋙ adicPurityFiniteRealization l E n T,
      HEq e (adicPurityFiniteTensorRealization l E n T d) := by
  sorry

/-- The ordinary tensor comparison, with the original full scalar-unit normalization.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
@[no_expose] def adicPurityFiniteRealizationTensor (d : ℕ) :=
  (adicPurityFiniteRealizationTensor_existsUnique l E n T d).exists.choose

/-- The generic normalized comparison type in the actual finite coefficient coordinates.
Packaging the equation retains the exact witnesses without a concrete iso-type conversion.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
abbrev AdicPurityDerivedFiniteTensorModel (d : ℕ)
    [hAdd : (adicPurityFiniteSheafTwist l E n T d).Additive]
    [hLimits : PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d)]
    [hColimits : PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d)] :=
  AdicPurityDerivedTensorModel (adicPurityFiniteRealization l E n T)
    (adicPurityFiniteSheafTwist l E n T d) (finiteTateProSheaf l E n T d)
    (adicPurityFiniteRealizationTensor l E n T d)

/-- Full K-flat counit normalization in the concrete finite-coefficient presentation.
The intermediate comparison uses the exact ordinary localization witnesses; heterogeneous
equality retains the same natural isomorphism in the recorded derived presentation.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
def IsAdicPurityDerivedFiniteTensor (d : ℕ)
    [hAdd : (adicPurityFiniteSheafTwist l E n T d).Additive]
    [hLimits : PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d)]
    [hColimits : PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d)]
    {S : Type (u + 2)} (e : S) : Prop :=
  HasAdicPurityDerivedTensorModel (adicPurityFiniteRealization l E n T)
    (adicPurityFiniteSheafTwist l E n T d) (finiteTateProSheaf l E n T d)
    (adicPurityFiniteRealizationTensor l E n T d) e

/-- The full type of the normalized finite tensor comparison, kept in its named
coefficient coordinates. Its data is precisely the recorded natural-isomorphism type.
Source: blueprint canonical tensor realization
(blueprint: def-pur-adic-twist-reduction). -/
def AdicPurityFiniteTensorIsoType (d : ℕ) : Type (u + 2) :=
    (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        finiteComplexTwist l E T n (d : ℤ) ≅
      tensorRight ((DerivedCategory.singleFunctor _ 0).obj (finiteTateProSheaf l E n T d)) ⋙
        (sfIntrinsicDerivedEquivalence T
          (Padic.coefficientExtensionRing l E (n + 1))).functor

/-- A concrete comparison together with its complete K-flat counit normalization.
The normalization determines the natural isomorphism, including its action on all
representatives; this is not a package of arbitrary endpoint isomorphisms.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction). -/
structure AdicPurityFiniteTensorComparison (d : ℕ)
    [hAdd : (adicPurityFiniteSheafTwist l E n T d).Additive]
    [hLimits : PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d)]
    [hColimits : PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d)] where
  comparison : AdicPurityFiniteTensorIsoType l E n T d
  normalized : IsAdicPurityDerivedFiniteTensor l E n T d comparison

/-- The fully normalized finite comparison exists.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction).
Proof: specialize adicPurityDerivedTensorGeneric_existsUnique with the recorded
scalar-unit comparison, explicitly in reduction coordinates. The intrinsic derived
equivalence is exact localization of that realization, and finiteComplexTwist is
exact localization of the ordinary finite tensor. Identifying these presentations
by proof irrelevance supplies the heterogeneous equality in the normalization. -/
theorem adicPurityFiniteTensorComparison_exists (d : ℕ)
    [hAdd : (adicPurityFiniteSheafTwist l E n T d).Additive]
    [hLimits : PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d)]
    [hColimits : PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d)] :
    Nonempty (AdicPurityFiniteTensorComparison l E n T d) := by
  sorry

/-- Full K-flat normalization determines the whole comparison package uniquely.
Source: blueprint finite tensor normalization (blueprint: def-pur-adic-twist-reduction).
Proof: the generic uniqueness theorem identifies the two exact-localization comparisons.
Their heterogeneous equalities identify the concrete natural isomorphisms. The remaining
field is a proposition, so proof irrelevance identifies the packages. -/
theorem adicPurityFiniteTensorComparison_unique (d : ℕ)
    [hAdd : (adicPurityFiniteSheafTwist l E n T d).Additive]
    [hLimits : PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d)]
    [hColimits : PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d)] :
    Subsingleton (AdicPurityFiniteTensorComparison l E n T d) := by
  sorry

/-- The concrete finite tensor comparison, selected from its unique normalized package.
The named existence and uniqueness theorems determine all of its data.
Source: blueprint finite twists (blueprint: def-pur-adic-twist-reduction). -/
@[no_expose] def adicPurityDerivedFiniteTensor (d : ℕ) :
    AdicPurityFiniteTensorIsoType l E n T d :=
  letI := adicPurityFiniteSheafTwist_additive l E n T d
  letI := adicPurityFiniteSheafTwist_limits l E n T d
  letI := adicPurityFiniteSheafTwist_colimits l E n T d
  (Classical.choice (adicPurityFiniteTensorComparison_exists l E n T d)).comparison

/-- The exact derived comparison is induced by the specified ordinary comparison.
Source: blueprint coefficient twists (blueprint: def-pur-adic-twist-reduction). -/
def adicPurityDerivedTwistRestriction (d : ℕ) :
    (scalarReductionRestriction l E T n).mapDerivedCategory ⋙
      (integralSheafTwist l E T (d : ℤ)).mapDerivedCategory ≅
    (adicPurityFiniteSheafTwist l E n T d).mapDerivedCategory ⋙
      (scalarReductionRestriction l E T n).mapDerivedCategory :=
  letI := scalarReductionRestrictionLimits l E T n
  letI := scalarReductionRestrictionColimits l E T n
  letI := integralSheafTwist_additive l E T (d : ℤ)
  letI := integralSheafTwist_finiteLimits l E T (d : ℤ)
  letI := integralSheafTwist_finiteColimits l E T (d : ℤ)
  letI := adicPurityFiniteSheafTwist_additive l E n T d
  letI := adicPurityFiniteSheafTwist_limits l E n T d
  letI := adicPurityFiniteSheafTwist_colimits l E n T d
  adicPurityExactSquare (scalarReductionRestriction l E T n)
    (integralSheafTwist l E T (d : ℤ)) (adicPurityFiniteSheafTwist l E n T d)
    (scalarReductionRestriction l E T n) (adicPurityTwistRestriction l E n T d)



/-- The defining full adjunction-transpose equation of the finite twist reduction.
The presentation equality retains the original finite twisting functor as codomain.
Source: blueprint canonical twist reduction (blueprint: def-pur-adic-twist-reduction). -/
def IsAdicPurityTwistReduction (d : ℕ) (M : DerivedCategory (scalarReductionSource l E T))
    (g : (scalarReductionDerivedExtension l E T n).obj
      ((integralSheafTwist l E T (d : ℤ)).mapDerivedCategory.obj M) ⟶
    (finiteComplexTwist l E T n (d : ℤ)).obj
      ((scalarReductionDerivedExtension l E T n).obj M)) : Prop :=
  letI := adicPurityFiniteSheafTwist_additive l E n T d
  letI := adicPurityFiniteSheafTwist_limits l E n T d
  letI := adicPurityFiniteSheafTwist_colimits l E n T d
  (derivedScalarExtensionRestrictionAdjunction l E T n).choose.homEquiv _ _
    (g ≫ (eqToIso (adicPurityFiniteTwistPresentation l E n T d)).hom.app
      ((scalarReductionDerivedExtension l E T n).obj M)) =
    (integralSheafTwist l E T (d : ℤ)).mapDerivedCategory.map
      ((derivedScalarExtensionRestrictionAdjunction l E T n).choose.unit.app M) ≫
        (adicPurityDerivedTwistRestriction l E n T d).hom.app
          ((scalarReductionDerivedExtension l E T n).obj M)

/-- Exactly one reduction morphism has the specified root-normalized transpose.
Source: blueprint canonical twist reduction (blueprint: def-pur-adic-twist-reduction).
Proof: the scalar extension/restriction Hom correspondence is a bijection. Its inverse
sends the integral twist of the scalar-extension unit followed by the specified
restriction comparison to a unique map into the cached finite twist. Postcompose
with the inverse of adicPurityFiniteTwistPresentation. The same Hom bijection and
cancellation of this presentation isomorphism prove uniqueness. -/
theorem adicPurityTwistReduction_existsUnique (d : ℕ)
    (M : DerivedCategory (scalarReductionSource l E T)) :
    ∃! g : (scalarReductionDerivedExtension l E T n).obj
      ((integralSheafTwist l E T (d : ℤ)).mapDerivedCategory.obj M) ⟶
    (finiteComplexTwist l E T n (d : ℤ)).obj
      ((scalarReductionDerivedExtension l E T n).obj M),
      IsAdicPurityTwistReduction l E n T d M g := by
  sorry

/-- The canonical twist reduction, uniquely specified by its complete transpose equation.
Source: blueprint coefficient twists (blueprint: def-pur-adic-twist-reduction). -/
def adicPurityTwistReduction (d : ℕ) (M : DerivedCategory (scalarReductionSource l E T)) :=
  (adicPurityTwistReduction_existsUnique l E n T d M).exists.choose

end TwistReduction

end WeilConjectures
