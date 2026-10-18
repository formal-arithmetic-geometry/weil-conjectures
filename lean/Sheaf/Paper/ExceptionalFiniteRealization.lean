/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.IntegralExceptionalInverseImage
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Finite realization of the strict exceptional adjunction
Source: blueprint def-weil-exceptional-inverse-image. All changes of quotient-ring
presentation act identically on sections. Derived comparisons retain the universal
right-derived unit, and exceptional comparisons are adjunction mates.
(blueprint: def-pur-adic-etale-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual quotient ring in the lifted integer presentation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
abbrev integralExceptionalQuotientRing (n : ℕ) :=
  integralExceptionalIntegers l E ⧸
    (Ideal.span ({integralExceptionalUniformizer l E} :
      Set (integralExceptionalIntegers l E))) ^ (n + 1)

/-- Forgetting commutativity commutes with etale sheafification.
Source: Stacks 00W1 (blueprint: def-pur-adic-etale-realization).
Proof: the forgetful functor preserves the finite limits and filtered colimits used
by the covering-compatible-family construction of sheafification. Local equality
is unchanged, giving the same associated ring sheaf in both constructions. -/
theorem integralExceptionalEtaleForget (W : Scheme.{u}) :
    W.smallEtaleTopology.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  sorry

/-- Ordinary finite realization on the etale site: forget the locally constant scalar
sections to constant scalars and restrict along the explicit quotient-ring equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalEtaleRealization (W : Scheme.{u}) (n : ℕ) :
    strictEtaleLevel W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) n ⥤
    Sheaf W.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  letI := integralExceptionalEtaleForget W
  SheafOfModules.restrictScalars
      ((constantCommuteCompose W.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv ⋙
    constantRingModuleRestriction W.smallEtaleTopology (integralExceptionalQuotientRing l E n) ⋙
      sheafCompose W.smallEtaleTopology
        (ModuleCat.restrictScalars (integralExceptionalQuotient l E n).symm.toRingHom)

/-- The finite realization is an exact additive equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization).
Proof: constant-ring restriction is the equivalence of locally constant scalar actions.Restriction
 along a ring equivalence is an equivalence with inverse the opposite scalar
restriction. All maps leave the underlying abelian sheaves unchanged, hence preserve
addition, kernels and cokernels. -/
theorem integralExceptionalEtaleRealization_properties (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalEtaleRealization l E W n).IsEquivalence ∧
      (integralExceptionalEtaleRealization l E W n).Additive ∧
      PreservesFiniteLimits (integralExceptionalEtaleRealization l E W n) ∧
      PreservesFiniteColimits (integralExceptionalEtaleRealization l E W n) := by
  sorry

/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_equivalence (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalEtaleRealization l E W n).IsEquivalence :=
  (integralExceptionalEtaleRealization_properties l E W n).1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_additive (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalEtaleRealization l E W n).Additive :=
  (integralExceptionalEtaleRealization_properties l E W n).2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (integralExceptionalEtaleRealization l E W n) :=
  (integralExceptionalEtaleRealization_properties l E W n).2.2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (integralExceptionalEtaleRealization l E W n) :=
  (integralExceptionalEtaleRealization_properties l E W n).2.2.2

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (A : StrictEtaleOrdinaryImage (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) g)

/-- Direct-image realization, uniquely determined by the given set-sheaf comparison
on every section. This fixes its scalar normalization, not just its isomorphism class.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization).
Proof: both direct images evaluate on the same base-change etale object. The specified
rightUnderlying map identifies their sections and commutes with restriction. Constants
have the same image under the explicit quotient equivalence, so the map is linear. Its
underlying bijection gives an inverse; faithful forgetting proves uniqueness. -/
theorem integralExceptionalEtaleRight_existsUnique (n : ℕ) :
    ∃! e : A.right n ⋙ integralExceptionalEtaleRealization l E Y n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g,
      ∀ (M : strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) (W : Y.Etaleᵒᵖ)
        (x : ((A.right n).obj M).val.obj W),
        (e.hom.app M).hom.app W x =
          ((A.rightUnderlying n).hom.app M).hom.app W x := by
  sorry

/-- The actual ordinary direct-image realization, fixed on all underlying sections.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalEtaleRight (n : ℕ) :
    A.right n ⋙ integralExceptionalEtaleRealization l E Y n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g :=
  (integralExceptionalEtaleRight_existsUnique l E g A n).choose

/-- Inverse-image realization, fixed by the actual Hom transposes and the normalized
ordinary right-image comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization).
Proof: transport both adjunctions along the finite realization equivalences. The
normalized right comparison induces the comparison of their left adjoints. The
adjunction bijections force precisely the displayed equation and make it unique. -/
theorem integralExceptionalEtaleInverse_existsUnique (n : ℕ) :
    ∃! e : (A.lift n).modules ⋙ integralExceptionalEtaleRealization l E X n ≅
      integralExceptionalEtaleRealization l E Y n ⋙
        Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g,
      ∀ (M : strictEtaleLevel Y (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (N : strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (h : (A.lift n).modules.obj M ⟶ N),
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g).homEquiv _ _
          (e.inv.app M ≫ (integralExceptionalEtaleRealization l E X n).map h) =
        (integralExceptionalEtaleRealization l E Y n).map
          ((A.levelAdj n).homEquiv _ _ h) ≫
            (integralExceptionalEtaleRight l E g A n).hom.app N := by
  sorry

/-- The ordinary inverse comparison specified by the full adjunction equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalEtaleInverse (n : ℕ) :
    (A.lift n).modules ⋙ integralExceptionalEtaleRealization l E X n ≅
      integralExceptionalEtaleRealization l E Y n ⋙
        Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g :=
  (integralExceptionalEtaleInverse_existsUnique l E g A n).choose
/-- The universal right-derived unit on cochain complexes, retaining its actual map.
Source: blueprint derived exceptional construction
(blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalFixedRightUnit (n : ℕ)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    DerivedCategory.Q.obj
      (((Etale.lowerStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).mapHomologicalComplex
           (.up ℤ)).obj J) ⟶
    (Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor.obj
         (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctorUnit.app
         ((HomotopyCategory.quotient _ _).obj J) ≫
    (Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor.map
         ((DerivedCategory.quotientCompQhIso _).inv.app J)

/-- The full right-derived-unit square on every cochain representative.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-etale-realization). -/
def IsIntegralExceptionalEtaleDerivedRight (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (e : B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor) :
      Prop :=
  ∀ J : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory.map
            (B.directUnit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
          (Etale.lowerStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor.map
                ((integralExceptionalEtaleRealization l E X n).mapDerivedCategoryFactors.hom.app
                   J) =
        (integralExceptionalEtaleRealization l E Y n).mapDerivedCategoryFactors.hom.app
          (((A.right n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalEtaleRight l E g A n).hom (.up ℤ)).app J) ≫
        integralExceptionalFixedRightUnit l E g n
          (((integralExceptionalEtaleRealization l E X n).mapHomologicalComplex
             (.up ℤ)).obj J)

/-- Proper derived realization is uniquely fixed by the full universal-unit square on
all cochain complexes. It agrees with the underlying section map before derivation.
Source: blueprint integral exceptional construction
(blueprint: def-pur-adic-etale-realization).
Proof: exact realization is an equivalence and thus preserves K-injective complexes.On
 such complexes the two right-derived units are isomorphisms; the square defines
the comparison from the ordinary section-normalized comparison. Resolve any complex
by a K-injective one. Universal right derivation extends the comparison uniquely and
proves the square for all complexes. Its inverse is obtained from the opposite ring
coordinate equivalence, and the two composites equal the identity by the unit square. -/
theorem integralExceptionalEtaleDerivedRight_existsUnique (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n)) :
    ∃! e : B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor,
      IsIntegralExceptionalEtaleDerivedRight l E g A n B e := by
  sorry

/-- The uniquely normalized derived right comparison, not an arbitrary natural iso.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
@[no_expose] def integralExceptionalEtaleDerivedRight (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n)) :
    B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor :=
  (integralExceptionalEtaleDerivedRight_existsUnique l E g A n B).choose

end WeilConjectures
