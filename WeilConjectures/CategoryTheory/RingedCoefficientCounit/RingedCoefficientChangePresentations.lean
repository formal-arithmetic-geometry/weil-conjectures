/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations

/-!
# Coefficient changes of normalized counit diagrams

Source: Stacks, Tags 03D7, 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations).
Ordinary maps are fixed on sections; derived maps are fixed by localization and
K-flat/K-injective representative equations. No counit identity is a field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r w u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace CategoryTheory.RingedCoefficientCounit

/-- One component of localized coefficient restriction and its composition comparisons.
Source: Stacks 03D7 and 07A6
(blueprint: def-pur-ringed-coefficient-change-presentations).
The categories are parameters, so recursors do not expand the ringed-site realization. -/
structure LocalizedRestrictionChangeData
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w} B]
    {B' : Type u₂} [Category.{v₂} B'] [Abelian B'] [HasDerivedCategory.{w} B']
    {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w} E]
    (V : B' ⥤ B) [V.Additive] (U : B ⥤ E) [U.Additive]
    (U' : B' ⥤ E) [U'.Additive]
    (X : DerivedCategory B ⥤ DerivedCategory E)
    (X' : DerivedCategory B' ⥤ DerivedCategory E) where
  v : DerivedCategory B' ⥤ DerivedCategory B
  factors : DerivedCategory.Q ⋙ v ≅ onComplex V ⋙ DerivedCategory.Q
  ordinary : V ⋙ U ≅ U'
  rho : v ⋙ X ≅ X'

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  {A : CommRingCat.{r}} {RX RI : Sheaf JX CommRingCat.{r}}
  {RY : Sheaf JY CommRingCat.{r}}
  {inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r)}
  {direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)} {geom : inverse ⊣ direct}
  {IA : SheafOfModules.AlgebraicInverseImage inverse (constantRing JY A) (constantRing JX A)}
  {IR : SheafOfModules.AlgebraicInverseImage inverse RY RI} {c : RI ⟶ RX}

variable [IA.modules.Additive]
  {aX : constantRing JX A ⟶ RX} {aY : constantRing JY A ⟶ RY}
  {aI : constantRing JX A ⟶ RI}
  {o : OrdinaryPresentation direct geom IA IR c aX aY aI}
  [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
  [HasDerivedCategory.{w} (modules (constantRing JX A))]
  [HasDerivedCategory.{w} (modules (constantRing JY A))]

variable {RX' RI' : Sheaf JX CommRingCat.{r}} {RY' : Sheaf JY CommRingCat.{r}}
  {IR' : SheafOfModules.AlgebraicInverseImage inverse RY' RI'} {c' : RI' ⟶ RX'}
  {aX' : constantRing JX A ⟶ RX'} {aY' : constantRing JY A ⟶ RY'}
  {aI' : constantRing JX A ⟶ RI'}
  {o' : OrdinaryPresentation direct geom IA IR' c' aX' aY' aI'}
  [HasDerivedCategory.{w} (modules RX')] [HasDerivedCategory.{w} (modules RY')]

/-- Localized coefficient restrictions and their composition comparison data.
Source: Stacks 03D7 and 07A6
(blueprint: def-pur-ringed-coefficient-change-presentations).
Normalization proofs are stored separately to keep generated recursors small. -/
structure CoefficientRestrictionChangeData
    (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') where
  localX : LocalizedRestrictionChangeData (restriction bX) (restriction aX)
    (restriction aX') p.x p'.x
  localY : LocalizedRestrictionChangeData (restriction bY) (restriction aY)
    (restriction aY') p.y p'.y

/-- The explicit compatibility and localization equations for coefficient restrictions.
Source: Stacks 03D7 and 07A6
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
def CoefficientRestrictionChangeNormalized
    (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    (s : CoefficientRestrictionChangeData p p' bX bY) : Prop :=
  (aX ≫ bX = aX') ∧
  (aY ≫ bY = aY') ∧
  (aI ≫ bI = aI') ∧
  (c ≫ bX = bI ≫ c') ∧
  (IR.ringUnderlying.hom ≫
    (sheafCompose JX (forget CommRingCat.{r})).map bI =
  inverse.map ((sheafCompose JY (forget CommRingCat.{r})).map bY) ≫
    IR'.ringUnderlying.hom) ∧
  (∀ M,
  (underlying (constantRing JX A)).map (s.localX.ordinary.hom.app M) = 𝟙 _) ∧
  (∀ M,
  (underlying (constantRing JY A)).map (s.localY.ordinary.hom.app M) = 𝟙 _) ∧
  (∀ I : CochainComplex (modules RX') ℤ,
  s.localX.rho.hom.app (DerivedCategory.Q.obj I) ≫ p'.xFactors.hom.app I =
    p.x.map (s.localX.factors.hom.app I) ≫
      p.xFactors.hom.app ((onComplex (restriction bX)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.localX.ordinary.hom
          (ComplexShape.up ℤ)).app I)) ∧
  (∀ I : CochainComplex (modules RY') ℤ,
  s.localY.rho.hom.app (DerivedCategory.Q.obj I) ≫ p'.yFactors.hom.app I =
    p.y.map (s.localY.factors.hom.app I) ≫
      p.yFactors.hom.app ((onComplex (restriction bY)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.localY.ordinary.hom
          (ComplexShape.up ℤ)).app I))

/-- Localized restriction together with all its coefficient normalization equations.
Source: Stacks 03D7 and 07A6
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
structure CoefficientRestrictionChange (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    extends CoefficientRestrictionChangeData p p' bX bY where
  normalized : CoefficientRestrictionChangeNormalized p p' bX bY bI
    toCoefficientRestrictionChangeData

/-- The direct-image comparison, normalized by the K-injective composition equation.
Source: Stacks 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
structure CoefficientDirectChangeData (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    (s : CoefficientRestrictionChange p p' bX bY bI) where
  ordinaryBeta : o'.pushR ⋙ restriction bY ≅ restriction bX ⋙ o.pushR
  beta : p'.r.right ⋙ s.localY.v ≅ s.localX.v ⋙ p.r.right

/-- Explicit representative normalization equations for `CoefficientDirectChangeData`.
Source: Stacks 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
def CoefficientDirectChangeNormalized (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    (s : CoefficientRestrictionChange p p' bX bY bI)
    (d : CoefficientDirectChangeData p p' bX bY bI s) : Prop :=
  (∀ M,
  (underlying RY).map (d.ordinaryBeta.hom.app M) ≫
    o.pushRUnderlying.hom.app ((restriction bX).obj M) = o'.pushRUnderlying.hom.app M) ∧
  (∀ (I : CochainComplex (modules RX') ℤ), I.IsKInjective →
  ∀ (T : CochainComplex (modules RX) ℤ), T.IsKInjective →
  ∀ (j : (onComplex (restriction bX)).obj I ⟶ T), ∀ [QuasiIso j],
    s.localY.factors.inv.app ((onComplex o'.pushR).obj I) ≫ s.localY.v.map (p'.r.eta.app I) ≫
        d.beta.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d.ordinaryBeta.hom
        (ComplexShape.up ℤ)).app I) ≫
        DerivedCategory.Q.map ((onComplex o.pushR).map j) ≫ p.r.eta.app T ≫
          p.r.right.map (inv (DerivedCategory.Q.map j) ≫ s.localX.factors.inv.app I))

/-- The comparison data together with their explicit normalization equations.
Source: Stacks 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
structure CoefficientDirectChange (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    (s : CoefficientRestrictionChange p p' bX bY bI)
    extends CoefficientDirectChangeData p p' bX bY bI s where
  normalized : CoefficientDirectChangeNormalized p p' bX bY bI s toCoefficientDirectChangeData

/-- The canonical identifications between two constant-coefficient derived presentations.
Source: Stacks 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
structure ConstantDerivedChangeData (p : DerivedPresentation o) (p' : DerivedPresentation o') where
  alpha : p.a.left ≅ p'.a.left
  ordinaryGamma : o'.pushA ≅ o.pushA
  gamma : p'.a.right ≅ p.a.right

/-- Explicit representative normalization equations for `ConstantDerivedChangeData`.
Source: Stacks 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
def ConstantDerivedChangeNormalized (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (d : ConstantDerivedChangeData p p') : Prop :=
  (∀ I : CochainComplex (modules (constantRing JY A)) ℤ,
  d.alpha.hom.app (DerivedCategory.Q.obj I) ≫ p'.a.epsilon.app I = p.a.epsilon.app I) ∧
  (∀ M,
  (underlying (constantRing JY A)).map (d.ordinaryGamma.hom.app M) ≫
    o.pushAUnderlying.hom.app M = o'.pushAUnderlying.hom.app M) ∧
  (∀ I : CochainComplex (modules (constantRing JX A)) ℤ,
  I.IsKInjective → p'.a.eta.app I ≫ d.gamma.hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d.ordinaryGamma.hom
      (ComplexShape.up ℤ)).app I) ≫ p.a.eta.app I)

/-- The comparison data together with their explicit normalization equations.
Source: Stacks 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
structure ConstantDerivedChange (p : DerivedPresentation o) (p' : DerivedPresentation o')
    extends ConstantDerivedChangeData p p' where
  normalized : ConstantDerivedChangeNormalized p p' toConstantDerivedChangeData

/-- Canonical comparisons for a coefficient map, with pullback map the adjoint mate.
Source: Stacks 03D7, 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations).
No coefficient-naturality equation is an input field. -/
structure CoefficientChangeData (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI') where
  restrictions : CoefficientRestrictionChange p p' bX bY bI
  direct : CoefficientDirectChange p p' bX bY bI restrictions
  constants : ConstantDerivedChange p p'
  sigma : restrictions.localY.v ⋙ p.r.left ⟶ p'.r.left ⋙ restrictions.localX.v

/-- The pullback comparison is the specified adjoint mate.
Source: Stacks 03D7 and 07A6
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
def CoefficientChangeNormalized (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    (d : CoefficientChangeData p p' bX bY bI) : Prop :=
  (∀ M : DerivedCategory (modules RY'),
  d.sigma.app M = (p.r.adj.homEquiv _ _).symm
    (d.restrictions.localY.v.map (p'.r.adj.unit.app M) ≫ d.direct.beta.hom.app (p'.r.left.obj M)))

/-- Canonical coefficient comparisons together with their adjoint-mate equation.
Source: Stacks 03D7, 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations).
The counit and coefficient-naturality squares are not fields. -/
structure CoefficientChange (p : DerivedPresentation o) (p' : DerivedPresentation o')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    extends CoefficientChangeData p p' bX bY bI where
  normalized : CoefficientChangeNormalized p p' bX bY bI toCoefficientChangeData

/-- The two actual coefficient-naturality squares, for tau and kappa respectively.
Source: Stacks 03D7, 07A6 and 0D6E
(blueprint: def-pur-ringed-coefficient-change-presentations). -/
def CoefficientChange.IsNatural {p : DerivedPresentation o} {p' : DerivedPresentation o'}
    {bX : RX ⟶ RX'} {bY : RY ⟶ RY'} {bI : RI ⟶ RI'}
    (m : CoefficientChange p p' bX bY bI) : Prop :=
  (∀ M : DerivedCategory (modules RY'),
    p.a.left.map (m.restrictions.localY.rho.hom.app M) ≫
        m.constants.alpha.hom.app (p'.y.obj M) ≫ p'.tau.app M =
      p.tau.app (m.restrictions.localY.v.obj M) ≫ p.x.map (m.sigma.app M) ≫
        m.restrictions.localX.rho.hom.app (p'.r.left.obj M)) ∧
  (∀ K : DerivedCategory (modules RX'),
    p.y.map (m.direct.beta.hom.app K) ≫ p.kappa.hom.app (m.restrictions.localX.v.obj K) ≫
        p.a.right.map (m.restrictions.localX.rho.hom.app K) =
      m.restrictions.localY.rho.hom.app (p'.r.right.obj K) ≫ p'.kappa.hom.app K ≫
        m.constants.gamma.hom.app (p'.x.obj K))

end CategoryTheory.RingedCoefficientCounit
