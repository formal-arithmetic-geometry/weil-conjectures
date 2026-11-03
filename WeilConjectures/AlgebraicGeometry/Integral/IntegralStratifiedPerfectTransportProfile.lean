/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportDescent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport

/-! # Reductions and the uniform reduction profile along isomorphisms of coefficient data

Restriction of scalars along the completed isomorphism induced by a datum isomorphism
commutes with the finite reductions, up to the level isomorphisms, and with the constant
reductions, up to the constant quotient ring isomorphisms. Constructibility is invariant
under restriction along an isomorphism of constant finite coefficient rings.

Source: Bhatt--Scholze, Definition 6.5.1 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

private local instance (priority := 100000) fixedSmall' (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} T.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _

private noncomputable local instance (priority := 100000) fixedSheafify'
    (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance (priority := 100000) fixedLocallyBijective'
    (T : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Derived restriction along the identity. (auxiliary; not a blueprint node). -/
def pbcDerivedRestrictIdIso {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcDerivedRestrict (𝟙 R) ≅ 𝟭 (DerivedCategory (pbcModules T R)) :=
  Functor.mapDerivedCategoryNatIso (pbcRestrictIdIso R) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Derived restriction along a ring sheaf isomorphism is an equivalence.
(auxiliary; not a blueprint node). -/
def pbcDerivedRestrictEquivalence {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (e : R ≅ S) :
    DerivedCategory (pbcModules T S) ≌ DerivedCategory (pbcModules T R) :=
  CategoryTheory.Equivalence.mk (pbcDerivedRestrict e.hom) (pbcDerivedRestrict e.inv)
    (pbcDerivedRestrictComp e.inv e.hom (𝟙 S) e.inv_hom_id ≪≫ pbcDerivedRestrictIdIso S).symm
    (pbcDerivedRestrictComp e.hom e.inv (𝟙 R) e.hom_inv_id ≪≫ pbcDerivedRestrictIdIso R)

section RingEquiv

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

/-- The level isomorphism of finite quotient coefficient sheaves.
(auxiliary; not a blueprint node). -/
abbrev AdicCoefficientDatum.levelIso (T : Scheme.{u}) (n : ℕ) :
    (pbcAdicRings T d).obj (op n) ≅ (pbcAdicRings T d').obj (op n) :=
  asIso ((d.ringSystemHom d' φ hφ T).app (op n))

/-- Finite reduction commutes with the transport of coefficient data.
(auxiliary; not a blueprint node).
Proof: both functors are left adjoints, and their right adjoints are restrictions along the
two equal composites of the completed isomorphism with the level projections. -/
def AdicCoefficientDatum.reductionTransportIso (T : Scheme.{u}) (n : ℕ) :
    d.transportDerived d' φ hφ T ⋙ pbcCompletedReduction T d' n ≅
      pbcCompletedReduction T d n ⋙ pbcDerivedRestrict (d.levelIso d' φ hφ T n).inv :=
  let ρ := d.completionIso d' φ hφ T
  let lv := d.levelIso d' φ hφ T n
  let adj₁ := (pbcDerivedRestrictEquivalence ρ.symm).toAdjunction.comp
    (pbcDerivedScalarAdjunction (pbcAdicProjection T d' n))
  let adj₂ := (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).comp
    (pbcDerivedRestrictEquivalence lv.symm).toAdjunction
  (conjugateIsoEquiv adj₂ adj₁).symm
    (pbcDerivedRestrictComp ρ.hom (pbcAdicProjection T d' n)
        (pbcAdicProjection T d n ≫ lv.hom) (d.completionIso_hom_projection d' φ hφ T n) ≪≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d n) lv.hom
        (pbcAdicProjection T d n ≫ lv.hom) rfl).symm).symm

/-- The constant quotient ring isomorphism. (auxiliary; not a blueprint node). -/
abbrev AdicCoefficientDatum.constantLevelIso (T : Scheme.{u}) (n : ℕ) :
    adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1)) ≅
      adicLisseConstantRing T (A' ⧸ d'.ideal ^ (n + 1)) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
    (d.quotientRingEquiv d' φ hφ n).toCommRingCatIso

theorem AdicCoefficientDatum.levelConstant_square (T : Scheme.{u}) (n : ℕ) :
    (pbcLevelConstantComparison T d' n).hom ≫ (d.levelIso d' φ hφ T n).inv =
      (d.constantLevelIso d' φ hφ T n).inv ≫ (pbcLevelConstantComparison T d n).hom := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  letI := d.quotientFinite
  letI := d'.quotientFinite
  exact pbcLevelConstantComparison_naturality T d d' n (d.quotientRingEquiv d' φ hφ n).toRingHom

/-- Constant reduction commutes with the transport of coefficient data.
(auxiliary; not a blueprint node). -/
def AdicCoefficientDatum.constantReductionTransportIso (T : Scheme.{u}) (n : ℕ) :
    d.transportDerived d' φ hφ T ⋙ pbcConstantReduction T d' n ≅
      pbcConstantReduction T d n ⋙
        pbcDerivedRestrict (d.constantLevelIso d' φ hφ T n).inv :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.reductionTransportIso d' φ hφ T n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (pbcDerivedRestrictComp _ _ _ (d.levelConstant_square d' φ hφ T n) ≪≫
        (pbcDerivedRestrictComp _ _ _ rfl).symm) ≪≫
    (Functor.associator _ _ _).symm

end RingEquiv

end AlgebraicGeometry.Scheme
