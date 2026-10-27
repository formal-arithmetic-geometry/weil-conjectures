/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.PointSystemRoosTransportData


/-! Derived cancellation of the strict point-system restriction square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemRoos

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] roosF

/-- Conjugating the strict whole-cone restriction square gives transport on representatives.

Source: blueprint integral-model proof (3), whole-Roos refinement step 8;
lem-trf-point-system-roos-transport proof step 3; Stacks Tag 0941.
(blueprint: lem-trf-point-system-roos-transport-representative).

Proof: put X=U(M), Y=U(G M) and let g identify G(Q M) with Q(G M). The target
realization comparison is L(g) followed by thetaA at Y. The a_model equation identifies
its composite with a as F(thetaA) followed by the inverse-image cone comparison.
The two zeta_model equations, with naturality at g, give the source and target sections
comparisons. The mapDerivedCategoryCompIso factorization identifies the resulting target
sections factor with the factor for the composite G followed by sections. The descent
formula for derivedTransport and naturality of thetaR then identify the scalar limit
transport with Q(H(u)). Apply Q to restriction_cone; multiply by kappaT on the left.
The sigma_model formula and naturality of the sections localization factor move sigmaD
past the cone comparison. Naturality of sigmaD with thetaA moves it to L(Q M).
Substitute the a_model equation. The two resulting composites agree after the invertible
target realization and sections comparisons, so cancel them. This proves only the
representative transport identity; all other data and laws are separate assertions. -/
theorem point_system_roos_transport_representative (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    (models : Models D l E) (products : Products D l E r)
    (comparisons : Comparisons D l E r)
    (hcomparisons : ComparisonLaws D l E r models products comparisons)
    (hcone : (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
        (products.kappaT M).inv ≫ comparisons.sigma.app (roosF.obj ((X D l E).obj M)) ≫
          ((T D l E).mapHomologicalComplex (.up ℤ)).map (products.kappaF M).hom ≫
          (products.kappaT (((G D l E r).mapHomologicalComplex (.up ℤ)).obj M)).hom =
        roosF.map ((PointSystemTransport.chainTransport D l E hl r hr).app M)))
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :
    (scalarLimit.{t, u} l E).map
        ((PointSystemTransport.derivedTransport D l E hl r hr).app (DerivedCategory.Q.obj M)) ≫
      (scalarLimit.{t, u} l E).map
        ((Functor.mapDerivedCategoryCompIso (G D l E r)
          (PointSystemTransport.sections D l E)).hom.app (DerivedCategory.Q.obj M)) ≫
      comparisons.zeta.hom.app
        ((G D l E r).mapDerivedCategory.obj (DerivedCategory.Q.obj M)) =
    comparisons.zeta.hom.app (DerivedCategory.Q.obj M) ≫
      comparisons.sigmaD.app ((L D l E).obj (DerivedCategory.Q.obj M)) ≫
      (T D l E).mapDerivedCategory.map
        (comparisons.a.hom.app (DerivedCategory.Q.obj M)) := by sorry

end WeilConjectures.PointSystemRoos
