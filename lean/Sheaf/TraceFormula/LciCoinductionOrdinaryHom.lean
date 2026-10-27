/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.TraceFormula.LciKoszulDualityData
public import Sheaf.AlgebraicGeometry.SheafExt
public import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # The canonical underlying Hom comparison for a Koszul chart

Source: Stacks Project, Tags 0BUZ, 0BV1 and 0A95
(blueprint: def-trf-lci-coinduction-ordinary-hom).
The comparison is fixed on K-injective representatives by the ordinary evaluation-normalized
coinduction comparison and projection onto source degree zero in the Hom complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

section Single
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A natural single-source comparison with its actual product-projection formula.
Source: Stacks 0A8X (blueprint: def-trf-lci-coinduction-ordinary-hom). -/
structure SingleHomComparison (R : Sheaf J CommRingCat.{u})
    (A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    [((SheafOfModules.homFunctor R).obj (op A)).Additive] where
  iso : (homComplexFunctor (R := R)).obj
      (op ((CochainComplex.singleFunctor _ 0).obj A)) ≅
        ((SheafOfModules.homFunctor R).obj (op A)).mapHomologicalComplex (.up ℤ)
  projection : ∀ (I : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
      (n : ℤ),
    (iso.hom.app I).f n =
      homComplexπ (R := R) ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n)

/-- The single-source projection is a natural chain isomorphism, with its exact formula.
Source: Stacks 0A8X (blueprint: def-trf-lci-coinduction-ordinary-hom).
Proof: all product factors except source degree zero are Hom(0,-)=0. The product lift
inserts the degree-zero factor and zeros elsewhere, giving the inverse. The source
has zero differential, so the Hom differential formula proves the chain-map identity.
The map formula proves naturality. Extensionality of natural transformations and
complex maps proves uniqueness of an isomorphism with these components. -/
theorem exists_singleHomComparison (R : Sheaf J CommRingCat.{u})
    (A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    [((SheafOfModules.homFunctor R).obj (op A)).Additive] :
    Nonempty (SingleHomComparison R A) := by
  sorry

/-- The canonical projection isomorphism, selected with its determining formula.
Source: Stacks 0A8X (blueprint: def-trf-lci-coinduction-ordinary-hom). -/
@[no_expose] def singleHomIso (R : Sheaf J CommRingCat.{u})
    (A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    [((SheafOfModules.homFunctor R).obj (op A)).Additive] :=
  (Classical.choice (exists_singleHomComparison R A)).iso

end Single

variable [∀ Z : RingedSpace.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]

attribute [local instance] LciKoszulDuality.schemeDerived LciKoszulDuality.imageRingDerived
  LciKoszulDuality.imageRingInjectives

/-- The quotient algebra regarded as an ambient module.
Source: Stacks 0BUZ (blueprint: def-trf-lci-coinduction-ordinary-hom). -/
def LciKoszulDuality.Chart.quotientModule {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) : T.chart.P.Modules :=
  T.scalars.obj (SheafOfModules.unit (moduleRings (directImageAlgebraSpace T.chart.i)))

/-- The ordinary comparison together with its evaluation-at-one normalization.
Source: Stacks 0BUZ (blueprint: def-trf-lci-coinduction-ordinary-hom). -/
structure OrdinaryHomComparison {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) where
  iso : polynomialChartCoinduction T.chart.i ⋙ T.scalars ≅
    (SheafOfModules.homFunctor T.chart.P.sheaf).obj (op T.quotientModule)
  evaluation : ∀ (F : T.chart.P.Modules) (V : T.chart.P.Opens)
      (φ : ((polynomialChartCoinduction T.chart.i).obj F).val.obj (op V))
      (a : (moduleRings (directImageAlgebraSpace T.chart.i)).obj.obj (op V)),
    ((((iso.hom.app F).val.app (op V)).hom φ).app (op (Over.mk (𝟙 V)))) a =
      (((polynomialChartOrdinaryAdjunction T.chart.i).counit.app F).val.app (op V)).hom
        (a • φ)

/-- The existing coinduction comparison satisfies its uniquely determining evaluation formula.
Source: Stacks 0BUZ (blueprint: def-trf-lci-coinduction-ordinary-hom).
Proof: the ordinary coinduction presentation supplies an isomorphism with multiplication
by precomposition and counit evaluation at one. Its value on a is the counit of a times
the section, giving the formula. That formula determines every local component by
restriction to each smaller open, so any two such isomorphisms are equal. -/
theorem exists_ordinaryHomComparison {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) : Nonempty (OrdinaryHomComparison T) := by
  sorry

/-- The existing ordinary comparison, selected with its determining evaluation formula.
Source: Stacks 0BUZ (blueprint: def-trf-lci-coinduction-ordinary-hom). -/
@[no_expose] def LciKoszulDuality.Chart.ordinaryHomComparison
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : LciKoszulDuality.Chart f d) :=
  (Classical.choice (exists_ordinaryHomComparison T)).iso


end AlgebraicGeometry
