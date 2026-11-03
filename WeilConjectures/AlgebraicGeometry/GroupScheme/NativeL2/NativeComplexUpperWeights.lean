/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed

/-! # The upper-weight formula on native condensed Weil complexes

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/sk-d-real-weights/
def-weil-complex-weights.md, upper-weight display
(blueprint: def-real-weil-complex-upper-weight).

This is the upper-weight part needed by sk-r-real-linear. It uses the maintained
strict action and the recorded native punctual predicate. It does not construct a
dualizing object or assert any lower-weight property.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Cohomology with the Weil isomorphism induced by exact pullback and K.str.
Source: latest blueprint, the cohomology-sheaf sentence before the upper-weight
formula (blueprint: def-real-weil-complex-upper-weight). -/
def complexWeilCohomology
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀))) (n : ℤ) :
    WeilModule D l X₀ :=
  IsoAlgebra.mk ((DerivedCategory.homologyFunctor _ n).obj K.carrier)
    (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).mapDerivedCategoryHomologyFunctorIso n).app K.carrier ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso K.str)

/-- In degree n the canonical Weil cohomology sheaf has mixed bound w+n.
The formula is defined in the ambient derived category and restricts to precisely
Wt_{iota,≤w} on bounded constructible Weil complexes.
Source: latest blueprint, upper-weight display
(blueprint: def-real-weil-complex-upper-weight). -/
def complexMixedOfWeightsAtMost
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀)))
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∀ n : ℤ, Mixed D l X₀ (complexWeilCohomology D l X₀ K n) iota (w + (n : ℝ))

end WeilConjectures.NativeL2
