/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.CategoryTheory.InternalSectionTensorComparison

/-! # Data for relabelling an integral coefficient presentation

Source: blueprint main-20261015, integral-criterion-reductions, final sentence;
Stacks Project, Tag 06YY, isomorphism-of-coefficients specialization
(blueprint: def-pe-integral-presentation-encoding).

This packages specified data, without choosing an isomorphism or an equivalence.
The forward functor is fixed to section-action followed by restriction along the
inverse ring isomorphism. The comparison theorem normalizes the ring isomorphism
against every finite quotient. No existence assertion is part of this definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Specified coefficient relabelling and its concrete section-action equivalence.
Source: Stacks 06YY; blueprint integral-criterion-reductions, final sentence
(blueprint: def-pe-integral-presentation-encoding). -/
structure Encoding where
  /-- The isomorphism from reconstructed section rings to completed coefficients. -/
  ringIso : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (AdicCompletion.ring l E X) ≅
    WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  /-- The module equivalence retaining the underlying abelian sheaves. -/
  modules : AdicCompletion.Modules l E X ≌ WeilConjectures.scalarReductionSource.{u, u} l E X
  /-- Its forward functor is the prescribed scalar relabelling. -/
  functor_eq : modules.functor =
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)).functor ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ringIso.inv)
  /-- Forward section-action preserves addition. -/
  [additive : modules.functor.Additive]
  /-- Its inverse preserves addition. -/
  [inverseAdditive : modules.inverse.Additive]

attribute [instance] Encoding.additive Encoding.inverseAdditive

/-- Termwise localization of the specified additive coefficient equivalence.
Source: Stacks 05RU and 06YY
(blueprint: def-pe-integral-presentation-encoding). -/
def Encoding.derived (A : Encoding l E X) :
    DerivedCategory.{u + 1} (AdicCompletion.Modules l E X) ≌
      DerivedCategory.{u + 2} (WeilConjectures.scalarReductionSource.{u, u} l E X) :=
  A.modules.mapDerivedCategory

end AlgebraicGeometry.ProEtale.IntegralPresentation
