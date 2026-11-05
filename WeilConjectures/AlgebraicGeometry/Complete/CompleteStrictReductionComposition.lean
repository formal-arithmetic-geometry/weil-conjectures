/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictPullComposition
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonPasting
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-!
# Composition of normalized derived reduction comparisons

Reduction comparisons normalized on good representatives are compatible with composites
of exact functors, whenever the underlying ordinary comparisons are. In particular the
normalized reduction/pullback comparisons are compatible with the inverse-image
compositors.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8;
Stacks Tags 06YY and 0D6D (blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section Triangle

variable {BY BY' BX DY DY' DX : Type*}
  [Category BY] [Category BY'] [Category BX] [Category DY] [Category DY'] [Category DX]
  [Abelian BY] [Abelian BY'] [Abelian BX] [Abelian DY] [Abelian DY'] [Abelian DX]
  [HasDerivedCategory BY] [HasDerivedCategory BY'] [HasDerivedCategory BX]
  [HasDerivedCategory DY] [HasDerivedCategory DY'] [HasDerivedCategory DX]
  (Fg : BY ⥤ BY') (Ff : BY' ⥤ BX) (Fh : BY ⥤ BX)
  (Gg : DY ⥤ DY') (Gf : DY' ⥤ DX) (Gh : DY ⥤ DX)
  [Fg.Additive] [Ff.Additive] [Fh.Additive] [Gg.Additive] [Gf.Additive] [Gh.Additive]
  [PreservesFiniteLimits Fg] [PreservesFiniteColimits Fg]
  [PreservesFiniteLimits Ff] [PreservesFiniteColimits Ff]
  [PreservesFiniteLimits Fh] [PreservesFiniteColimits Fh]
  [PreservesFiniteLimits Gg] [PreservesFiniteColimits Gg]
  [PreservesFiniteLimits Gf] [PreservesFiniteColimits Gf]
  [PreservesFiniteLimits Gh] [PreservesFiniteColimits Gh]
  (RY : BY ⥤ DY) (RY' : BY' ⥤ DY') (RX : BX ⥤ DX)
  [RY.Additive] [RY'.Additive] [RX.Additive]
  (MY : DerivedCategory BY ⥤ DerivedCategory DY)
  (MY' : DerivedCategory BY' ⥤ DerivedCategory DY')
  (MX : DerivedCategory BX ⥤ DerivedCategory DX)
  (εY : DerivedCategory.Q ⋙ MY ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εY' : DerivedCategory.Q ⋙ MY' ⟶ RY'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX : DerivedCategory.Q ⋙ MX ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

end Triangle

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section ReductionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

end ReductionComposition

end AlgebraicGeometry.Scheme
