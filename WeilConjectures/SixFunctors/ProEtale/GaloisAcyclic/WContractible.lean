/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections

/-!
# Cohomology over w-contractible affine schemes and acyclicity for direct images

Let `Λ` be a ring. Sections over a weakly contractible object `W` of the small pro-étale site
form an exact functor on pro-étale sheaves of `Λ`-modules, so the higher derived sections over
`W` vanish
(`AlgebraicGeometry.ProEtale.isZero_rightDerived_sectionsFunctor_of_isWeaklyContractible`).
Through the comparison of pro-étale and étale cohomology, the higher étale cohomology of an
affine scheme with w-contractible ring of global sections vanishes
(`AlgebraicGeometry.ProEtale.isZero_rightDerived_etaleSectionsFunctor_of_isWContractibleRing`).

Since the objects of the pro-étale site of `V` whose underlying scheme is the spectrum of a
w-contractible ring cover the site and are weakly contractible, a pro-étale sheaf `G` on `U` is
acyclic for the direct image along `f : U ⟶ V` as soon as its higher derived sections over the
base changes `U ×_V W` of these objects vanish
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isWContractibleRing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [Ring Λ]

end AlgebraicGeometry.ProEtale
