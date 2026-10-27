/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FormalClosedSupportSheaves
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.CohomologicalDimension

/-!
# Cohomology of the restricted support of an integral derived reduction

Source: blueprint `sk-lem-int-ext.proof.md`, paragraph (2), finite-reduction bullets.
(blueprint: lem-sf-integral-reduction-support-amplitude).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The restricted support of a positive derived reduction has classical prime-power
torsion cohomology in the interval `[-1,c+1]`. No source sheaf or derived dual occurs here.

Source: blueprint `sk-lem-int-ext.proof.md`, paragraph (2), first bullet;
`lem-sf-integral-stratum-reduction-ext-bound`, steps 1--2 and 5--7;
Stacks Tags 093J, 093M, 09A6 and 08J5.
(blueprint: lem-sf-integral-reduction-support-amplitude).

Proof: the completed constant quotient resolution represents the reduction by
[N -- pi^(n+1) --> N] in degrees [-1,0]. The constructible reduction criterion and
finite-coefficient comparison make its cohomology classical. It is a complex of
modules over the finite quotient, so its cohomology is prime-power torsion. Work over
that quotient ring. Exact j^* preserves the bounds and classicality. The relative cd
bound on classical torsion sheaves bounds Rj_* on heart objects in [0,c]; its finite
cohomology filtration therefore bounds Rj_*j^* of the reduction in [-1,c]. The qcqs
comparison makes that direct image classical. The support triangle gives the fibre
bounds [-1,c+1]: below -1 both adjacent terms vanish, and above c+1 the preceding
direct-image cohomology and the reduction cohomology vanish. Exact inverse image
along i and v preserves the bounds, classicality and torsion. Finally restriction
from quotient coefficients to integral coefficients commutes with the support
adjunction and its unit, and with both inverse images, so this is the stated actual
integral support object. The zero reduction and empty schemes satisfy the same bounds. -/
theorem integral_reduction_support_amplitude
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (S Z V : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (hAdd : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive)
    (c : ℕ)
    (hc : (c : WithTop ℕ) = relativeCohomologicalDimension l (Fact.out : l.Prime) j)
    (N : pulledBackModuleObjects (integralCoefficientRing l E) X)
    (hN : IsConstantModelConstructible (integralCoefficientRing l E) X N) (n : ℕ) :
    let K := (upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
      ((closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).rightDerivedFunctor.obj
        ((integralReductionFunctor l E X (n + 1)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)))
    (∀ q : ℤ, q < -1 ∨ (c : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    (∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
