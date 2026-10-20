/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U6
-/
module

public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses

/-! # Ordinary Hom calculations for a bounded finite-free retract complex

Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ,
lemma-Rhom-strictly-perfect and lemma-dual-perfect-complex.
(blueprint: lem-sfb-ringed-site-strict-perfect-hom).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Ordinary duality for a bounded complex of finite-free retracts.
Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ,
lemma-Rhom-strictly-perfect and the strictly perfect case of lemma-dual-perfect-complex.
(blueprint: lem-sfb-ringed-site-strict-perfect-hom).

Proof: split each term into a finite power of the coefficient sheaf. Dualizing
its inclusion and projection gives a splitting for its dual. The dual basis
identity gives mutually inverse termwise bidual and tensor-Hom evaluations.
The Hom functor of a term is a retract of a finite-power functor, hence exact.
The bounded-exact-term Hom lemma applied to the resolution augmentation gives
both ordinary-to-derived quasi-isomorphisms. The dual complex has term
(E^(-q))^dual in degree q, differential (-1)^(q+1) times the dual differential,
and bounds [-b,-a]. Its terms remain finite-free retracts. Under the Hom-product
projections, signed ordinary biduality is
(-1)^i times termwise biduality, hence invertible. For an arbitrary F the
ordinary evaluation in degree n is the finite direct sum over p+q=n of
F^p tensor (E^(-q))^dual to Hom(E^(-q),F^p). Each summand is invertible by
the dual basis identity. The two differentials are d_F f-(-1)^n f d_E,
so these degreewise inverses give an inverse chain map. The argument includes
zero ranks, the zero ring, odd shifts, and unbounded F. -/
theorem ringedSiteStrictPerfectHom
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    let D := homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (D.X n)) ∧
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ D) ∧
    (∀ F, QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) ∧
    QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 D)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app
        (ringedSiteDualityUnitComplex.{c, v, r} J R))) ∧
    IsIso (ringedSiteOrdinaryBidual.{c, v, r} J R E) ∧
    (∀ F, IsIso (ringedSiteOrdinaryEvaluation.{c, v, r} J R E F)) := by
  sorry

end CategoryTheory
