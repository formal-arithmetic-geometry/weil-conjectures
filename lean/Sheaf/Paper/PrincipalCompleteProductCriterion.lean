/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Algebra.Homology.RegularPrincipalCompletionFiber
public import Sheaf.Paper.CountableScalarDifference
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Derived principal completeness as a product differential criterion

Source: Bhatt--Scholze, Definition 3.4.1, Lemma 3.4.12 and Proposition 3.1.11.
(blueprint: lem-sfb-principal-complete-product-criterion).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PrincipalQuotientCompletion.Model

/-- A module is complete for the canonical quotient-completion unit precisely when
`1 - scalar shift` on its countable power is invertible.

Source: Bhatt--Scholze, Definition 3.4.1, Lemma 3.4.12, proof of (1) iff (2),
printed pp.20--23, and Proposition 3.1.11, printed p.17.
(blueprint: lem-sfb-principal-complete-product-criterion).

Proof: Apply regularPrincipalCompletionFiber to the regular parameter. The universal
property of the quotient-completion model identifies its completion functor with F:
both derive the same ordinary quotient Roos functor. On a K-flat representative,
the comparison intertwines the units by unit_computes and the two augmentation
coordinate equations. Those equations determine the augmentation chain map, since
the Roos coordinate map is an isomorphism. Naturality and a K-flat resolution extend
this unit compatibility to every derived object. Thus the fibre triangle has second
arrow the specified unit of F, up to that compatible isomorphism. The second arrow
of a distinguished triangle is invertible if and only if the first object is zero.
For the module in degree zero, the first object is the localization of the actual
repeated-scalar Roos complex. Countable products are exact on the pro-etale site,
so no product resolution changes this representative. It is the two-term complex
with the countable power of M in degrees 0 and 1 and differential minus the map
`1 - scalar shift`. Its homology objects are the kernel and cokernel of this map,
and all other homology objects are zero. The derived object is zero if and only if
these homology objects vanish. In an abelian category this is equivalent to the map
being both monic and epic, hence invertible. Signs do not affect invertibility.
Regularity is used only on the coefficient ring. -/
theorem complete_product_criterion
    (T : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology T) R))]
    (a : (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology T) R)).sections)
    (_ha : Mono (globalSectionMultiplication R a))
    (F : Model.{t + 1, t, max u (t + 1), w} R a)
    (M : ringedSiteModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology T) R)) :
    IsIso (F.unit.app ((DerivedCategory.singleFunctor _ 0).obj M)) ↔
      IsIso ((CountableScalarDifference.difference
        (PrincipalCompletionFiber.scalar R a)).app M) := by sorry

end CategoryTheory.PrincipalQuotientCompletion.Model
