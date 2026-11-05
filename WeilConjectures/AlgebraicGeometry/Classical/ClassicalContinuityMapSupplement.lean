/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Continuity maps and classical pro-étale sheaves

Source: current blueprint, sec-proetale-coefficients/sk-def-pe-classical-definition,
`sk-def-pe-classical-definition-continuity-map.md`, clauses 1--4 and final paragraph
(blueprint: det-pe-classical-definition-continuity-map).

The index categories and section values live in the common larger universe `u + 1`.
Module coefficients use the intrinsic constant-ring module category of the recorded
small pro-étale site, with the same coefficient lift as `Scheme.proEtaleDerivedCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Modules

variable {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]

variable (F : ringedSiteModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} Λ)))))

end Modules

end AlgebraicGeometry.ProEtale
