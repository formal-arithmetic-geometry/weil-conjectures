/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedContinuitySections
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage

/-!
# Continuity of pro-etale cohomology

Source: Weil conjectures blueprint, literature/blueprint/latest/blueprint/,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity/_section.md and its proof
(blueprint: sk-cor-pe-bounded-continuity).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

/-- Filtered colimits of complexes with one common lower bound commute with
hypercohomology on qcqs pro-etale objects, and with higher direct images under qcqs
scheme morphisms. Complex colimits are termwise colimits of module sheaves.
The first map is the canonical `colimit.post`. The second is the map from the
colimit of higher direct images to the higher direct image of the termwise colimit,
induced by applying localization and higher direct image to its cocone.

Source: Weil conjectures blueprint, literature/blueprint/latest/blueprint/,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity/_section.md
(blueprint: sk-cor-pe-bounded-continuity).

Proof:
1. For every qcqs object U and integer q, apply
   det-pe-bounded-continuity-sections, namely
   `isIso_ringHypercohomology_colimitPost X R U K a hK q`. The coefficient sheaf,
   filtered diagram and strict common lower bound are exactly those in the hypothesis.
2. For every qcqs morphism f from X and integer q, apply
   det-pe-bounded-continuity-direct-image, namely
   `boundedContinuityDirectImage f R K a hK q`. Its canonical map uses the same
   termwise complex colimit and is an isomorphism of module sheaves on the target
   pro-etale site. These two conclusions give the conjunction. -/
theorem boundedContinuity (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (ringedSiteModules.{u + 1} R) ℤ)
    (a : ℤ) (hK : ∀ (i : I) (b : ℤ), b < a → IsZero ((K.obj i).X b)) :
    (∀ U : X.ProEt, CompactSpace U.left → QuasiSeparatedSpace U.left →
      ∀ q : ℤ, IsIso (colimit.post K (ringHypercohomology X R U q))) ∧
    (∀ (Y : Scheme.{u}) (f : X ⟶ Y), QuasiCompact f → QuasiSeparated f →
      ∀ q : ℤ, IsIso (colimit.desc
        ((K ⋙ DerivedCategory.Q) ⋙ ringHigherDirectImage f R q)
        ((ringHigherDirectImage f R q).mapCocone
          (DerivedCategory.Q.mapCocone (colimit.cocone K))))) := by
  constructor
  · intro U hcompact hseparated q
    letI : CompactSpace U.left := hcompact
    letI : QuasiSeparatedSpace U.left := hseparated
    exact isIso_ringHypercohomology_colimitPost X R U K a hK q
  · intro Y f hquasiCompact hquasiSeparated q
    letI : QuasiCompact f := hquasiCompact
    letI : QuasiSeparated f := hquasiSeparated
    exact boundedContinuityDirectImage f R K a hK q

end AlgebraicGeometry.Scheme.ProEt
