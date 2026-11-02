/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap

/-! # Finite-etale direct image of lisse condensed modules

Source: current blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-correction,
prop-fd-zero-extension-comparison.proof.md, Step 3 (and its degree-zero use in Step 2).
(blueprint: lem-fd-condensed-finite-etale-lisse-pushforward).

The single-degree comparison is the canonical right-derived unit, whose inverse is the
asserted derived isomorphism. The split-cover comparison is the biproduct lift of the
pullback-composition and adjunction-counit maps. No choice of an abstract isomorphism
replaces either canonical comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteFieldDatum

/-- The map on geometric fibres is the map of the existing base-change functor.
Source: current blueprint, prop-fd-zero-extension-comparison.proof.md, Steps 2--3.
(blueprint: lem-fd-condensed-finite-etale-lisse-pushforward). -/
abbrev geometricFiberMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (π₀ : X₀ ⟶ Y₀) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map π₀).left

end WeilConjectures.FiniteFieldDatum

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

attribute [local irreducible] upperStarComp upperStarLowerStarAdjunction

end

attribute [local irreducible] upperStarComp upperStarLowerStarAdjunction

end AlgebraicGeometry.ProEtale.CondensedRing
