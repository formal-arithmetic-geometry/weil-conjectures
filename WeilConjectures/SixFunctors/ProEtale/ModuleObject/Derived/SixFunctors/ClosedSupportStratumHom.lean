/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteProjectiveDualizable
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Global derived Hom out of a stratum extension

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-formal-closed-support-stratum-hom.md
(blueprint: det-lem-formal-closed-support-stratum-hom).

The global Hom functor is derived into abelian groups, rather than internal Hom.
All coefficient modules and derived categories are the existing module-object categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Global RHom from a module in degree zero, computed by Hom into a K-injective
representative. This is the global-sections Hom complex of the source statement:
its degree n is Hom(M,I^n), and its differential is postcomposition with d_I.
Source: blueprint stratum Hom lemma, definition of global RHom
(blueprint: det-lem-formal-closed-support-stratum-hom). -/
noncomputable def stratumGlobalRHom (X : Scheme.{u}) (M : supportModules Λ X) :
    DerivedCategory (supportModules Λ X) ⥤ DerivedCategory Ab.{u + 1} :=
  (preadditiveCoyoneda.obj (op M)).rightDerivedFunctor

/-- RΓ is the unbounded right derived functor of Hom from the regular coefficient module.
Source: blueprint stratum Hom lemma, definition of hypercohomology
(blueprint: det-lem-formal-closed-support-stratum-hom). -/
noncomputable def stratumRGamma (X : Scheme.{u}) :
    DerivedCategory (supportModules Λ X) ⥤ DerivedCategory Ab.{u + 1} :=
  stratumGlobalRHom Λ X (Mod.regular (condensedRingObj Λ X))

/-- The coefficient-linear internal Hom dual of L. The existing closed module tensor
represents sheaf Hom; its unit is the regular coefficient module.
Source: blueprint stratum Hom lemma, L-dual definition
(blueprint: det-lem-formal-closed-support-stratum-hom). -/
noncomputable def stratumDual (S : Scheme.{u}) (L : supportModules Λ S) : supportModules Λ S :=
  (ihom L).obj (𝟙_ (supportModules Λ S))

end AlgebraicGeometry.ProEtale.CondensedRing
