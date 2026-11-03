/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max

/-!
# Finite Tor amplitude of locally constant perfect duals

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md,
  paragraph 2 final sentence and paragraph 3 parenthetical
  (blueprint: lem-sfb-internal-hom-dual-tor-amplitude).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- The termwise scalar extension of a coefficient complex to a pro-etale chart.
The zero-morphism preservation witness is explicit so this construction does not depend on a
file-local instance. Source: def-weil-pbc-strict-perfect-coefficient-package
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
noncomputable def scalarExtensionComplex
    {Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})}
    {U : Scheme.{u}}
    (G : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X ⥤
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ.X U))
    (hG : G.PreservesZeroMorphisms)
    (F : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) ℤ) :
    CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ.X U)) ℤ :=
  by
    letI : G.PreservesZeroMorphisms := hG
    exact (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- A finite projective module object is a retract of a finite free module object.
The maps between finite free condensed modules are matrices over `R = Λ(*)`. Thus a
retract is scalar extension of the corresponding finite projective R-module; maps between
retracts are likewise R-linear matrices. This identifies complexes of these retracts with
the termwise scalar models of the statement, including their differentials.
Source: def-pc-perfect-ring-complex and def-weil-pbc-strict-perfect-coefficient-package;
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
def FiniteProjectiveCondensedModule
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) : Prop :=
  ∃ n : ℕ, ∃ i : M ⟶ Mod.finiteFree Λ.X n,
    ∃ p : Mod.finiteFree Λ.X n ⟶ M, i ≫ p = 𝟙 M

end AlgebraicGeometry.ProEtale
