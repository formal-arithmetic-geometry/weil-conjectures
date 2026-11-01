/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Finite direct image preserves ordinary scalar-extension units

Source: Stacks Project, Tag 03QP, finite direct image and its finite stalk formula.
(blueprint: lem-asd-finite-ordinary-scalar-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private noncomputable abbrev moduleScalar
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A) :
    ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} A :=
  ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ

private noncomputable abbrev scalar {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (moduleScalar φ)

end AlgebraicGeometry.Etale
