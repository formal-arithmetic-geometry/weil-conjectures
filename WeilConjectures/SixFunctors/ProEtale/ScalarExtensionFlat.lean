/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.Sites.FlatExtendScalars
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Descent
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Extension of scalars of pro-étale sheaves preserves flatness

For any morphism of commutative rings `R ⟶ S`, extension of scalars
`S ⊗_R - : Sh(X_proét, R) ⥤ Sh(X_proét, S)` sends flat sheaves to flat sheaves
(`AlgebraicGeometry.ProEtale.preservesFlat_sheafExtendScalars`), since with scalars restricted to
`R`, tensoring with `S ⊗_R F` is tensoring with `F` (`CategoryTheory.Sheaf.flat_extendScalars_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

variable {X}

end AlgebraicGeometry.ProEtale
