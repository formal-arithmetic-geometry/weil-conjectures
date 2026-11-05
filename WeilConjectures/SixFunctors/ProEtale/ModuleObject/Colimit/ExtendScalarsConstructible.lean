/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-!
# Extension of scalars preserves constructibility

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `X` a scheme. The extension of
scalars `Λ'_X ⊗_{Λ_X} -` along `a_X : Λ_X ⟶ Λ'_X`

* preserves finitely presented module objects, being right exact and sending `Λ_X` to `Λ'_X`;
* commutes with the pullbacks of module objects (the underived (Pull),
  `ProEtale.CondensedRing.pullIso`), hence preserves pro-étale local finite presentation
  (`ProEtale.CondensedRing.IsLocallyFinitelyPresented.extendScalars`) and constructibility
  (`ProEtale.CondensedRing.IsConstructibleModuleObject.extendScalars`), along the same covers and
  stratifications.

If moreover `Λ'_X` is flat over `Λ_X`, i.e. the extension of scalars is exact, its left derived
functor is computed termwise and commutes with the cohomology sheaves, so it preserves bounded
constructible complexes (`ProEtale.CondensedRing.boundedConstructible_leftDerivedExtendScalars_obj`,
blueprint `lem-sfb-extend-subfield-constructible`, `lem-sfb-extend-to-qlbar-constructible`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

end AlgebraicGeometry.ProEtale.CondensedRing
