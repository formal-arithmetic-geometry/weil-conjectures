/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimensionFiniteField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundPadicAlgCl
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundRationalLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundUniversalHomeomorphism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundSubfield

/-!
# The uniform `Ext` bound for the `ℓ`-adic coefficient rings

Blueprints `sk-lem-uniform-constructible-ext` and `sk-lem-int-ext` (2): let `k` be a field which
is finite or separably closed, of characteristic different from `ℓ`, and `X` a separated scheme of
finite type over `k`. For the coefficient rings `𝒪_E`, `E` and `ℚ̄_ℓ`, every constructible sheaf
`C` on `X` admits `d` with `Ext^q(C, N) = 0` for `q > d` and every constructible `N`:

* `ProEtale.hasUniformConstructibleExtBound_padicIntegersRingObj_of_locallyOfFiniteType`,
* `ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_locallyOfFiniteType`,
* `ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_locallyOfFiniteType`.

The base field has finite cohomological dimension for `𝔽_E`-coefficients
(`ProEtale.hasFiniteCohomologicalDimension_residueFieldCoeff`, blueprint `sk-lem-base-field-cd`),
which gives the bound for `𝒪_E` by reduction modulo a uniformizer
(`hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension`);
the bound for `E` follows by inverting `ℓ`
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_padicIntegersRingObj`), over a
perfect base field by dévissage to lisse sheaves on connected regular schemes, which have
lattices; a separably closed base field is replaced by its algebraic closure, the base change
being a universal homeomorphism
(`ProEtale.CondensedRing.HasUniformConstructibleExtBound.of_isUniversalHomeomorphism`). The
bound for `ℚ̄_ℓ` follows from the finite subextensions
(`ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield`). Abstract finite
extensions `E` of `ℚ_ℓ` are reduced to subextensions of `ℚ̄_ℓ` by choosing an embedding
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_finiteIntermediateField`,
`ProEtale.hasUniformConstructibleExtBound_padicIntegersRingObj_of_finiteIntermediateField`).
-/

@[expose] public section

universe u

open CategoryTheory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

variable {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX]

include aX

end AlgebraicGeometry.ProEtale
