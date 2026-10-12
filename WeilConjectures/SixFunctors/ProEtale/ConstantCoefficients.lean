/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal

/-!
# Constant coefficients on the pro-étale site

Let `Λ` be a (finite) commutative ring and `T` a scheme.

* Blueprint `def-weil-pbc-proetale-modules`. The constant sheaf `Λ_{T,proét}` (the
  sheafification of `U ↦ Cont(π₀(U), Λ)`, that is, of the constant presheaf `Λ`) is the monoidal
  unit `𝟙_ (Sheaf (ProEt.topology T) (ModuleCat Λ))`; sheaves of `Λ_{T,proét}`-modules are the
  sheaves `Sheaf (Scheme.ProEt.topology T) (ModuleCat Λ)` of `Λ`-modules, an abelian
  (Grothendieck) category. The derived category `D(T_proét, Λ)` is
  `DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat Λ))`, its bounded below part is
  `DerivedCategory.Plus`, and its bounded constructible part is
  `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible` (pullbacks of bounded
  constructible étale complexes).
* Blueprint `def-weil-pbc-proetale-operations`. For `u : U ⟶ V` the module inverse image is
  `AlgebraicGeometry.ProEtale.upperStar` (the coefficient rings being constant, `u^{-1}F ⊗ Λ_U`
  is `u^{-1}F`, see below), and the derived operations with `Lu^* ⊣ Ru_*` are
  `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction` (unbounded, via K-flat and
  K-injective resolutions) and `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunctionPlus`
  (bounded below).
* Blueprint `prop-weil-pbc-proetale-constant-ring-map`:
  `AlgebraicGeometry.ProEtale.upperStarConstantIso`, the structure map `u^{-1}Λ_V ⟶ Λ_U` is an
  isomorphism.
* Blueprint `prop-weil-pbc-proetale-constant-exact`:
  `AlgebraicGeometry.ProEtale.upperStar_exact`, the module inverse image is exact.
* Blueprint `rem-ptr-weil-pbc-proetale-operations-8`: pointer remark to the two preceding
  results.
* Blueprint `def-weil-pbc-site-comparison-morphism`: the comparison morphism of sites
  `ν_T : T_proét ⟶ T_ét` is given by the continuous, finite-limit-preserving inclusion
  `AlgebraicGeometry.toProEt T` of the small étale site into the small pro-étale site; the
  adjunction `ν_T^* ⊣ ν_{T,*}` is `AlgebraicGeometry.ProEtale.comparisonAdjunction`, for any
  Grothendieck abelian coefficient category, in particular for sheaves of `Λ`-modules
  (`AlgebraicGeometry.ProEtale.comparisonAdjunctionModuleCat`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory

variable (Λ : Type (u + 1)) [CommRing Λ] {U V : Scheme.{u}} (f : U ⟶ V)

/-- Blueprint `prop-weil-pbc-proetale-constant-ring-map`: constant coefficients on the pro-étale
site. For a morphism `f : U ⟶ V` of schemes, the structure map `f^{-1}Λ_{V,proét} ⟶ Λ_{U,proét}`
(the comparison map `η` of the oplax monoidal inverse image, the constant sheaves being the
monoidal units) is an isomorphism. -/
noncomputable def upperStarConstantIso :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso (η (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f))

@[simp]
lemma upperStarConstantIso_hom :
    (upperStarConstantIso Λ f).hom = η (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) :=
  rfl

/-- Blueprint `prop-weil-pbc-proetale-constant-exact`: exactness of the pro-étale inverse image
for constant coefficients. For a morphism `f : U ⟶ V`, the module inverse image `f^*` on
sheaves of `Λ`-modules preserves finite limits and finite colimits. -/
lemma upperStar_exact :
    PreservesFiniteLimits (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) ∧
      PreservesFiniteColimits (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) :=
  ⟨inferInstance, inferInstance⟩

/-- Blueprint `def-weil-pbc-site-comparison-morphism`: the comparison morphism of sites
`ν_T : T_proét ⟶ T_ét` on sheaves of `Λ`-modules, the adjunction `ν_T^* ⊣ ν_{T,*}`. -/
noncomputable abbrev comparisonAdjunctionModuleCat (T : Scheme.{u}) :
    ν^*(T)[ModuleCat.{u + 1} Λ] ⊣ ν_*(T)[ModuleCat.{u + 1} Λ] :=
  comparisonAdjunction (ModuleCat.{u + 1} Λ) T

end AlgebraicGeometry.ProEtale
