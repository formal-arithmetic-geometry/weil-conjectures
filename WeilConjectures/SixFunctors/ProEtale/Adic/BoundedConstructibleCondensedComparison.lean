/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Bounded constructibility in the two models of `ℓ`-adic sheaves

The equivalence `D(AdicSheaf ℓ T) ≌ D(Mod_{Λ_T})` between the derived categories of the two
models of `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicSheafDerivedEquivCondensedMod`)
identifies the bounded constructible complexes of the two models, for `T` separated of finite type
over an algebraic closure of a finite field
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdic_iff_boundedConstructible`). The coefficient
realization used by the native forgetful functors of Weil complexes is this comparison
(`AlgebraicGeometry.ProEtale.forgetAbCompComapNativeModuleCoefficientIso`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The native coefficient realization `forgetAb` followed by restriction of scalars along the
native coefficient isomorphism is the comparison functor of the two models of `ℓ`-adic
sheaves. -/
noncomputable def forgetAbCompComapNativeModuleCoefficientIso (T : Scheme.{u}) :
    AdicSheaf.forgetAb ℓ T ⋙ Mod.comap (nativeModuleCoefficientIso ℓ T).hom ≅
      (adicSheafEquivCondensedMod ℓ T).functor :=
  sorry

/-- **Bounded constructibility in the two models**: a complex of `ℓ`-adic sheaves on a separated
scheme of finite type `T` over an algebraic closure `k` of a finite field `k₀` is bounded with
constructible cohomology if and only if its image in the condensed model is bounded
constructible. -/
theorem boundedConstructibleAdic_iff_boundedConstructible (k₀ k : Type u) [Field k₀] [Finite k₀]
    [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k] [Fact (ringChar k₀ ≠ ℓ)]
    (T : Over (Spec (CommRingCat.of k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (K : _root_.DerivedCategory (AdicSheaf ℓ T.left)) :
    DerivedCategory.boundedConstructibleAdic ℓ T.left K ↔
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T.left)
        ((adicSheafDerivedEquivCondensedMod ℓ T.left).functor.obj K) :=
  sorry

end AlgebraicGeometry.ProEtale
