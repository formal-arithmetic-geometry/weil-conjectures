/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible

/-!
# Constructible module objects with finite coefficients are of étale origin

Let `T` be a finite discrete commutative ring (for instance `𝒪_E ⧸ ℓⁿ`) and `X` a scheme. A
bounded constructible complex `K` of module objects over `Λ_X = p_X^* T̲` on the pro-étale site
(`ProEtale.boundedConstructible`) is of étale origin: under the identification
`ProEtale.finiteCoefficientDerivedEquivalence` of module objects over `Λ_X` with sheaves of
`T`-modules, it is `D(ν^*) K'` for a bounded constructible complex `K'` of étale sheaves of
`T`-modules (`ProEtale.boundedConstructible_finiteCoefficientDerivedEquivalence_functor_obj`).

This is the reading on the étale site of the finite coefficient categories of blueprint
`sk-def-sf-categories` ("for finite `Λ = A_{E,n}`, and only there, the same definitions may be
read on the small étale site; the comparison `ν_T^*` identifies them with the pro-étale
categories"), in the form needed for blueprint `det-prop-scalar-six-pullback` (1) for
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site.

The proof: the cohomology sheaves of `K` are constructible module objects, so the corresponding
sheaves of `T`-modules are constructible in the intrinsic sense
(`ProEtale.isConstructible_finiteCoefficientModEquivalence_functor_obj`), and an intrinsically
bounded constructible pro-étale complex is of étale origin
(`ProEtale.DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic`, blueprint
`lem-sf-proetale-constructible-origin`).

## Main statements

- `ProEtale.boundedConstructible_finiteCoefficientDerivedEquivalence_functor_obj`: bounded
  constructible complexes of module objects over `Λ_X` are of étale origin.
- `ProEtale.isEtaleOrigin_of_isConstructible`: the same, for `X` of finite type over a field.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

section

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Constructible finite-coefficient module objects are of étale origin**, on any scheme `X`.
For a finite discrete commutative ring `T`, a bounded constructible complex `K` of module objects
over `Λ_X = p_X^* T̲` on `X_proét` corresponds, under `finiteCoefficientDerivedEquivalence`, to a
complex of étale origin: `D(ν^*) K'` for a bounded constructible complex `K'` of étale sheaves of
`T`-modules. -/
theorem boundedConstructible_finiteCoefficientDerivedEquivalence_functor_obj {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj K) :=
  DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic
    ⟨(finiteCoefficientModEquivalence X T).functor.bounded_mapDerivedCategory_obj hK.1, fun n ↦
      isConstructible_of_iso
        (((finiteCoefficientModEquivalence X T).functor.mapDerivedCategoryHomologyFunctorIso
          n).app K)
        (isConstructible_finiteCoefficientModEquivalence_functor_obj T (hK.2 n))⟩

end

/-- Blueprint `lem-sf-proetale-constructible-origin` (ii), for module objects (section
`sec-proetale-coefficients`, `sk-prop-sf-comparison`; the comparison
`sk-thm-pe-constructible-comparison`): **constructible pro-étale complexes with finite
coefficients are of étale origin**. For a finite discrete commutative ring `T` and a scheme `X`
of finite type over a field, a bounded complex of module objects over `T̲_X` with constructible
cohomology objects, read as a complex of pro-étale sheaves of `T`-modules through
`finiteCoefficientDerivedEquivalence`, is isomorphic to `ν^* K'` for a bounded constructible
complex `K'` of étale sheaves of `T`-modules (Bhatt–Scholze, *The pro-étale topology for
schemes*, Corollary 5.1.6 and Section 6.8). The finiteness hypotheses on `X` are not needed
(`boundedConstructible_finiteCoefficientDerivedEquivalence_functor_obj`). -/
theorem isEtaleOrigin_of_isConstructible {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T]
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X.left)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T)) X.left
      ((finiteCoefficientDerivedEquivalence X.left T).functor.obj K.obj) :=
  boundedConstructible_finiteCoefficientDerivedEquivalence_functor_obj T K.property

end AlgebraicGeometry.ProEtale
