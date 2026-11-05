/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
public import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralFlat
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!
# Continuity of `Hom` out of a bounded constructible `E`-complex

For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a topologically noetherian scheme `X` and a bounded
constructible complex `C ∈ Dᵇc(X)⟦E̲⟧`, morphisms in `D(X_proét, E)` from `C` to a filtered
colimit `K = colim_j K_j` of complexes of `E_X`-modules which all vanish below a fixed degree are
the filtered colimit of the morphisms `C ⟶ K_j`, in every shift
(`ProEtale.CondensedRing.constructibleExtContinuity_continuousMapRingObj`, blueprint
`sk-lem-constructible-ext-continuity` (1)).

## Proof

Following the blueprint, the class of objects `s` such that `Hom(s, -[n])` commutes with filtered
colimits of `E_X`-modules is closed under shifts and extensions; by dévissage
(`ProEtale.prop_of_boundedConstructibleModule`) it contains `Dᵇc(X, E)` as soon as it contains the
constructible sheaves, which is
`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`
(reducing to lisse, hence locally free, sheaves:
`ProEtale.CondensedRing.homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj`).
Since `C` is bounded above, the continuity extends to filtered colimits of uniformly bounded below
complexes (`DerivedCategory.HomCommutesWithFilteredColimits.cochainComplex`), filtered colimits of
`E_X`-modules being exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

end AlgebraicGeometry.ProEtale.CondensedRing
