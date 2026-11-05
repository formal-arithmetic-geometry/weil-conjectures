/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperStarProducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedAdicCompleteRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarMapModLimits
public import WeilConjectures.TraceFormula.OpenCover

/-!
# Constructible `𝒪_E`-module objects are derived complete

Let `X` be a noetherian scheme. A constructible `𝒪_{E,X}`-module object `M` on `X_proét` is
derived `ℓ`-adically complete (`ProEtale.isDerivedAdicComplete_of_isConstructibleModuleObject`).

As in the proof of Nakayama's lemma for constructible module objects
(`ProEtale.isZero_of_isConstructibleModuleObject_of_isZero_extendScalars`), there is a finite
jointly surjective family of quasi-compact morphisms `g : V ⟶ X`, composites of the inclusion of
an affine open, a member of a pro-étale cover and the immersion of a stratum, such that every
`g^* M` is finitely presented, hence derived complete
(`ProEtale.isDerivedAdicComplete_of_isFinitelyPresented`). The pullbacks `g^*` jointly reflect
isomorphisms (`ProEtale.CondensedRing.jointlyReflectIsomorphisms_upperStar_of_cover`) and
commute with countable products: pullbacks along weakly étale morphisms preserve all limits, and
pullbacks along immersions into noetherian schemes preserve countable products
(`ProEtale.CondensedRing.preservesLimitsOfShape_upperStar_of_isImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end CondensedRing

open CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

end AlgebraicGeometry.ProEtale
