/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube

/-!
# The derived (Pull) isomorphism is monoidal, for an arbitrary coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, write
`T = L(Ext_a) = Λ' ⊗ᴸ_Λ -` for the derived extensions of scalars and let `f : X ⟶ Y` be a
morphism of schemes. The derived (Pull) isomorphism
`Lf^* ⋙ T ≅ T ⋙ Lf^*` (`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`) is compatible
with the tensor comparisons of the derived pullbacks (`leftDerivedUpperStarTensor`) and of the
derived extensions of scalars (`derivedExtendScalarsTensorIso`)
(`ProEtale.CondensedRing.comparisonCompatible_derivedUpperStarExtendScalarsIso`). This is the
analogue without flatness of `ProEtale.CondensedRing.comparisonCompatible_derivedPullIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **(Pull) is monoidal**: for an arbitrary coefficient change `a`, the derived (Pull)
isomorphism `Lf^* ⋙ T ≅ T ⋙ Lf^*` is compatible with the tensor comparisons of the derived
pullbacks and of the derived extensions of scalars. -/
theorem comparisonCompatible_derivedUpperStarExtendScalarsIso :
    Adjunction.ComparisonCompatible (derivedUpperStarExtendScalarsIso a f).symm
      (leftDerivedUpperStarTensor Λ f) (leftDerivedUpperStarTensor Λ' f)
      (derivedExtendScalarsTensorIso a X) (derivedExtendScalarsTensorIso a Y) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
