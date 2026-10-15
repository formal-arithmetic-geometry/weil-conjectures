/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Locally closed generators for constructible condensed modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Single sheaves obtained by extension by zero from an open in a closed subscheme,
with a locally finitely presented coefficient module on the open.
Source: the open/closed steps of Hemo--Richarz--Scholbach, Lemma 5.3(2).
(blueprint: def-weil-pbc-condensed-constructible-piece) -/
def condensedConstructiblePiece
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T))) :=
  fun K ↦ ∃ (Z U : Scheme.{u}) (i : Z ⟶ T) (j : U ⟶ Z),
    Exists fun [_hi : IsClosedImmersion i] ↦ Exists fun [_hj : IsOpenImmersion j] ↦
      QuasiCompact j ∧ ∃ (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) U)),
        IsLocallyFinitelyPresented
          (condensedRingObj (Profinite.continuousMapRingObj E.val) U) P ∧
        Nonempty (K ≅ (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.val) i).obj
            ((CondensedRing.openImmersionLowerShriek
              (Profinite.continuousMapRingObj E.val) j).obj P)))

end AlgebraicGeometry.ProEtale
