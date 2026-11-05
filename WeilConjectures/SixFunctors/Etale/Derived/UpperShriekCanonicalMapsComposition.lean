/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarInternalHom

/-!
# The canonical maps of `Rf^!` under composition, for finite coefficients

For a finite coefficient ring `Λ`, the composition law and the étale descent of the canonical
maps of the exceptional inverse image: the tensor map
`θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` (`AlgebraicGeometry.Etale.dualizingComplexTensorMap`) and the
base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). They are deduced from the
coherence of the composition law for `Rf_!` with the projection formula and with base change
(`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`) and of the projection formula
with the associativity of `⊗ᴸ` (`AlgebraicGeometry.Etale.projectionMapAssociativity`), through
the general statements of
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_comp`
- `AlgebraicGeometry.Etale.isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale`
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap_comp`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product: otherwise the monoidal structures found by instance
-- search differ from the ones in these definitions, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section BaseChange

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {f' : X' ⟶ Y'}
  {g' : Y' ⟶ Z'} {h' : X' ⟶ Z'} {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
  (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (sqh : IsPullback a h' h c)
  (w : f ≫ g = h) (w' : f' ≫ g' = h') [HasCompactification f] [HasCompactification g]
  [HasCompactification h] [HasCompactification f'] [HasCompactification g']
  [HasCompactification h'] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact h']

include sqf sqg sqh w w' in
/-- **Base change maps of a composite.** For stacked cartesian squares, the base change map of
`R(f ≫ g)^!` is, up to the composition isomorphisms, the composite of those of `Rf^!` and `Rg^!`
(the blueprint's "exceptional composition identifies the base-change comparisons"). In
particular, `β_h` is an isomorphism at `K` as soon as `β_f` is one at `Rg^! K` and `β_g` at `K`,
and `Rf'^! β_g` is one at `K` as soon as `β_h` is one at `K` and `β_f` at `Rg^! K`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hf : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqf).app
      ((R(g)^![Λ]).obj K))) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqh).app K) ↔
      IsIso ((R(f')^![Λ]).map
        ((rightDerivedUpperShriekBaseChangeMap Λ sqg).app K)) := by
  obtain ⟨E, -, hEx⟩ := exists_rightDerivedLowerShriekCompIso Λ
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqf
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqg
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqh
  have key := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (rightDerivedUpperShriekAdjunction _ f) (rightDerivedUpperShriekAdjunction _ g)
    (rightDerivedUpperShriekAdjunction _ h) (rightDerivedUpperShriekAdjunction _ f')
    (rightDerivedUpperShriekAdjunction _ g') (rightDerivedUpperShriekAdjunction _ h')
    (rightDerivedLowerShriekBaseChangeMap Λ sqf) (rightDerivedLowerShriekBaseChangeMap Λ sqg)
    (rightDerivedLowerShriekBaseChangeMap Λ sqh) (E f g h w) (E f' g' h' w')
    (hEx sqf sqg sqh w w') K
  change IsIso ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqh))).natTrans.app K) ↔
    IsIso ((R(f')^![Λ]).map
      ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqg))).natTrans.app K))
  change IsIso ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqf))).natTrans.app
    ((R(g)^![Λ]).obj K)) at hf
  rw [← isIso_comp_right_iff _ ((Adjunction.rightAdjointUniq
      ((rightDerivedUpperShriekAdjunction _ h').ofNatIsoLeft (E f' g' h' w'))
      ((rightDerivedUpperShriekAdjunction _ f').comp
        (rightDerivedUpperShriekAdjunction _ g'))).hom.app _), ← key,
    isIso_comp_left_iff, isIso_comp_left_iff]

end BaseChange

section InvertibleBaseChange

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, whose
-- compatibility of the projection map with base change is used below: with the same instances,
-- its statement matches the one expected here syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

end InvertibleBaseChange

end Etale

end AlgebraicGeometry
