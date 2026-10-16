/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.CondensedQbarComparisons

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Coefficient pullback comparisons commute with the specified geometric square comparison.
Source: ChangeOfCoefficients.lean, derivedPullIso and derivedComapLowerStarIso;
UpperLowerStar/Defs.lean, upperStarComp; Derived/UpperLowerStar.lean, leftDerivedUpperStarComp;
TwoColimit.lean, final transport paragraph
(blueprint: lem-weil-pbc-qbar-condensed-pullback-cube).

Proof in words. Restriction of scalars followed by geometric direct image and geometric
direct image followed by restriction have the same underlying sheaf functor; the natural
isomorphism comapLowerStarIso is the identity on underlying sheaves. Its compatibility
with direct-image composition follows by forgetting the action, which is faithful, and
using associativity of direct-image composition. The change-of-coefficients square for
the coefficient maps follows from their naturality. Derive these commuting diagrams using
K-injective resolutions: restriction is exact and preserves K-injectives since its left
adjoint is exact, and direct images preserve K-injectives. The universal property of the
right derived functor identifies the resulting comparison with derivedComapLowerStarIso
and preserves its composition equation. Conjugate that equation along the two geometric
adjunctions and the extension/restriction adjunctions. Conjugation respects composition
and associators, giving compatibility of derivedPullIso with geometric composition.
The geometric composition maps are the specified leftDerivedUpperStarComp: derive the
underived adjunction-conjugate composition equation and use uniqueness of derived
adjunctions, with exact pullbacks computed termwise. Apply this composition equation to
(f', g) and (g', f), transport along sq.w, and cancel the common comparison for the equal
composite. Naturality under equality and proof irrelevance handle the commutativity proof.
This gives the pullback cube in the displayed inverse-alpha_f' orientation. Restrict along
the fully faithful bounded constructible inclusions, whose composition constraints are
restrictions of these same maps. This proof uses no base-change exchange morphism, no
push comparison, and no properness or Cartesianity. For identity morphisms the equation
reduces to the unit coherence; for a zero object both sides are its unique morphism. -/
theorem constructibleToQbar_pullback_cube
    (sq : CommSq g' f' f g) (V : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToQbarPullIso ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj V)).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison
          (Profinite.continuousMapRingObj E) ℓ k sq).hom.app V) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f).obj V)).hom =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarPullIso ℓ k E g V).hom ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ)
        ℓ k sq).hom.app ((constructibleToPadicAlgCl Y ℓ E).obj V) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').map
        (constructibleToQbarPullIso ℓ k E f V).inv := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
