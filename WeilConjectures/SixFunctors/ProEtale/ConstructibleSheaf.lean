/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!

# Constructible sheaves on the small pro-étale site

This file defines the intrinsic notion of constructibility of sheaves of `Λ`-modules on the
small pro-étale site of a scheme `X` (blueprint `def-weil-finite-torsion-constructibility`): a
sheaf is constructible if, on the strata of a stratification of `X`, it is locally constant with
finite stalks. Locally constant with finite stalks means that the pullbacks along the members
of a pro-étale covering family are constant sheaves of finite `Λ`-modules.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant`: locally constant with finite
  stalks.
- `AlgebraicGeometry.ProEtale.IsConstructible`: constructible.

## Main statements

- `AlgebraicGeometry.ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`
  (`lem-sf-proetale-constructible-origin` (i)): a constructible pro-étale sheaf is `ν^*` of a
  constructible étale sheaf.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `def-weil-finite-torsion-constructibility`: a sheaf `F` of `Λ`-modules on the
small pro-étale site of `X` is *locally constant with finite stalks* if there is a pro-étale
covering family `g i : W i ⟶ X` such that every pullback `(g i)^* F` is the constant sheaf of a
finite `Λ`-module. -/
def IsFiniteLocallyConstant {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
    Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
      ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj F ≅
          (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)

/-- Blueprint `def-weil-finite-torsion-constructibility`: a sheaf `F` of `Λ`-modules on the
small pro-étale site of `X` is *constructible* if there is a finite partition of `X` into
locally closed constructible subschemes on each of which the restriction of `F` is locally
constant with finite stalks. -/
def IsConstructible {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ S : Stratification X, ∀ i : Fin S.n,
    IsFiniteLocallyConstant Λ (((S.immersion i))^*[ModuleCat.{u + 1} Λ].obj F)

/-- Blueprint `lem-sf-proetale-constructible-origin`: Constructible pro-étale coefficients are
of étale origin, clause (i), essential surjectivity.

At a finite coefficient ring `Λ`, every constructible sheaf of `Λ`-modules on the small
pro-étale site of a scheme `T` is `ν^*` of a constructible sheaf on the small étale site. -/
theorem exists_isConstructibleSheaf_iso_comparisonUpperStar_obj [Finite Λ] {T : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)} (hF : IsConstructible Λ F) :
    ∃ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), Scheme.IsConstructibleSheaf G ∧
      Nonempty ((ν^*(T)[ModuleCat.{u + 1} Λ]).obj G ≅ F) :=
  sorry

end AlgebraicGeometry.ProEtale
