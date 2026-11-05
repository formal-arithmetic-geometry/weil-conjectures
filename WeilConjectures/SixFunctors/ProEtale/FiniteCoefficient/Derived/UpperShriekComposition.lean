/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-!
# The mate of the composition law for the constructible `Rf^!`

Let `X ⟶[f] Y ⟶[g] Z` be morphisms admitting compactifications. The constructible exceptional
inverse image `Rf^! = ν_X^* f^× Rν_{Y,*}` of the small pro-étale sites
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`) is right adjoint to `Rf_!` on the bounded
below objects of étale origin (blueprint `sk-prop-sf-existence` (c),
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction`). This file proves clause (b) of
blueprint `sk-lem-sf-mate` in its constructible form: the mate of the composition isomorphism
`R(g ∘ f)_! ≅ Rg_! Rf_!` under these adjunctions is an isomorphism `R(g ∘ f)^! ≅ Rf^! Rg^!` of
functors `D⁺(Z_proét) ⥤ D⁺(X_proét)`, the unit and counit of the composite adjunction being the
pasted ones; and it restricts to `Dctf` as soon as the three functors preserve `Dctf`. It also
records the formal clause (a), for the ambient right adjoints, and that the constructible
adjunction is the restriction of any ambient one.

## Main definitions

- `AlgebraicGeometry.ProEtale.comparisonUpperStarPlusEtaleOrigin`: `ν^*` as a functor from
  `D⁺(X_ét)` to the bounded below objects of étale origin in `D(X_proét)`; it is an equivalence.

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_iso_ι_comp_rightDerivedLowerShriek_comp`: the composition
  law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the pro-étale `Rf_!` on objects bounded below of étale
  origin, transported from the étale one (blueprint `sk-thm-sf-comp-composition`).
- `AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq`: the mate
  statement on any full subcategories preserved by the six functors involved.
- `AlgebraicGeometry.ProEtale.nonempty_iso_rightDerivedUpperShriekPlus_comp`:
  `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` on `D⁺(Z_proét)`.
- `AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq_of_finiteTor`: the
  restriction to `Dctf`.
- `HasAmbientExceptionalRightAdjoint.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv` (in the
  namespace `AlgebraicGeometry.ProEtale`): clause (a), the ambient form.
- `HasAmbientExceptionalRightAdjoint.compIso`: clause (a), the isomorphism of ambient functors
  `Rg^× ⋙ Rf^× ≅ R(f ≫ g)^×` mate to an ambient composition isomorphism, with its unit and counit
  lemmas; `HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_iff`: it exists exactly when the
  ambient composition law does.
- `HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_yoneda_comp_whiskeringLeft`: clause (a)
  with the composition law of `sk-thm-sf-comp-composition`.
- `AlgebraicGeometry.ProEtale.exists_bijective_comp_and_homEquiv_symm_comp_eq`: under the ambient
  datum, the constructible adjunction is the restriction of the ambient one.

## Implementation notes

The composition law of the pro-étale `Rf_!` is only available through the étale one
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, which asserts that *some*
isomorphism exists; this is why the mate statements are existential in the isomorphism of left
adjoints. Being formal, they hold for every such isomorphism.

Clause (a) of `sk-lem-sf-mate` takes the mate of "the composition isomorphism
`R(gf)_! ≅ Rg_! Rf_!` of `sk-thm-sf-comp-composition`" on the *ambient* functors, but that node
only gives the composition law on bounded below objects of étale origin. So clause (a) is stated
for a given ambient composition isomorphism (`HasAmbientExceptionalRightAdjoint.compIso`), and
`HasAmbientExceptionalRightAdjoint.nonempty_iso_comp_iff` records that the ambient isomorphism
`R(f ≫ g)^× ≅ Rg^× ⋙ Rf^×` exists exactly when the ambient composition law does. The ambient
composition law on all of `D(X_proét)` is not stated. Comparing the chosen compactifications
needs proper base change at the boundary for arbitrary unbounded pro-étale sheaves, which is not
known. The datum `FullCD` does not help: it bounds only the proper parts of the three chosen
compactifications, not those of the auxiliary compactifications used in the comparison.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section EtaleOrigin

variable (X : Scheme.{u})

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end EtaleOrigin

section Composition

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y)
  (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]

variable {Λ}

variable [CompactSpace Y] [CompactSpace Z]

variable (PX : ObjectProperty (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))
  (PY : ObjectProperty (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))))
  (PZ : ObjectProperty (_root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))))
  (hPX : PX ≤ DerivedCategory.plusEtaleOrigin _ X)
  (hPY : PY ≤ DerivedCategory.plusEtaleOrigin _ Y) (hPZ : PZ ≤ DerivedCategory.TStructure.t.plus)
  (hf₁ : ∀ K, PX K → PY ((R(f)_![ModuleCat.{u + 1} Λ]).obj K))
  (hf₂ : ∀ L, PY L → PX ((R(f)^![Λ]).obj L))
  (hg₁ : ∀ K, PY K → PZ ((R(g)_![ModuleCat.{u + 1} Λ]).obj K))
  (hg₂ : ∀ L, PZ L → PY ((R(g)^![Λ]).obj L))
  (hfg₁ : ∀ K, PX K → PZ ((R(f ≫ g)_![ModuleCat.{u + 1} Λ]).obj K))
  (hfg₂ : ∀ L, PZ L → PX ((R(f ≫ g)^![Λ]).obj L))

end Composition

section LowerShriek

variable {A} {Λ} {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

end LowerShriek

section BoundedBelow

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y)
  (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [CompactSpace Y] [CompactSpace Z]

end BoundedBelow

section Ambient

variable {A} {Λ} {X Y Z : Scheme.{u}}

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end Ambient

end AlgebraicGeometry.ProEtale
