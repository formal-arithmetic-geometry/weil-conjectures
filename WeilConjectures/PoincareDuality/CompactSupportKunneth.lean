/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionPadicAlgCl

/-!

# The Künneth formula for compact supports

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of separated `k`-schemes of finite type, and let
```
P --p₂--> Y
|         |
p₁        g
v         v
X --f---> S
```
be a cartesian square, `P = X ×_S Y`, with structure map `h = p₁ ≫ f`. For bounded constructible
`ℚ̄_ℓ`-complexes `K` on `X` and `L` on `Y`, write `K ⊠_S L = Lp₁^* K ⊗ Lp₂^* L`. The *Künneth
isomorphism* (blueprint `lemma-kunneth-formula-compact-supports`) is the composite
```
Rh_! (Lp₁^* K ⊗ Lp₂^* L) ≅ Rf_! (K ⊗ Rp₁_! Lp₂^* L) ≅ Rf_! (K ⊗ Lf^* Rg_! L) ≅ Rf_! K ⊗ Rg_! L
```
of the projection formula for `p₁` (after `Rh_! ≅ Rp₁_! ⋙ Rf_!` and the symmetry of `⊗`), of the
inverse of compact-support base change `Ex_! : Rg_! ⋙ Lf^* ⟶ Lp₂^* ⋙ Rp₁_!` of the square, and of
the projection formula for `f`. Each of the three maps is an isomorphism: the projection formula
is `ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism`, and
compact-support base change is
`ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl`.

## Main definitions

- `ProEtale.CondensedRing.compactSupportKunnethProjectionIso`: the first isomorphism, the
  projection formula for `p₁` (blueprint `lemma-kunneth-formula-compact-supports--1`).
- `ProEtale.CondensedRing.compactSupportKunnethBaseChangeIso`: the second isomorphism, induced by
  compact-support base change (blueprint `lemma-kunneth-formula-compact-supports--2`).
- `ProEtale.CondensedRing.compactSupportKunnethProjectionIso'`: the third isomorphism, the
  projection formula for `f` (blueprint `lemma-kunneth-formula-compact-supports--3`).
- `ProEtale.CondensedRing.compactSupportKunnethIso`: the Künneth isomorphism
  `Rh_! (K ⊠_S L) ≅ Rf_! K ⊗ Rg_! L` (blueprint `lemma-kunneth-formula-compact-supports`).

## Implementation notes

The coefficient field is `ℚ̄_ℓ`, for which the composition isomorphism of the lower shrieks
`boundedConstructibleLowerShriekComp_padicAlgCl` and the symmetry of the derived tensor product
`boundedConstructibleBraiding` are available. The fibre product is an arbitrary cartesian square,
and `h` is the composite `p₁ ≫ f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y S P : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {f : X ⟶ S} {g : Y ⟶ S} {p₁ : P ⟶ X} {p₂ : P ⟶ Y}

/-- **The projection formula for `p₁` in the Künneth formula** (blueprint
`lemma-kunneth-formula-compact-supports--1`): for a morphism `p₁ : P ⟶ X` followed by
`f : X ⟶ S`, the isomorphism
`R(p₁ ≫ f)_! (Lp₁^* K ⊗ M) ≅ Rf_! (K ⊗ Rp₁_! M)`, the composite of the composition isomorphism
`R(p₁ ≫ f)_! ≅ Rp₁_! ⋙ Rf_!`, the symmetry of `⊗`, the inverse of the projection morphism
`Rp₁_! M ⊗ K ⟶ Rp₁_! (M ⊗ Lp₁^* K)`, which is an isomorphism
(`isIso_boundedConstructibleExceptionalProjectionMorphism`), and the symmetry again. In the
Künneth formula `M = Lp₂^* L`. -/
noncomputable def compactSupportKunnethProjectionIso (f : X ⟶ S) (p₁ : P ⟶ X)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ (p₁ ≫ f)).obj
        ((boundedConstructibleUpperStar _ ℓ p₁).obj K ⊗ M) ≅
      (boundedConstructibleLowerShriek ℓ f).obj
        (K ⊗ (boundedConstructibleLowerShriek ℓ p₁).obj M) :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ p₁ f).app _ ≪≫
    (boundedConstructibleLowerShriek ℓ f).mapIso
      ((boundedConstructibleLowerShriek ℓ p₁).mapIso (β_ _ _) ≪≫
        (asIso (boundedConstructibleExceptionalProjectionMorphism ℓ p₁ M K)).symm ≪≫ β_ _ _)

/-- **Compact-support base change in the Künneth formula** (blueprint
`lemma-kunneth-formula-compact-supports--2`): for a cartesian square `sq` with sides
`p₁ : P ⟶ X`, `p₂ : P ⟶ Y` over `f : X ⟶ S`, `g : Y ⟶ S`, the compact-support base-change
morphism `Ex_! : Rg_! ⋙ Lf^* ⟶ Lp₂^* ⋙ Rp₁_!` is an isomorphism
(`isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl`), and its inverse induces
`Rf_! (K ⊗ Rp₁_! Lp₂^* L) ≅ Rf_! (K ⊗ Lf^* Rg_! L)`. -/
noncomputable def compactSupportKunnethBaseChangeIso (sq : IsPullback p₂ p₁ g f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ f).obj
        (K ⊗ (boundedConstructibleLowerShriek ℓ p₁).obj
          ((boundedConstructibleUpperStar _ ℓ p₂).obj L)) ≅
      (boundedConstructibleLowerShriek ℓ f).obj
        (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
          ((boundedConstructibleLowerShriek ℓ g).obj L)) :=
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  (boundedConstructibleLowerShriek ℓ f).mapIso
    (whiskerLeftIso K
      ((asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).symm.app L))

/-- **The projection formula for `f` in the Künneth formula** (blueprint
`lemma-kunneth-formula-compact-supports--3`): the inverse
`Rf_! (K ⊗ Lf^* B) ≅ Rf_! K ⊗ B` of the exceptional projection morphism, which is an isomorphism
(`isIso_boundedConstructibleExceptionalProjectionMorphism`). In the Künneth formula
`B = Rg_! L`. -/
noncomputable def compactSupportKunnethProjectionIso' (f : X ⟶ S)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ f).obj (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) ≅
      (boundedConstructibleLowerShriek ℓ f).obj K ⊗ B :=
  (asIso (boundedConstructibleExceptionalProjectionMorphism ℓ f K B)).symm

/-- **The Künneth formula for compact supports** (blueprint
`lemma-kunneth-formula-compact-supports`): for a cartesian square `sq` with sides
`p₁ : P ⟶ X`, `p₂ : P ⟶ Y` over `f : X ⟶ S`, `g : Y ⟶ S`, and bounded constructible
`ℚ̄_ℓ`-complexes `K` on `X` and `L` on `Y`, the *Künneth isomorphism*
`Rh_! (K ⊠_S L) = Rh_! (Lp₁^* K ⊗ Lp₂^* L) ≅ Rf_! K ⊗ Rg_! L`, `h = p₁ ≫ f`. It is the composite
of the projection formula for `p₁` (`compactSupportKunnethProjectionIso`), of the inverse of
compact-support base change (`compactSupportKunnethBaseChangeIso`) and of the projection formula
for `f` (`compactSupportKunnethProjectionIso'`). -/
noncomputable def compactSupportKunnethIso (sq : IsPullback p₂ p₁ g f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ (p₁ ≫ f)).obj
        ((boundedConstructibleUpperStar _ ℓ p₁).obj K ⊗
          (boundedConstructibleUpperStar _ ℓ p₂).obj L) ≅
      (boundedConstructibleLowerShriek ℓ f).obj K ⊗ (boundedConstructibleLowerShriek ℓ g).obj L :=
  compactSupportKunnethProjectionIso ℓ f p₁ K _ ≪≫
    compactSupportKunnethBaseChangeIso ℓ sq K L ≪≫
    compactSupportKunnethProjectionIso' ℓ f K _

end AlgebraicGeometry.ProEtale.CondensedRing
