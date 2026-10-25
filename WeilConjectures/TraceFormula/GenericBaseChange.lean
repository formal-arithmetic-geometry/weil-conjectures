/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProper
public import WeilConjectures.TraceFormula.Product
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism

/-!

# Base change along a product projection

Let `f : U ⟶ Y` be a morphism of separated `k`-schemes of finite type and `X` a separated
`k`-scheme of finite type. The square
```
X ⨯ U ──(𝟙 × f)──▶ X ⨯ Y
  │ p_U               │ p_Y
  ▼                   ▼
  U ────── f ───────▶ Y
```
(`ProEtale.CondensedRing.commSq_prodMap_snd`) is cartesian, and its base change morphism
`Lp_Y^* Rf_* ⟶ R(𝟙 × f)_* Lp_U^*` on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is an isomorphism
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`; blueprint
`sk-lem-tf-independent-base-change`). Since `X` may be singular, smooth base change does not
apply. Following the blueprint (`det-tf-ibc-pasting`), we choose a compactification
`f = p ∘ i` with `i` an open immersion and `p` proper (Nagata). The square of `f` is the vertical
pasting of the squares of `i` and of `p`, so its base change morphism is the pasting of theirs
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap_comp`). The one of `p` is an
isomorphism by proper base change, the one of `i` by base change for open direct images over a
field.

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`: generic base change
  over the field `k` along `X ⨯ Y ⟶ Y`.

## Inputs from other subsections

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion`:
  base change for open direct images over a field (blueprint `sk-cor-geo-open-finiteness`,
  `det-geo-open-finiteness-base-change`, section `sec-six-functors-basics`), in its `ℚ̄_ℓ` form.
- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`: proper
  base change.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom]
  [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- The commutative square
```
X ⨯ U ──(𝟙 × f)──▶ X ⨯ Y
  │ p_U               │ p_Y
  ▼                   ▼
  U ────── f ───────▶ Y
```
of the second projections, the base change of `f` along `X ⨯ Y ⟶ Y`. -/
lemma commSq_prodMap_snd (f : U ⟶ Y) :
    CommSq (prod.snd : X ⨯ U ⟶ U) (prod.map (𝟙 X) f) f prod.snd :=
  ⟨(prod.map_snd _ _).symm⟩

/-- **Base change for open direct images over a field**, in its `ℚ̄_ℓ` form: for an open
immersion `j : U ⟶ Y` of separated `k`-schemes of finite type and any separated `k`-scheme of
finite type `X`, the base change morphism `Lp_Y^* Rj_* ⟶ R(𝟙 × j)_* Lp_U^*` of the square
`commSq_prodMap_snd` is an isomorphism on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`.

This is the blueprint node `det-geo-open-finiteness-base-change` (equivalently the base change
assertion of `sk-cor-geo-open-finiteness`), section `sec-six-functors-basics`, which states it for
finite `ℓ`-primary coefficients; it is Deligne's generic base change theorem (SGA 4½,
[Th. finitude], Théorème 1.9) over the base `Spec k`, whose only nonempty open is itself. The
`ℚ̄_ℓ`-coefficients follow by passage to the limit (Bhatt–Scholze, Section 6.8). -/
theorem isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion (j : U ⟶ Y)
    [IsOpenImmersion j.left] :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) j)) :=
  sorry

/-- Base change along a product projection for a proper morphism `p`: the square
`commSq_prodMap_snd p` is cartesian, so its base change morphism is an isomorphism by proper base
change (`isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`). -/
theorem isIso_boundedConstructibleBaseChange_prodMap_of_isProper (p : U ⟶ Y) [IsProper p.left] :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) p)) :=
  isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
    (IsPullback.of_prod_snd_with_id p X)

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism (Profinite.padicAlgClRingObj ℓ) ℓ k

/-- **Pasting of base change along a product projection**: if the base change morphisms of the
squares `commSq_prodMap_snd i` and `commSq_prodMap_snd p` are isomorphisms, so is the one of
`commSq_prodMap_snd (i ≫ p)`, the vertical pasting of the two squares (blueprint
`det-tf-ibc-pasting`). -/
theorem isIso_boundedConstructibleBaseChange_prodMap_comp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (i : U ⟶ Z) (p : Z ⟶ Y)
    (hi : IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) i)))
    (hp : IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) p))) :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) (i ≫ p))) := by
  rw [boundedConstructibleBaseChange_eq_pfBaseChange] at hi hp
  have h := (𝔽).pfBaseChange_paste_vert (SepFinType.homMk (prod.snd : X ⨯ U ⟶ U))
    (SepFinType.homMk (prod.snd : X ⨯ Z ⟶ Z)) (SepFinType.homMk (prod.snd : X ⨯ Y ⟶ Y))
    (SepFinType.homMk (prod.map (𝟙 X) i)) (SepFinType.homMk i)
    (SepFinType.homMk (prod.map (𝟙 X) p)) (SepFinType.homMk p)
    (SepFinType.homMk (prod.map (𝟙 X) (i ≫ p))) (SepFinType.homMk (i ≫ p))
    (SepFinType.homMk_comp_homMk (commSq_prodMap_snd i).w)
    (SepFinType.homMk_comp_homMk (commSq_prodMap_snd p).w)
    (ObjectProperty.hom_ext _ (by simp)) (ObjectProperty.hom_ext _ rfl)
    (SepFinType.homMk_comp_homMk (commSq_prodMap_snd (i ≫ p)).w)
  have key : IsIso ((𝔽).pfBaseChange (SepFinType.homMk (prod.snd : X ⨯ U ⟶ U))
      (SepFinType.homMk (prod.map (𝟙 X) (i ≫ p))) (SepFinType.homMk (i ≫ p))
      (SepFinType.homMk (prod.snd : X ⨯ Y ⟶ Y))
      (SepFinType.homMk_comp_homMk (commSq_prodMap_snd (i ≫ p)).w)).natTrans := by
    rw [h]
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]
    infer_instance
  rw [boundedConstructibleBaseChange_eq_pfBaseChange]
  exact key

/-- **Generic base change over the field `k`**: for any morphism `f : U ⟶ Y` of separated
`k`-schemes of finite type and any `X`, the base change morphism
`Lp_Y^* Rf_* ⟶ R(𝟙 × f)_* Lp_U^*` of the square `commSq_prodMap_snd`, i.e. of the base change
of `f` along `X ⨯ Y ⟶ Y`, is an isomorphism on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (blueprint
`sk-lem-tf-independent-base-change`, stated there for finite coefficients; SGA 4½,
[Th. finitude], Théorème 1.9 over `Spec k`).

Following the blueprint (`det-tf-ibc-pasting`), a Nagata compactification `f = p ∘ i` reduces it
to the open immersion `i`
(`isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion`) and the proper morphism `p`
(`isIso_boundedConstructibleBaseChange_prodMap_of_isProper`). -/
theorem isIso_boundedConstructibleBaseChange_prodMap (f : U ⟶ Y) :
    IsIso (boundedConstructibleBaseChange ℓ
      (commSq_prodMap_snd (X := X) f)) := by
  let c := compactificationOverField f
  have hf : c.overI ≫ c.overG = f := c.overI_overG
  have := isIso_boundedConstructibleBaseChange_prodMap_comp ℓ (X := X) c.overI c.overG
    (isIso_boundedConstructibleBaseChange_prodMap_of_isOpenImmersion ℓ c.overI)
    (isIso_boundedConstructibleBaseChange_prodMap_of_isProper ℓ c.overG)
  rwa [hf] at this

end AlgebraicGeometry.ProEtale.CondensedRing
