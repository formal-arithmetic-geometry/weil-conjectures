/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismComp
public import WeilConjectures.TraceFormula.OrdinaryKunnethDevissage
public import WeilConjectures.TraceFormula.GenericBaseChangePullback

/-!

# The relative Künneth formula in projection form

Let
```
P ──p₁──▶ X
│ p₂       │
▼          ▼
Y ───────▶ Spec k
```
be a cartesian square of separated `k`-schemes of finite type. For `A ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and
`W ∈ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`, the projection morphism
```
Rp₂_* (Lp₁^* A) ⊗ W ⟶ Rp₂_* (Lp₁^* A ⊗ Lp₂^* W)
```
is an isomorphism (`ProEtale.CondensedRing.isIso_projectionMorphism_upperStar_of_isPullback`,
SGA 4½ [Th. finitude] Cor. 1.11).

## Proof

Compactify `X ⟶ Spec k` as `X ⟶ X̄ ⟶ Spec k`, with `j : X ⟶ X̄` an open immersion and `X̄` proper.
Then `p₂ = e ≫ m ≫ g` with `e = (p₂, p₁) : P ⟶ Y ⨯ X` an isomorphism, `m = 𝟙 × j` and
`g : Y ⨯ X̄ ⟶ Y` the first projection, which is proper. The projection morphism of a composite is
an isomorphism if those of the factors are
(`CategoryTheory.Adjunction.isIso_projectionMorphism_of_comp`):

* for `e`, by the proper projection formula, `e` being an isomorphism; moreover the unit of
  `Le^* ⊣ Re_*` is an isomorphism;
* for `g`, by the proper projection formula
  (`isIso_projectionMorphism_boundedConstructible_padicAlgCl`);
* for `m`, at `(Lp_X^* A, Lg^* W)`, by the ordinary Künneth formula along the open immersion `j`
  (`ProEtale.CondensedRing.isIso_openKunnethMap`), through the left projection morphism
  (`ProEtale.CondensedRing.isIso_projectionMorphism_prodMap_id_of_isOpenImmersion`).

## Main statements

- `ProEtale.CondensedRing.isIso_projectionMorphism_upperStar_of_isPullback`

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

-- the tensor products are elaborated through the monoidal category instance, as in
-- `WeilConjectures.TraceFormula.OrdinaryKunneth`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Factors

variable {X Y U P Q : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]

end Factors

variable {X Y P : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
