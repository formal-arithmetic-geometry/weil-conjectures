/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# The exceptional inverse image on bounded constructible module objects

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
separated and of finite type over `Spec k`, and all morphisms are morphisms of
`Over (Spec (.of k))`.

The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` is constructed on the bounded
constructible derived categories directly, out of the two halves of the derived lower shriek
attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
```
Rf_!(c) := i_! ⋙ Rg_*,      Rf^!(c) := Rg^! ⋙ i^*,
```
where `i_! ⊣ i^*` is the adjunction along the open immersion `i` on bounded constructible
complexes (`boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction`) and `Rg^!` is a
chosen right adjoint of the bounded constructible pushforward `Rg_*` along the proper `g`. The
adjunction `Rf_!(c) ⊣ Rf^!(c)` is the composite of these two adjunctions.

The only input is that `Rg_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` is a left adjoint for proper `g`. The
constructions take it as an instance argument, and it is assumed (`sorry`) for the `ℓ`-adic
coefficient rings only: the condensed ring `E̲ = C(-, E)` of a finite extension `E` of `ℚ_ℓ`
(`Profinite.continuousMapRingObj E`), the condensed ring `𝒪̲_E = C(-, 𝒪_E)` of its ring of
integers, for `E ⊆ ℚ̄_ℓ` (`Profinite.padicIntegersRingObj ℓ E`), and the condensed ring `ℚ̲̄_ℓ`
(`Profinite.padicAlgClRingObj ℓ`).

Exactly as the lower shriek `boundedConstructibleLowerShriek`, the functor `Rf^!` is `Rf^!(c)`
for the compactification `c = compactificationOverField f` chosen by Nagata's theorem, and the
adjunction `Rf_! ⊣ Rf^!` is the adjunction `Rf_!(c) ⊣ Rf^!(c)`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification`: `Rf^!(c)` on
  bounded constructible complexes, right adjoint to the lower shriek
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction`: the
  adjunction `Rf_!(c) ⊣ Rf^!(c)`.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriek`: `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` for
  the chosen compactification, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`: the adjunction
  `Rf_! ⊣ Rf^!`.

## Sorried input

- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_of_isProper`: for `g`
  proper and an `ℓ`-adic coefficient ring `Λ`, `Rg_*` on bounded constructible complexes is a left
  adjoint.

## Implementation notes

`Rg^!` for proper `g` is `Functor.rightAdjoint`, an arbitrary choice of right adjoint extracted
from the instance, not a construction. Only the adjunction `Adjunction.ofIsLeftAdjoint` should be
used about it.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The adjunction along a compactification -/

section OfCompactification

include ℓ k

variable {ℓ} (Λ : Profinite.EllAdicCoefficient ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

variable [(boundedConstructibleLowerStar Λ c.overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen right adjoint `Rg^!`
of the derived pushforward `Rg_*` along the proper `g`, followed by the pullback `i^*` along the
open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification :
    Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructibleLowerStar Λ c.overG).rightAdjoint ⋙
    boundedConstructibleUpperStar Λ ℓ c.overI

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the composite of the adjunction `i_! ⊣ i^*`
along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification Λ c ⊣
      boundedConstructibleUpperShriekOfCompactification Λ c :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ c.overI).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The lower shriek `Rf_!(c)` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperShriekOfCompactification`. -/
instance isLeftAdjoint_boundedConstructibleLowerShriekOfCompactification :
    (boundedConstructibleLowerShriekOfCompactification Λ c).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction Λ c).isLeftAdjoint

/-- The exceptional inverse image `Rf^!(c)` on bounded constructible complexes is a right
adjoint, its left adjoint being `boundedConstructibleLowerShriekOfCompactification`. -/
instance isRightAdjoint_boundedConstructibleUpperShriekOfCompactification :
    (boundedConstructibleUpperShriekOfCompactification Λ c).IsRightAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction Λ c).isRightAdjoint

end OfCompactification

/-! ### The adjunction `Rf_! ⊣ Rf^!` -/

section Chosen

include ℓ k

variable {ℓ} (Λ : Profinite.EllAdicCoefficient ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

variable [(boundedConstructibleLowerStar Λ (compactificationOverField f).overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification` attached to the chosen
compactification `compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  boundedConstructibleUpperShriekOfCompactification Λ (compactificationOverField f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the adjunction
`Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek Λ f ⊣ boundedConstructibleUpperShriek Λ f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction Λ
    (compactificationOverField f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek`. -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek Λ f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ f).isLeftAdjoint

instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek Λ f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ f).isRightAdjoint

end Chosen

/-! ### The proper pushforward for the `ℓ`-adic coefficient rings -/

section EllAdic

include k

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

variable {ℓ} in
/-- For a proper morphism `g : Z ⟶ Y` and an `ℓ`-adic coefficient ring `Λ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes is a left adjoint;
its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
lemma isLeftAdjoint_boundedConstructibleLowerStar_of_isProper
    (Λ : Profinite.EllAdicCoefficient ℓ) :
    (boundedConstructibleLowerStar Λ g).IsLeftAdjoint :=
  sorry

/-- `isLeftAdjoint_boundedConstructibleLowerStar_of_isProper` for `E̲`, `E` a finite extension of
`ℚ_ℓ`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (.field ℓ E) g).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_of_isProper g _

/-- `isLeftAdjoint_boundedConstructibleLowerStar_of_isProper` for `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite
extension of `ℚ_ℓ`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (.integers ℓ E) g).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_of_isProper g _

/-- `isLeftAdjoint_boundedConstructibleLowerStar_of_isProper` for `ℚ̲̄_ℓ`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar (.algClosure ℓ) g).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_of_isProper g _

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
