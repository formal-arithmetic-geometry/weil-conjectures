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
separated and of finite type over `Spec k`, and all morphisms are morphisms over `Spec k`.

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
for the compactification `c = compactificationOverField k f` chosen by Nagata's theorem, and the
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

- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `E`-sheaves is a left adjoint.
- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `𝒪_E`-sheaves is a left adjoint.
- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `ℚ̄_ℓ`-sheaves is a left adjoint.

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
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The adjunction along a compactification -/

section OfCompactification

include ℓ k

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))] (c : Compactification f)

variable [(boundedConstructibleLowerStar Λ ℓ k c.g).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen right adjoint `Rg^!`
of the derived pushforward `Rg_*` along the proper `g`, followed by the pullback `i^*` along the
open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  (boundedConstructibleLowerStar Λ ℓ k c.g).rightAdjoint ⋙
    boundedConstructibleUpperStar Λ ℓ k c.i

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the composite of the adjunction `i_! ⊣ i^*`
along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ k c ⊣
      boundedConstructibleUpperShriekOfCompactification Λ ℓ k c :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ k c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

end OfCompactification

/-! ### The adjunction `Rf_! ⊣ Rf^!` -/

section Chosen

include ℓ k

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

variable [(boundedConstructibleLowerStar Λ ℓ k (compactificationOverField k f).g).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification` attached to the chosen
compactification `compactificationOverField k f`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  boundedConstructibleUpperShriekOfCompactification Λ ℓ k (compactificationOverField k f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the adjunction
`Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField k f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek Λ ℓ k f ⊣ boundedConstructibleUpperShriek Λ ℓ k f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction Λ ℓ k
    (compactificationOverField k f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek`. -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek Λ ℓ k f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ k f).isLeftAdjoint

instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek Λ ℓ k f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ k f).isRightAdjoint

end Chosen

/-! ### The proper pushforward for the `ℓ`-adic coefficient rings -/

section EllAdic

include k

variable {Z Y : Scheme.{u}} [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (g : Z ⟶ Y) [IsProper g] [g.IsOver (Spec (.of k))]

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible `E`-sheaves is a left
adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k g).IsLeftAdjoint :=
  sorry

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible `𝒪_E`-sheaves is a
left adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E) ℓ k g).IsLeftAdjoint :=
  sorry

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible `ℚ̄_ℓ`-sheaves is a left adjoint;
its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k g).IsLeftAdjoint :=
  sorry

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
