/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability
import Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible

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
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The adjunction along a compactification -/

section OfCompactification

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

variable [IsFinitenessCoefficient ℓ Λ]

variable [(boundedConstructibleLowerStar Λ ℓ c.overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen right adjoint `Rg^!`
of the derived pushforward `Rg_*` along the proper `g`, followed by the pullback `i^*` along the
open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification :
    Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructibleLowerStar Λ ℓ c.overG).rightAdjoint ⋙
    boundedConstructibleUpperStar Λ ℓ c.overI

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the composite of the adjunction `i_! ⊣ i^*`
along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⊣
      boundedConstructibleUpperShriekOfCompactification Λ ℓ c :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ c.overI).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The lower shriek `Rf_!(c)` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperShriekOfCompactification`. -/
instance isLeftAdjoint_boundedConstructibleLowerShriekOfCompactification :
    (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction Λ ℓ c).isLeftAdjoint

/-- The exceptional inverse image `Rf^!(c)` on bounded constructible complexes is a right
adjoint, its left adjoint being `boundedConstructibleLowerShriekOfCompactification`. -/
instance isRightAdjoint_boundedConstructibleUpperShriekOfCompactification :
    (boundedConstructibleUpperShriekOfCompactification Λ ℓ c).IsRightAdjoint :=
  (boundedConstructibleUpperShriekOfCompactificationAdjunction Λ ℓ c).isRightAdjoint

end OfCompactification

/-! ### The adjunction `Rf_! ⊣ Rf^!` -/

section Chosen

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

variable [IsFinitenessCoefficient ℓ Λ]

variable [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification` attached to the chosen
compactification `compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  boundedConstructibleUpperShriekOfCompactification Λ ℓ (compactificationOverField f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the adjunction
`Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek Λ ℓ f ⊣ boundedConstructibleUpperShriek Λ ℓ f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction Λ ℓ
    (compactificationOverField f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek`. -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek Λ ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ f).isLeftAdjoint

instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek Λ ℓ f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ f).isRightAdjoint

end Chosen

/-! Upstream declarations retained; generic interface is separate. -/

/-! ### The proper pushforward for the `ℓ`-adic coefficient rings. -/

section EllAdic

include k

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- Restrict the localizing adjunction along the full bounded constructible inclusions. -/
private theorem isLeftAdjoint_boundedConstructibleLowerStar_of_ellAdic
    [IsFinitenessCoefficient ℓ Λ]
    (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) :
    (boundedConstructibleLowerStar Λ ℓ g).IsLeftAdjoint := by
  let F := ellAdicLocalizingLowerStar Λ ℓ g hΛ
  have : F.IsLeftAdjoint := ellAdic_isLeftAdjoint_localizingLowerStar Λ ℓ g hΛ
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  let Gbc : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(Z.left)⟦Λ⟧ :=
    (boundedConstructible (condensedRingObj Λ Z.left)).lift
      (boundedConstructibleToLocalizing Λ Y.left ⋙ G ⋙
        (boundedConstructibleLocalizingClosure Λ Z.left).ι)
      (fun K ↦ ellAdic_localizing_rightAdjoint_obj_boundedConstructible Λ ℓ g hΛ G adj K)
  let iZ := boundedConstructibleToLocalizing Λ Z.left
  let iY := boundedConstructibleToLocalizing Λ Y.left
  have hiZ : iZ.FullyFaithful :=
    ObjectProperty.fullyFaithfulιOfLE (boundedConstructible_le_localizingClosure Λ Z.left)
  have hiY : iY.FullyFaithful :=
    ObjectProperty.fullyFaithfulιOfLE (boundedConstructible_le_localizingClosure Λ Y.left)
  have eF : iZ ⋙ F ≅ boundedConstructibleLowerStar Λ ℓ g ⋙ iY :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (fun a ↦ by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  have eG : iY ⋙ G ≅ Gbc ⋙ iZ :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (fun a ↦ by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  exact (Adjunction.restrictFullyFaithful adj hiZ hiY eF eG).isLeftAdjoint

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible `E`-sheaves is a left
adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ g).IsLeftAdjoint := by
  exact isLeftAdjoint_boundedConstructibleLowerStar_of_ellAdic _ ℓ g (.continuous E)

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible `𝒪_E`-sheaves is a
left adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E) ℓ g).IsLeftAdjoint := by
  exact isLeftAdjoint_boundedConstructibleLowerStar_of_ellAdic _ ℓ g (.integral E)

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible `ℚ̄_ℓ`-sheaves is a left adjoint;
its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g).IsLeftAdjoint := by
  exact isLeftAdjoint_boundedConstructibleLowerStar_of_ellAdic _ ℓ g .algebraicClosure

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
