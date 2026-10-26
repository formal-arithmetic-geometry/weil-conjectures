/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# The exceptional inverse image along an open immersion

Let `ℓ` be a prime, `k` a field of characteristic `p > 0` with `p ≠ ℓ`, and `j : U ⟶ X` a
morphism of separated `k`-schemes of finite type whose underlying morphism of schemes is an open
immersion. This file identifies the six functors along `j` on bounded constructible
`ℚ̄_ℓ`-complexes, canonically, without any choice:

* the lower shriek `Rj_!`, defined through the compactification of `j` chosen by Nagata's
  theorem, is the extension by zero `j_!`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`):
  by independence of the compactification, `Rj_!` is computed by the trivial compactification
  `U ⟶[j] X ⟶[𝟙] X`, which gives `j_! ⋙ R(𝟙 X)_* ≅ j_!`;
* the exceptional inverse image `Rj^!` is the pullback `j^*`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl`), the
  conjugate of the previous isomorphism under the adjunctions `Rj_! ⊣ Rj^!` and `j_! ⊣ j^*`;
* in particular `Rj^! ℚ̄_ℓ,X ≅ j^* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,U`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`), through the unit
  isomorphism of the monoidal functor `j^*`. This is smooth purity in relative dimension zero
  for open immersions, with its canonical normalization.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The identification of `X` with the middle object of the compactification
`U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`. -/
noncomputable def openImmersionCompactificationHom :
    X ⟶ (Compactification.ofIsOpenImmersion j.left).overObj :=
  Over.homMk (𝟙 X.left) (by
    change 𝟙 X.left ≫ 𝟙 X.left ≫ X.hom = X.hom
    simp)

instance : IsIso (openImmersionCompactificationHom j) := by
  have : IsIso ((Over.forget _).map (openImmersionCompactificationHom j)) :=
    inferInstanceAs (IsIso (𝟙 X.left))
  exact isIso_of_reflects_iso _ (Over.forget _)

instance : IsProper (openImmersionCompactificationHom j).left :=
  inferInstanceAs (IsProper (𝟙 X.left))

omit [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma isPullback_openImmersionCompactificationHom :
    IsPullback (𝟙 U) j (Compactification.ofIsOpenImmersion j.left).overI
      (openImmersionCompactificationHom j) :=
  IsPullback.of_horiz_isIso ⟨by ext; simp [openImmersionCompactificationHom]; rfl⟩

omit [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma openImmersionCompactificationHom_comp_overG :
    openImmersionCompactificationHom j ≫ (Compactification.ofIsOpenImmersion j.left).overG =
      𝟙 X := by
  ext
  simp [openImmersionCompactificationHom, Compactification.overG]
  rfl

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The lower shriek along an open immersion is the extension by zero, `Rj_! ≅ j_!`, on bounded
constructible `ℚ̄_ℓ`-complexes: by independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl`), `Rj_!` is `j_! ⋙ R(𝟙 X)_*`
for the trivial compactification `U ⟶[j] X ⟶[𝟙] X`
(`AlgebraicGeometry.Compactification.ofIsOpenImmersion`), and `R(𝟙 X)_* ≅ 𝟭`. -/
noncomputable def boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl :
    boundedConstructibleLowerShriek ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (compactificationOverField j) (.ofIsOpenImmersion j.left) ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
      (boundedConstructibleLowerStarId ℓ X) ≪≫
    Functor.rightUnitor _

/-- The exceptional inverse image along an open immersion is the pullback, `Rj^! ≅ j^*`, on
bounded constructible `ℚ̄_ℓ`-complexes: the conjugate of
`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl` under the adjunctions
`Rj_! ⊣ Rj^!` and `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl :
    boundedConstructibleUpperShriek ℓ j ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).symm

/-- **Purity for an open immersion**, `Rj^! ℚ̄_ℓ,X ≅ ℚ̄_ℓ,U`: the isomorphism `Rj^! ≅ j^*` of
`boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl` at the unit, followed by the unit
isomorphism of the monoidal functor `j^*`. -/
noncomputable def boundedConstructibleUpperShriekUnitIso_padicAlgCl :
    (boundedConstructibleUpperShriek ℓ j).obj
        (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≅
      𝟙_ (Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).app _ ≪≫
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).symm

end AlgebraicGeometry.ProEtale.CondensedRing
