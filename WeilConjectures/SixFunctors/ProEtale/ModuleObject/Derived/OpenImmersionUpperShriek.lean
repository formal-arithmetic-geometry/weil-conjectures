/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# The exceptional functors of an open immersion

Let `j : U ⟶ X` be an open immersion of separated `k`-schemes of finite type. Its derived lower
shriek `Rj_!` on bounded constructible `ℚ̄_ℓ`-sheaves, defined through the chosen compactification
of `j`, is the extension by zero `j_!`: by independence of the compactification it is computed
by the compactification `U ⟶[j] X ⟶[𝟙] X`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`).
Taking right adjoints, the exceptional inverse image `Rj^!` is the pullback `Lj^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl`): this is the
canonical form of purity in relative dimension zero for open immersions.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

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

/-- For an open immersion `j`, the derived lower shriek `Rj_!` on bounded constructible
`ℚ̄_ℓ`-sheaves is the extension by zero `j_!`: by independence of the compactification, `Rj_!` is
computed by the compactification `U ⟶[j] X ⟶[𝟙] X`. -/
noncomputable def boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (isPullback_openImmersionCompactificationHom j)
  boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ _
      (Compactification.ofIsOpenImmersion j.left) ≪≫
    boundedConstructibleLowerShriekRefinementIso' _ ℓ
      (isPullback_openImmersionCompactificationHom j)
      (openImmersionCompactificationHom_comp_overG j) ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarId _ ℓ X) ≪≫ Functor.rightUnitor _

/-- **Purity for open immersions**: for an open immersion `j`, the exceptional inverse image
`Rj^!` on bounded constructible `ℚ̄_ℓ`-sheaves is the pullback `Lj^*`, the conjugate of
`Rj_! ≅ j_!` for the adjunctions `Rj_! ⊣ Rj^!` and `j_! ⊣ Lj^*`. -/
noncomputable def boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl :
    boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  (conjugateIsoEquiv
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)).symm

end AlgebraicGeometry.ProEtale.CondensedRing
