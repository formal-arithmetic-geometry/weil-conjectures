/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!

# The lower shriek along a proper morphism

Let `f : X ⟶ Y` be a proper morphism of separated `k`-schemes of finite type. Then `f` is its
own compactification `X ⟶[𝟙] X ⟶[f] Y` (`AlgebraicGeometry.Compactification.ofIsProper`), for
which `Rf_!^c = (𝟙)_! ⋙ Rf_*` is `Rf_*`, the extension by zero along the identity being the
identity. By independence of the lower shriek from the compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'`), this gives
`Rf_! ≅ Rf_*` on bounded constructible `E`- and `ℚ̄_ℓ`-sheaves.

## Main definitions

- `ProEtale.CondensedRing.openImmersionLowerShriekId` and
  `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId`: the identity isomorphisms
  `(𝟙 X)_! ≅ 𝟭` on module objects over `Λ` and on their derived category, obtained from the
  identity isomorphism `(𝟙 X)^* ≅ 𝟭` (`ProEtale.CondensedRing.upperStarId`) by uniqueness of
  left adjoints.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationOfIsProperIso`:
  `Rf_!^c ≅ Rf_*` for the trivial compactification `c` of a proper `f`, for any `Λ`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`: the
  isomorphism `Rf_! ≅ Rf_*` for a proper `f`, for `E`- and `ℚ̄_ℓ`-sheaves.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The extension by zero along the identity -/

section Id

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (X : Scheme.{u})

/-- The identity isomorphism `(𝟙 X)_! ≅ 𝟭` of the extension by zero along the identity on module
objects over `Λ`, obtained from the identity isomorphism `ProEtale.CondensedRing.upperStarId` of
the pullback by uniqueness of left adjoints: both are left adjoint to `(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def openImmersionLowerShriekId : (𝟙 X)_!open⟦Λ⟧ ≅ 𝟭 _ :=
  ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
    (upperStarId Λ X)).leftAdjointUniq Adjunction.id

/-- The identity isomorphism `D((𝟙 X)_!) ≅ 𝟭` of the levelwise extension by zero along the
identity on the derived category of module objects over `Λ`. -/
noncomputable def derivedOpenImmersionLowerShriekId : D((𝟙 X)_!open⟦Λ⟧) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekId Λ X) ≪≫
    Functor.mapDerivedCategoryIdIso _

end Id

/-! ### The lower shriek of a proper morphism -/

section Proper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left]

/-- The extension by zero `i_!` on bounded constructible complexes along the open immersion
`i = 𝟙` of the trivial compactification `X ⟶[𝟙] X ⟶[f] Y` of a proper `f` is the identity: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekOfIsProperIso :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ
        (Compactification.ofIsProper f.left).overI ≅ 𝟭 (Dᵇc(X.left)⟦Λ⟧) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ
        (Compactification.ofIsProper f.left).overI ≪≫
      Functor.isoWhiskerLeft _ (derivedOpenImmersionLowerShriekId Λ X.left) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The lower shriek `Rf_!^c` attached to the trivial compactification `c = (X ⟶[𝟙] X ⟶[f] Y)`
of a proper `f` (`AlgebraicGeometry.Compactification.ofIsProper`) is the derived pushforward
`Rf_*` on bounded constructible complexes. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationOfIsProperIso
    [IsFinitenessCoefficient ℓ Λ] :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ (Compactification.ofIsProper f.left) ≅
      boundedConstructibleLowerStar Λ ℓ f :=
  Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ f) _ ≪≫
    Functor.leftUnitor _

variable (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- The isomorphism `Rf_! ≅ Rf_*` on bounded constructible `E`-sheaves for a proper `f`: by
independence of the compactification, `Rf_!` is `Rf_!^c` for the trivial compactification
`c = (X ⟶[𝟙] X ⟶[f] Y)`, which is `Rf_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekIsoLowerStar :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f ≅
      boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ f :=
  boundedConstructibleLowerShriekOfCompactificationIso' ℓ E (compactificationOverField f)
      (.ofIsProper f.left) ≪≫
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso _ ℓ f

/-- The isomorphism `Rf_! ≅ Rf_*` on bounded constructible `ℚ̄_ℓ`-sheaves for a proper `f`: by
independence of the compactification, `Rf_!` is `Rf_!^c` for the trivial compactification
`c = (X ⟶[𝟙] X ⟶[f] Y)`, which is `Rf_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ≅
      boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (compactificationOverField f) (.ofIsProper f.left) ≪≫
    boundedConstructibleLowerShriekOfCompactificationOfIsProperIso _ ℓ f

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing
