/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# The exceptional inverse image on `Loc(Dᵇc)`, `ℓ`-adic coefficients

Let `Λ` be a commutative condensed ring. For a scheme `X` the localizing closure
`Loc(Dᵇc(X)⟦Λ⟧)` (blueprint `sk-def-localizing-closure`) is the smallest triangulated
subcategory of `D(X_proét, Λ_X)` (module objects over `Λ_X = p_X^* Λ`) containing the bounded
constructible complexes `Dᵇc(X)⟦Λ⟧` and closed under direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`). For the `ℓ`-adic
coefficient rings `Λ = 𝒪_E, E, ℚ̄_ℓ` (`ℤ_ℓ` and `ℚ_ℓ` being the case `E = ℚ_ℓ`), one has
`Dctf(X, Λ) = Dᵇc(X, Λ)`, so this is the blueprint's `Loc(Dctf(X, Λ))`.

For a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f : X ⟶ Y` such that `Rf_!(c)⟦Λ⟧` maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)`, its restriction is the functor
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)`
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekLocalizing`). Under the
hypotheses of Brown representability (blueprint `sk-lem-brown-hypotheses`) and the properties of
`Rf_!(c)` of blueprint `det-sf-comp-coherence-single`, it has an exact right adjoint `f^!`,
which preserves direct sums and is unique up to unique isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_rightAdjoint_rightDerivedLowerShriekLocalizing`,
blueprint `sk-prop-sf-existence`). This is uniform in `Λ`.

For the three families of `ℓ`-adic coefficient rings, schemes separated of finite type over a
field `k` in which `ℓ` is invertible, the two inputs are stated as `sorry`ed theorems, and the
existence theorem follows:

| `Λ` | `sk-lem-brown-hypotheses` | `det-sf-comp-coherence-single` |
| --- | --- | --- |
| `E` | `compactlyGenerates_continuousMapRingObj` | `lowerShriek_continuousMapRingObj` |
| `𝒪_E` | `compactlyGenerates_padicIntegersRingObj` | `lowerShriek_padicIntegersRingObj` |
| `ℚ̄_ℓ` | `compactlyGenerates_padicAlgClRingObj` | `lowerShriek_padicAlgClRingObj` |

(all in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`). The finite coefficient rings
are treated in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Blueprint `sk-def-localizing-closure`: the localizing closure `Loc(Dᵇc(X)⟦Λ⟧)`, the smallest
triangulated subcategory of `D(X_proét, Λ_X)` closed under isomorphisms and direct sums which
contains the bounded constructible complexes. For the `ℓ`-adic coefficient rings these are the
blueprint's `Dctf(X, Λ)`. -/
noncomputable abbrev localizingBoundedConstructible (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  (boundedConstructible (condensedRingObj Λ X)).localizingClosure

/-- The category `Loc(Dᵇc(X)⟦Λ⟧)`, a full subcategory of `D(X_proét, Λ_X)`. It is
pretriangulated and has direct sums. -/
abbrev LocalizingBoundedConstructible (X : Scheme.{u}) : Type _ :=
  (localizingBoundedConstructible Λ X).FullSubcategory

/-- The derived category `D(X_proét, Λ_X)` of module objects has direct sums. -/
instance hasCoproducts_derivedCategory (X : Scheme.{u}) :
    HasCoproducts.{u + 1} (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) := by
  intro J
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  exact DerivedCategory.hasColimitsOfShape_discrete J

section General

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The properties of the compact-support direct image `Rf_!(c)⟦Λ⟧ = Rp_* ∘ j_!` along a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of blueprint `det-sf-comp-coherence-single`: it maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)` and `Dᵇc(X)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧`, and its restriction
to `Loc(Dᵇc(X)⟦Λ⟧)` preserves direct sums. -/
def LowerShriekLocalizingHypotheses : Prop :=
  (∀ K, localizingBoundedConstructible Λ X K →
    localizingBoundedConstructible Λ Y ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  (∀ K, boundedConstructible (condensedRingObj Λ X) K →
    boundedConstructible (condensedRingObj Λ Y)
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
    ((localizingBoundedConstructible Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)

variable {Λ c} (hc : LowerShriekLocalizingHypotheses Λ c)

/-- The compact-support direct image `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` attached to a
compactification `c` of `f`: the restriction of `Rf_!(c)⟦Λ⟧`. -/
noncomputable abbrev rightDerivedLowerShriekLocalizing :
    LocalizingBoundedConstructible Λ X ⥤ LocalizingBoundedConstructible Λ Y :=
  ObjectProperty.localizingClosureLift _ _ (rightDerivedLowerShriekOfCompactification Λ c) hc.1

/-- `Rf_!` on the localizing closures preserves direct sums (blueprint
`det-sf-comp-coherence-single`). -/
instance (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) (rightDerivedLowerShriekLocalizing hc) :=
  have := hc.2.2 J
  ObjectProperty.preservesColimitsOfShape_localizingClosureLift _ _ _ _ J

omit [IsCommMonObj Λ] in
/-- Blueprint `sk-prop-sf-existence`, uniformly in the coefficient ring `Λ`: if
`Dᵇc(X)⟦Λ⟧` and `Dᵇc(Y)⟦Λ⟧` compactly generate their localizing closures (blueprint
`sk-lem-brown-hypotheses`) and `Rf_!(c)⟦Λ⟧` has the properties of blueprint
`det-sf-comp-coherence-single`, then the coproduct-preserving functor
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` has a right adjoint `f^!`, which commutes with shifts
compatibly with the adjunction, is exact (triangulated), preserves direct sums and is unique up
to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing
    (hX : (boundedConstructible (condensedRingObj Λ X)).CompactlyGeneratesLocalizingClosure)
    (hY : (boundedConstructible (condensedRingObj Λ Y)).CompactlyGeneratesLocalizingClosure) :
    ∃ (G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X)
      (adj : rightDerivedLowerShriekLocalizing hc ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X)
        (adj' : rightDerivedLowerShriekLocalizing hc ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing hc).map (e.hom.app N) ≫
          adj'.counit.app N = adj.counit.app N :=
  have := hc.2.2
  ObjectProperty.exists_rightAdjoint_localizingClosureLift _ _ _ _ hX hY hc.2.1

end General

/-! ### The `ℓ`-adic coefficient rings -/

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-- Blueprint `sk-lem-brown-hypotheses`: Hypotheses of Brown representability, for the
coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` (including `E = ℚ_ℓ`) and a separated
finite-type `k`-scheme `X`. The category `Loc(Dᵇc(X)⟦E⟧)` is locally small, triangulated and has
direct sums (by construction); it has split idempotents, and `Dᵇc(X)⟦E⟧ = Dctf(X, E)` is
essentially small, with a small skeleton forming a set of compact generators. -/
theorem compactlyGenerates_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible (Profinite.continuousMapRingObj E) X) :=
  sorry

/-- Blueprint `det-sf-comp-coherence-single`: Compact support along one compactification on the
localizing category, for the coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` and a
quasi-compact quasi-separated `k`-scheme `Y`: for a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)`
of `f`, `Rp_* ∘ j_!` maps `Loc(Dctf(X, E))` into `Loc(Dctf(Y, E))` and `Dctf(X, E)` into
`Dctf(Y, E)`, and preserves direct sums on `Loc(Dctf(X, E))`. -/
theorem lowerShriek_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [CompactSpace Y] [QuasiSeparatedSpace Y]
    {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.continuousMapRingObj.{u} E) c :=
  sorry

/-- `lowerShriek_continuousMapRingObj` for a separated finite-type `k`-scheme `Y`, which is
quasi-compact and quasi-separated. -/
theorem lowerShriek_continuousMapRingObj_of_finiteType (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.continuousMapRingObj.{u} E) c :=
  have := QuasiCompact.compactSpace_of_compactSpace aY
  have := quasiSeparatedSpace_of_quasiSeparated aY
  lowerShriek_continuousMapRingObj ℓ E aY c

/-- Blueprint `sk-lem-brown-hypotheses`: Hypotheses of Brown representability, for the
coefficient ring `𝒪_E` of the ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(including `ℤ_ℓ`, for `E = ℚ_ℓ`) and a separated finite-type `k`-scheme `X`: `Loc(Dᵇc(X)⟦𝒪_E⟧)`
has split idempotents, and `Dᵇc(X)⟦𝒪_E⟧ = Dctf(X, 𝒪_E)` is essentially small, with a small
skeleton forming a set of compact generators. -/
theorem compactlyGenerates_padicIntegersRingObj (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX] :
    (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete
        (LocalizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X) :=
  sorry

/-- Blueprint `det-sf-comp-coherence-single`: Compact support along one compactification on the
localizing category, for the coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
and a quasi-compact quasi-separated `k`-scheme `Y`: for a compactification
`c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, `Rp_* ∘ j_!` maps `Loc(Dctf(X, 𝒪_E))` into `Loc(Dctf(Y, 𝒪_E))`
and `Dctf(X, 𝒪_E)` into `Dctf(Y, 𝒪_E)`, and preserves direct sums on `Loc(Dctf(X, 𝒪_E))`. -/
theorem lowerShriek_padicIntegersRingObj (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [CompactSpace Y] [QuasiSeparatedSpace Y]
    {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) c :=
  sorry

/-- `lowerShriek_padicIntegersRingObj` for a separated finite-type `k`-scheme `Y`, which is
quasi-compact and quasi-separated. -/
theorem lowerShriek_padicIntegersRingObj_of_finiteType (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] {f : X ⟶ Y}
    (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) c :=
  have := QuasiCompact.compactSpace_of_compactSpace aY
  have := quasiSeparatedSpace_of_quasiSeparated aY
  lowerShriek_padicIntegersRingObj ℓ E aY c

/-- Blueprint `sk-lem-brown-hypotheses`: Hypotheses of Brown representability, for the
coefficient ring `ℚ̄_ℓ` and a separated finite-type `k`-scheme `X`: `Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)` has split
idempotents, and `Dᵇc(X)⟦ℚ̄_ℓ⟧ = Dctf(X, ℚ̄_ℓ)` is essentially small, with a small skeleton
forming a set of compact generators. -/
theorem compactlyGenerates_padicAlgClRingObj {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) :=
  sorry

/-- Blueprint `det-sf-comp-coherence-single`: Compact support along one compactification on the
localizing category, for the coefficient ring `ℚ̄_ℓ` and a quasi-compact quasi-separated
`k`-scheme `Y`: for a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, `Rp_* ∘ j_!` maps
`Loc(Dctf(X, ℚ̄_ℓ))` into `Loc(Dctf(Y, ℚ̄_ℓ))` and `Dctf(X, ℚ̄_ℓ)` into `Dctf(Y, ℚ̄_ℓ)`, and
preserves direct sums on `Loc(Dctf(X, ℚ̄_ℓ))`. -/
theorem lowerShriek_padicAlgClRingObj {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [CompactSpace Y] [QuasiSeparatedSpace Y] {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) c :=
  sorry

/-- `lowerShriek_padicAlgClRingObj` for a separated finite-type `k`-scheme `Y`, which is
quasi-compact and quasi-separated. -/
theorem lowerShriek_padicAlgClRingObj_of_finiteType {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] {f : X ⟶ Y}
    (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) c :=
  have := QuasiCompact.compactSpace_of_compactSpace aY
  have := quasiSeparatedSpace_of_quasiSeparated aY
  lowerShriek_padicAlgClRingObj ℓ aY c

variable {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)

include aX in
/-- Blueprint `sk-prop-sf-existence`: Existence of the exceptional inverse image, for the
coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` (including `ℚ_ℓ`) and separated
finite-type `k`-schemes `X`, `Y`. For a compactification `c` of `f : X ⟶ Y`, the
coproduct-preserving functor `Rf_! : Loc(Dctf(X, E)) ⥤ Loc(Dctf(Y, E))` has a right adjoint
`f^!`, which commutes with shifts compatibly with the adjunction, is exact (triangulated),
preserves direct sums and is unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (G : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
        LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_continuousMapRingObj_of_finiteType ℓ E aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
          LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_continuousMapRingObj_of_finiteType ℓ E aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_continuousMapRingObj_of_finiteType ℓ E aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_continuousMapRingObj ℓ E aX).1
    (compactlyGenerates_continuousMapRingObj ℓ E aY).1

include aX in
/-- Blueprint `sk-prop-sf-existence`: Existence of the exceptional inverse image, for the
coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (including `ℤ_ℓ`) and
separated finite-type `k`-schemes `X`, `Y`. For a compactification `c` of `f : X ⟶ Y`, the
coproduct-preserving functor `Rf_! : Loc(Dctf(X, 𝒪_E)) ⥤ Loc(Dctf(Y, 𝒪_E))` has a right adjoint
`f^!`, which commutes with shifts compatibly with the adjunction, is exact (triangulated),
preserves direct sums and is unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (G : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
        LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_padicIntegersRingObj_of_finiteType ℓ E aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
          LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_padicIntegersRingObj_of_finiteType ℓ E aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_padicIntegersRingObj_of_finiteType ℓ E aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_padicIntegersRingObj ℓ E aX).1
    (compactlyGenerates_padicIntegersRingObj ℓ E aY).1

include aX in
/-- Blueprint `sk-prop-sf-existence`: Existence of the exceptional inverse image, for the
coefficient ring `ℚ̄_ℓ` and separated finite-type `k`-schemes `X`, `Y`. For a compactification
`c` of `f : X ⟶ Y`, the coproduct-preserving functor
`Rf_! : Loc(Dctf(X, ℚ̄_ℓ)) ⥤ Loc(Dctf(Y, ℚ̄_ℓ))` has a right adjoint `f^!`, which commutes with
shifts compatibly with the adjunction, is exact (triangulated), preserves direct sums and is
unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj :
    ∃ (G : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
        LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_padicAlgClRingObj_of_finiteType ℓ aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
          LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_padicAlgClRingObj_of_finiteType ℓ aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_padicAlgClRingObj_of_finiteType ℓ aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_padicAlgClRingObj ℓ aX).1 (compactlyGenerates_padicAlgClRingObj ℓ aY).1

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
