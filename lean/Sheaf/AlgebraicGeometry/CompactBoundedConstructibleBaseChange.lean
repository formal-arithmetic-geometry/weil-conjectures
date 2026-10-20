/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible

/-!
# Bounded constructibility and base change for compact direct images

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-fin-compact-bounded-and-base-change.md`, statement and proof
(blueprint: lem-fin-compact-bounded-and-base-change).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

private theorem boundedConstructible_iff (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) (K : DerivedCategoryModule Λ T) :
    DerivedCategory.isBoundedConstructible Λ T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K := by
  constructor
  · rintro ⟨hc, a, b, hab, hvan⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩,
      fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hvan i (Or.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦ hvan i (Or.inr hi)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i
        (lt_of_le_of_lt (le_max_right _ _) hi)

/-- Compact direct image preserves bounded constructibility over a field of characteristic
other than `ℓ`, and its specified exchange is invertible after every Noetherian base change.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-fin-compact-bounded-and-base-change.md`
(blueprint: lem-fin-compact-bounded-and-base-change).

The coefficient ring is the universe lift of the prime field `ZMod ℓ`. A bounded constructible
complex is viewed in `D⁺`, with the constructibility and two-sided bound imposed on its underlying
object in `D`. The compactification `c` computes the candidate `Rp_* j_!`; its base change computes
the target of the exchange, exactly as in `def-cbc-exchange-map`.

Proof: Convert bounded constructibility to the source library's equivalent formulation:
constructible cohomology for the finite coefficient ring, and boundedness for the standard
t-structure. The comparison of finite-value and finite-stalk constructibility is
`Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`; the interval bounds are exactly
`DerivedCategory.isGE_iff` and `DerivedCategory.isLE_iff`.
The supplied compactification already gives the proper map `c.g` and open immersion `c.i`.
Its ambient scheme is Noetherian because `c.g ≫ aS` is finite type over a field, so `c.i` is
quasi-compact. Exact extension by zero preserves bounded constructibility by
`boundedConstructible_mapDerivedCategory_openImmersionLowerShriek`.
The prime field is killed by `ℓ`; its positive exponent is invertible on every scheme
mapping to `Spec k`, by applying the global-sections ring maps to the unit `(ℓ : k)`.
Apply `isBoundedConstructible_rightDerivedLowerStar_of_proper` to `c.g`, with structure
morphism `c.g ≫ aS`, and convert the extension-by-zero complex back to the project predicate.
For base change use the existing instance
`isIso_rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, evaluated at `K`.
It applies to precisely the specified compactification and arbitrary Cartesian square;
its proof assembles proper base change and extension-by-zero base change. -/
theorem isBoundedConstructible_compactSupport_and_baseChange
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] (hℓ : (ℓ : k) ≠ 0)
    {X S : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aS = aX) (c : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))))
    (hK : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X K.obj) :
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) S
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) c).obj K.obj) ∧
    ∀ (S' : Scheme.{u}) [IsNoetherian S'] (v : S' ⟶ S)
      (X' : Scheme.{u}) (vX : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback vX f' f v),
      IsIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        (ULift.{u + 1} (ZMod ℓ)) sq c).app K) := by
  have hcompat := hf
  let Λ := ULift.{u + 1} (ZMod ℓ)
  have hcoeff (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) :
      IsSmoothBaseChangeCoefficients ℓ Λ T := by
    refine ⟨(Fact.out : ℓ.Prime).pos, inferInstance, ?_, ?_⟩
    · apply ULift.down_injective
      simp [Λ]
    · have hu : IsUnit (ℓ : Γ(Spec (.of k), ⊤)) := by
        simpa using (Ne.isUnit hℓ).map (Scheme.ΓSpecIso (.of k)).inv.hom
      simpa using hu.map aT.appTop.hom
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian c.Z :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aS)
      __ := QuasiCompact.compactSpace_of_compactSpace c.g }
  refine ⟨?_, ?_⟩
  · have hj := boundedConstructible_mapDerivedCategory_openImmersionLowerShriek Λ c.i
      ((boundedConstructible_iff Λ X K.obj).1 hK)
    exact isBoundedConstructible_rightDerivedLowerStar_of_proper Λ ℓ
      (c.g ≫ aS) aS c.g rfl (hcoeff _ (c.g ≫ aS)) (hcoeff _ aS) _
      ((boundedConstructible_iff Λ c.Z _).2 hj)
  · intro S' _ v X' vX f' sq
    infer_instance

end AlgebraicGeometry.Etale
