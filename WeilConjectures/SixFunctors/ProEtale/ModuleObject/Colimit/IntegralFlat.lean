/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsSequentialColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteCondensed

/-!

# Flatness of `E_X` over `𝒪_{E,X}`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `X`
a scheme. This file proves that the coefficient ring `E_X = p_X^* E̲` is flat over
`𝒪_{E,X} = p_X^* 𝒪̲_E`: the extension of scalars along the inclusion
`ProEtale.padicIntegersToPadicSubfield X ℓ E : 𝒪_{E,X} ⟶ E_X` is exact
(`ProEtale.preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield`).

The proof follows `E = 𝒪_E[1/ℓ]`:

* on profinite sets, the maps `ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲`
  (`Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow`), for `φ` the inclusion, exhibit
  `E̲` as the sequential colimit of the multiplications by `ℓ` on `𝒪̲_E`
  (`Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone`). This is checked sectionwise:
  a continuous map from a profinite set to `E` is `ℓ⁻ᵐ` times a continuous map to `𝒪_E`
  (`PadicAlgCl.exists_norm_pow_mul_le_one`);
* the inverse image `p_X^*` is an additive left adjoint, so `E_X` is the sequential colimit of
  the multiplications by `ℓ` on `𝒪_{E,X}`;
* hence `E_X ⊗_{𝒪_{E,X}} M = colim(M --ℓ--> M --ℓ--> ⋯)` for every `𝒪_{E,X}`-module `M`, and the
  extension of scalars is exact, sequential colimits of abelian sheaves being exact
  (`CategoryTheory.Mod.preservesFiniteLimits_extendScalars_of_isColimit`).

Consequently the comparison **(Pull)** `ProEtale.CondensedRing.derivedPullIso` applies to the
inclusion `𝒪̲_E ⟶ E̲`, and restricts to bounded constructible complexes:
`Lf^*_{𝒪_E} ⋙ (E ⊗ᴸ_{𝒪_E} -) ≅ (E ⊗ᴸ_{𝒪_E} -) ⋙ Lf^*_E`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The map `c_k = ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲`, where `φ` is the inclusion. -/
noncomputable def padicIntegersRingObjToContinuousMapRingObjInvPow (k : ℕ) :
    padicIntegersRingObj.{u} ℓ E.1 ⟶ continuousMapRingObj E.1 :=
  padicIntegersRingObjToContinuousMapRingObj ℓ E ≫
    continuousMapRingObjMulLeft E.1 ((ℓ : E.1)⁻¹ ^ k)

lemma padicIntegersRingObjToContinuousMapRingObjInvPow_zero :
    padicIntegersRingObjToContinuousMapRingObjInvPow.{u} ℓ E 0 =
      padicIntegersRingObjToContinuousMapRingObj ℓ E := by
  rw [padicIntegersRingObjToContinuousMapRingObjInvPow, pow_zero,
    continuousMapRingObjMulLeft_one, Category.comp_id]

lemma nsmul_padicIntegersRingObjToContinuousMapRingObjInvPow_succ (k : ℕ) :
    ℓ • padicIntegersRingObjToContinuousMapRingObjInvPow.{u} ℓ E (k + 1) =
      padicIntegersRingObjToContinuousMapRingObjInvPow ℓ E k := by
  have hℓ : (ℓ : E.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  rw [padicIntegersRingObjToContinuousMapRingObjInvPow,
    padicIntegersRingObjToContinuousMapRingObjInvPow, ← Preadditive.comp_nsmul,
    nsmul_continuousMapRingObjMulLeft, pow_succ', ← _root_.mul_assoc, mul_inv_cancel₀ hℓ,
    _root_.one_mul]

/-- **`E̲ = colim(𝒪̲_E --ℓ--> 𝒪̲_E --ℓ--> ⋯)`**: the maps `ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲` exhibit the condensed
abelian group `E̲` as the sequential colimit of the multiplications by `ℓ` on `𝒪̲_E`. Sectionwise,
every continuous map from a profinite set to `E` is `ℓ⁻ᵐ` times a continuous map to `𝒪_E`
(`PadicAlgCl.exists_norm_pow_mul_le_one`), and the maps `ℓ⁻ᵏ φ` are injective. -/
noncomputable def isColimitPadicIntegersRingObjSmulSequenceCocone :
    IsColimit (Mod.smulSequenceCocone ℓ
      (padicIntegersRingObjToContinuousMapRingObjInvPow.{u} ℓ E)
      (nsmul_padicIntegersRingObjToContinuousMapRingObjInvPow_succ ℓ E)) := by
  have hℓ : (ℓ : E.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (sheafToPresheaf _ _) ?_
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨x⟩ := x
    obtain ⟨m, hm⟩ := PadicAlgCl.exists_norm_pow_mul_le_one
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(E.1, PadicAlgCl ℓ)).comp x)
    have hmem (s : S.unop) : (ℓ : E.1) ^ m * x s ∈ PadicAlgCl.integers ℓ E.1 := by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, map_mul, map_pow,
        map_natCast]
      exact hm s
    refine ⟨m, ULift.up ⟨fun s ↦ ⟨_, hmem s⟩, (continuous_const.mul x.continuous).subtype_mk _⟩,
      ULift.ext _ _ (ContinuousMap.ext fun s ↦ ?_)⟩
    have key : (ℓ : E.1)⁻¹ ^ m * ((ℓ : E.1) ^ m * x s) = x s := by
      rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hℓ, one_pow, _root_.one_mul]
    exact key.symm
  · intro k x y h
    refine ⟨k, 𝟙 k, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have hk : (ℓ : E.1)⁻¹ ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero hℓ)
    have h' (s : S.unop) :
        (ℓ : E.1)⁻¹ ^ k * (x s : E.1) = (ℓ : E.1)⁻¹ ^ k * (y s : E.1) :=
      congrArg (fun z : ULift.{u + 1} C(S.unop, E.1) ↦ z.down s) h
    obtain rfl : x = y := ContinuousMap.ext fun s ↦ Subtype.ext (mul_left_cancel₀ hk (h' s))
    rfl

end Profinite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- **Flatness of `E_X` over `𝒪_{E,X}`**: the extension of scalars along the inclusion
`𝒪_{E,X} ⟶ E_X` is exact. Indeed `E_X = p_X^* E̲` is the sequential colimit of the
multiplications by `ℓ` on `𝒪_{E,X} = p_X^* 𝒪̲_E`, `p_X^*` being an additive left adjoint, so
`E_X ⊗_{𝒪_{E,X}} M = colim(M --ℓ--> M --ℓ--> ⋯)`, and sequential colimits of abelian sheaves are
exact. -/
instance preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield (X : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
  exact Mod.preservesFiniteLimits_extendScalars_of_isColimit _
    (Mod.isColimitSmulSequenceCoconeMap (upperStarFromPoint X) _
      (Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone ℓ E))
    (by rw [Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow_zero])

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : Y ⟶ X)

/-- **(Pull)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E`:
`Lf^*_{𝒪_E} ⋙ (E ⊗ᴸ_{𝒪_E} -) ≅ (E ⊗ᴸ_{𝒪_E} -) ⋙ Lf^*_E`, the restriction of
`ProEtale.CondensedRing.derivedPullIso` (which applies since `E_X` is flat over `𝒪_{E,X}`) along
the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarExtendScalarsIso :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ f ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleExtendScalarsCompatibility Y.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedPullIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleExtendScalarsCompatibility X.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
