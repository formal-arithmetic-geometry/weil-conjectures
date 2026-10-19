module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Density of the localized source in the relative normalization.

Source: Stacks Project, Tags 035I and 081I (flat base change of schematic images).
(blueprint: lem-sbc-stalk-normalization-dense-part)

Proof: Put M = f.normalization and N = M ×_C L. The map P → M has zero
kernel by the integral-closure construction. The stalk morphism Spec O_{S,s} → S
is flat, since on an affine neighbourhood it is a localization. Consequently
L → C and N → M are flat. Pulling P → M back along N → M gives a
quasi-compact schematically dominant map k : P ×_M N → N, so its image is dense.
The pullback identities and P → M → C = f show that every point in that image
maps into C_U under N → L → C. The displayed open therefore contains a dense
subset and is dense itself. This also covers an empty source or empty U. -/
theorem stalk_normalization_dense_part {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (_hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    Dense (↑(n ⁻¹ᵁ (l ⁻¹ᵁ (c ⁻¹ᵁ U))) :
      Set (pullback f.fromNormalization l : Scheme.{u})) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let l := pullback.fst c (S.fromSpecStalk s)
  let a := pullback.fst f.fromNormalization l
  let n := pullback.snd f.fromNormalization l
  let k := pullback.snd f.toNormalization a
  have : IsSchemeTheoreticallyDominant f.toNormalization := ⟨f.ker_toNormalization⟩
  have : Flat l := inferInstance
  have : Flat a := inferInstance
  have : IsSchemeTheoreticallyDominant k := inferInstance
  have : QuasiCompact k := inferInstance
  apply k.denseRange.mono
  rintro _ ⟨x, rfl⟩
  change l (n (k x)) ∈ c ⁻¹ᵁ U
  have h : k ≫ n ≫ l = pullback.fst f.toNormalization a ≫ f := by
    change pullback.snd f.toNormalization a ≫
      pullback.snd f.fromNormalization l ≫ l = _
    rw [← pullback.condition, ← Category.assoc, ← pullback.condition,
      Category.assoc, f.toNormalization_fromNormalization]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
  exact (PA.obj.hom (pullback.fst f.toNormalization a x)).property

end AlgebraicGeometry.Scheme
