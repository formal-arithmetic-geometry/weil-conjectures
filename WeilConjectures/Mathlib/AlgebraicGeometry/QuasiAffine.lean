/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Quasi-affine morphisms and quasi-affineness from Zariski's Main Theorem

A morphism of schemes is quasi-affine if the preimage of every affine open of the target is a
quasi-affine scheme. This is the relative form of `AlgebraicGeometry.Scheme.IsQuasiAffine`, and
it sits beside `AlgebraicGeometry.IsAffineHom` exactly as the absolute notion sits beside
`AlgebraicGeometry.IsAffine`.

We also record the two consequences of Zariski's Main Theorem that the Nagata compactification
argument uses. Zariski's Main Theorem says that a separated, quasi-compact, locally quasi-finite
morphism of finite type `f : X ⟶ Y` factors as an open immersion into the relative normalization
of `Y` in `X` followed by an integral (in particular affine) morphism.

## Main results

* `AlgebraicGeometry.IsQuasiAffineHom`: the class of quasi-affine morphisms.
* `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isAffineHom_of_locallyQuasiFinite`:
  a separated, quasi-compact, locally quasi-finite morphism of finite type factors as an open
  immersion followed by an affine morphism.
* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_locallyQuasiFinite`:
  the source of such an `f` is quasi-affine as soon as the target is.
* `AlgebraicGeometry.IsQuasiAffineHom.of_locallyQuasiFinite`:
  such an `f` is quasi-affine as a morphism, with no hypothesis on `Y`.
* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isQuasiAffineHom`: over an affine base, the relative
  notion recovers the absolute one.

None of the three Zariski's Main Theorem statements is an instance: the hypothesis list is long
and `LocallyQuasiFinite` is not something typeclass inference should be asked to discharge.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Quasi-affineness only depends on the isomorphism class of a scheme. -/
lemma Scheme.IsQuasiAffine.of_isIso (e : X ⟶ Y) [IsIso e] [Y.IsQuasiAffine] : X.IsQuasiAffine :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace e
  .of_isImmersion e

/-- **Zariski's Main Theorem**, in factorization form: a separated, quasi-compact, locally
quasi-finite morphism of finite type factors as an open immersion followed by an affine
morphism. The factorization is through the relative normalization `f.normalization`. -/
theorem Scheme.Hom.exists_isOpenImmersion_isAffineHom_of_locallyQuasiFinite
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ (W : Scheme.{u}) (j : X ⟶ W) (g : W ⟶ Y), IsOpenImmersion j ∧ IsAffineHom g ∧ j ≫ g = f :=
  ⟨f.normalization, f.toNormalization, f.fromNormalization, inferInstance, inferInstance,
    f.toNormalization_fromNormalization⟩

/-- If `f : X ⟶ Y` is separated, quasi-compact and locally quasi-finite of finite type and `Y` is
quasi-affine, then `X` is quasi-affine. Indeed, by Zariski's Main Theorem `f` factors as an open
immersion `X ⟶ f.normalization` followed by an affine morphism onto `Y`, so `f.normalization` is
quasi-affine, and `X` is a quasi-compact locally closed subscheme of it. -/
theorem Scheme.IsQuasiAffine.of_locallyQuasiFinite [Y.IsQuasiAffine]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    X.IsQuasiAffine :=
  have : f.normalization.IsQuasiAffine := .of_isAffineHom f.fromNormalization
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  .of_isImmersion f.toNormalization

/-- A morphism of schemes is quasi-affine if the preimage of every affine open of the target is a
quasi-affine scheme. -/
@[mk_iff]
class IsQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isQuasiAffine_preimage (U : Y.Opens) (hU : IsAffineOpen U) : (f ⁻¹ᵁ U).toScheme.IsQuasiAffine

lemma IsAffineOpen.isQuasiAffine_preimage {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsQuasiAffineHom f] : (f ⁻¹ᵁ U).toScheme.IsQuasiAffine :=
  IsQuasiAffineHom.isQuasiAffine_preimage _ hU

instance (priority := 900) [IsAffineHom f] : IsQuasiAffineHom f where
  isQuasiAffine_preimage U hU :=
    have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
    inferInstance

/-- A quasi-compact morphism out of a quasi-affine scheme is quasi-affine: the preimage of an
affine open is a quasi-compact open subscheme of a quasi-affine scheme. -/
instance (priority := 900) [X.IsQuasiAffine] [QuasiCompact f] : IsQuasiAffineHom f where
  isQuasiAffine_preimage U hU :=
    have : CompactSpace (f ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
    .of_isImmersion (f ⁻¹ᵁ U).ι

/-- If `f : X ⟶ Y` is separated, quasi-compact and locally quasi-finite of finite type, then it is
quasi-affine as a morphism. This is Zariski's Main Theorem applied over each affine open of `Y`;
note that no hypothesis on `Y` is needed. -/
theorem IsQuasiAffineHom.of_locallyQuasiFinite
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsQuasiAffineHom f where
  isQuasiAffine_preimage U hU :=
    have : IsAffine U.toScheme := hU
    .of_locallyQuasiFinite (f ∣_ U)

/-- Precomposing a quasi-affine morphism with an immersion again gives a quasi-affine morphism,
provided the composite is quasi-compact. -/
instance {Z : Scheme.{u}} (g : Z ⟶ X) [IsImmersion g] [IsQuasiAffineHom f]
    [QuasiCompact (g ≫ f)] : IsQuasiAffineHom (g ≫ f) where
  isQuasiAffine_preimage U hU := by
    have hcpt : CompactSpace ((g ≫ f) ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.mp ((g ≫ f).isCompact_preimage hU.isCompact)
    have he : (g ≫ f) ⁻¹ᵁ U = g ⁻¹ᵁ (f ⁻¹ᵁ U) := by
      rw [Scheme.Hom.comp_base, Opens.map_comp_obj]
    rw [he] at hcpt ⊢
    have := hU.isQuasiAffine_preimage f
    exact .of_isImmersion (g ∣_ (f ⁻¹ᵁ U))

/-- Quasi-affine morphisms are stable under restricting the base to an open subscheme. -/
instance (V : Y.Opens) [IsQuasiAffineHom f] : IsQuasiAffineHom (f ∣_ V) where
  isQuasiAffine_preimage W hW :=
    have : (f ⁻¹ᵁ (V.ι ''ᵁ W)).toScheme.IsQuasiAffine :=
      (hW.image_of_isOpenImmersion V.ι).isQuasiAffine_preimage f
    .of_isIso ((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ W) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage f V W)).hom

/-- Over an affine base, a quasi-affine morphism has quasi-affine source: the relative notion
recovers the absolute one. -/
lemma Scheme.IsQuasiAffine.of_isQuasiAffineHom [IsQuasiAffineHom f] [IsAffine Y] :
    X.IsQuasiAffine :=
  have : (⊤ : X.Opens).toScheme.IsQuasiAffine := (isAffineOpen_top Y).isQuasiAffine_preimage f
  .of_isIso X.topIso.inv

end AlgebraicGeometry
