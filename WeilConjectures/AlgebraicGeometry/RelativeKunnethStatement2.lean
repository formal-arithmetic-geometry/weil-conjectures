/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.AlgebraicGeometry.ProperRelativeKunnethSupports
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
import WeilConjectures.AlgebraicGeometry.ProperShriekCompCompForgetSupports
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.AlgebraicGeometry.ProperKunnethNormalizationAlgebra
import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Compactification.NagataCompactification

/-!
# Relative Künneth theorem

Source: current blueprint, `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/thm-sf-kunneth-relative.md` (blueprint: thm-sf-kunneth-relative).

This is the statement node `thm-sf-kunneth-relative` from the current blueprint.  The
canonical comparison is the published six-factor composite
`AlgebraicGeometry.Etale.relativeKunnethIso`; its naturality is exposed by the published
bifunctor isomorphism `relativeKunnethNatIso`.  The remaining clauses record the canonical
base-change and proper `Rf_!`/`Rf_*` comparisons and the compact-support product after
restriction to closed subschemes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale


/--
Relative compact-support Künneth, with the canonical map and the compatibility clauses of
`thm-sf-kunneth-relative`.

The first conjunct is invertibility of the displayed canonical map. The second is its
naturality equation in both variables. The third is the commuting base-change square;
the fourth is its compatibility with the proper identifications `Rf_! ≅ Rf_*`. The final
conjunct is the `B = Spec k` compact-support product for closed
restrictions, with `RΓ_c(V,-)` rendered as the lower-shriek direct image along the structure
map of `V`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/sk-thm-sf-kunneth-relative/
thm-sf-kunneth-relative.md`, statement and proof Steps 1--5 (blueprint: thm-sf-kunneth-relative).

Proof steps recorded by this statement are: Step 1 uses the composition isomorphism for
`f ×_B g = q ≫ g`; Step 2 uses the inverse projection transformation for `q`; Step 3
uses the inverse compact-support exchange for the Cartesian square; Step 4 uses tensor
symmetry and the inverse projection transformation for `g`, proving the displayed map is
an isomorphism and natural.  Step 5 specializes the same construction to the structure
maps of closed subschemes and identifies the exterior product after restriction.
For base change, paste the projection-formula base-change squares for `q` and `g`, the
exchange pasting squares, and the symmetric monoidal pullback comparisons. Cancel the
intermediate inverse comparisons to obtain the equality in the third conjunct. For proper
normalization, the compositor, exchange and projection factors commute with the canonical
forward forget-supports maps. Substitution in the inverse six-factor word gives the ordinary
Künneth factorization; precomposition by the forward word cancels its inverse and gives the
fourth conjunct. For each proper factor its forget-supports map is the proper identification.
The support-cohomology functor is distinct and is not asserted to have a relative
product formula here.
-/
theorem relativeKunnethStatement
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k]
    {B X Y : Scheme.{u}} (aB : B ⟶ Spec (.of k))
    [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    [HasCompactification aB]
    (f : X ⟶ B) (g : Y ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ aB)] [HasCompactification (g ≫ aB)]
    (Sf : SixFunctorDatum Λ k f aB) (Sg : SixFunctorDatum Λ k g aB)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    letI : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian aB
    letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace aB
    letI : HasCompactification (pullback.toBase f g) := by
      have : IsSeparated (pullback.snd f g) :=
        MorphismProperty.of_isPullback (P := @IsSeparated)
          (IsPullback.of_hasPullback f g) inferInstance
      have : LocallyOfFiniteType (pullback.snd f g) :=
        MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
          (IsPullback.of_hasPullback f g) inferInstance
      have : QuasiCompact (pullback.snd f g) :=
        MorphismProperty.of_isPullback (P := @QuasiCompact)
          (IsPullback.of_hasPullback f g) inferInstance
      rw [← pullback.snd_comp_eq_toBase]
      infer_instance
    IsIso (relativeKunnethIso Λ f g K L).hom ∧
      (∀ {K' : _root_.DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        {L' : _root_.DerivedCategory
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        (_hK' : DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} Λ) X K')
        (_hL' : DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} Λ) Y L')
        (a : K ⟶ K') (b : L ⟶ L'),
        (R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).map
            (((-⊗ᴸ-(pullback f g)[ModuleCat.{u + 1} Λ]).map
              ((L((pullback.fst f g)^*[ModuleCat.{u + 1} Λ])).map a)).app
              ((L((pullback.snd f g)^*[ModuleCat.{u + 1} Λ])).obj L) ≫
            ((-⊗ᴸ-(pullback f g)[ModuleCat.{u + 1} Λ]).obj
              ((L((pullback.fst f g)^*[ModuleCat.{u + 1} Λ])).obj K')).map
              ((L((pullback.snd f g)^*[ModuleCat.{u + 1} Λ])).map b)) ≫
          (relativeKunnethIso Λ f g K' L').hom =
        (relativeKunnethIso Λ f g K L).hom ≫
          ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).map
            ((R(f)_![ModuleCat.{u + 1} Λ]).map a)).app
            ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) ≫
          ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj
            ((R(f)_![ModuleCat.{u + 1} Λ]).obj K')).map
            ((R(g)_![ModuleCat.{u + 1} Λ]).map b)) ∧
      relativeKunnethBaseChangeCompatibility f g K L ∧
      relativeKunnethProperCompatibility f g K L ∧
      (∀ {X₀ Y₀ Z W : Scheme.{u}} (aX : X₀ ⟶ Spec (.of k))
        (aY : Y₀ ⟶ Spec (.of k)) (iZ : Z ⟶ X₀) (iW : W ⟶ Y₀)
        [IsClosedImmersion iZ] [IsClosedImmersion iW]
        [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
        [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
        (K₀ : _root_.DerivedCategory
          (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (L₀ : _root_.DerivedCategory
          (Sheaf Y₀.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (hK₀ : DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} Λ) X₀ K₀)
        (hL₀ : DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} Λ) Y₀ L₀),
        letI : HasCompactification (pullback.toBase (iZ ≫ aX) (iW ≫ aY)) := by
          have : IsSeparated (pullback.snd (iZ ≫ aX) (iW ≫ aY)) :=
            MorphismProperty.of_isPullback (P := @IsSeparated)
              (IsPullback.of_hasPullback (iZ ≫ aX) (iW ≫ aY)) inferInstance
          have : LocallyOfFiniteType (pullback.snd (iZ ≫ aX) (iW ≫ aY)) :=
            MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
              (IsPullback.of_hasPullback (iZ ≫ aX) (iW ≫ aY)) inferInstance
          have : QuasiCompact (pullback.snd (iZ ≫ aX) (iW ≫ aY)) :=
            MorphismProperty.of_isPullback (P := @QuasiCompact)
              (IsPullback.of_hasPullback (iZ ≫ aX) (iW ≫ aY)) inferInstance
          rw [← pullback.snd_comp_eq_toBase]
          infer_instance
        IsIso (relativeKunnethClosedRestrictionMap aX aY iZ iW K₀ L₀)) := by
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian aB
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace aB
  have : IsSeparated (pullback.snd f g) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (IsPullback.of_hasPullback f g) inferInstance
  have : LocallyOfFiniteType (pullback.snd f g) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback f g) inferInstance
  have := quasiCompact_pullback_snd f g
  let : HasCompactification (pullback.toBase f g) := by
    rw [← pullback.snd_comp_eq_toBase]
    infer_instance
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro K' L' hK' hL' a b
    have := quasiCompact_pullback_snd f g
    have := quasiCompact_pullback_toBase f g
    dsimp only [relativeKunnethIso]
    rw [Functor.map_comp, Category.assoc]
    erw [relativeKunnethIsoOfIsPullback_hom_naturality_right]
    erw [relativeKunnethIsoOfIsPullback_hom_naturality_left_assoc]
  · intro B' X' Y' b f' g' pX pY sqf sqg π hX hY sqt
    let : HasCompactification f' := HasCompactification.of_isPullback sqf
    let : HasCompactification g' := HasCompactification.of_isPullback sqg
    let : QuasiCompact f' :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqf inferInstance
    let : QuasiCompact g' :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqg inferInstance
    let : HasCompactification (pullback.toBase f' g') :=
      HasCompactification.of_isPullback sqt
    let : QuasiCompact (pullback.toBase f g) := quasiCompact_pullback_toBase f g
    let : QuasiCompact (pullback.toBase f' g') :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqt inferInstance
    have := quasiCompact_pullback_snd f g
    have := quasiCompact_pullback_snd f' g'
    have sqq : IsPullback π (pullback.snd f' g') (pullback.snd f g) pY := by
      have ht : IsPullback π (pullback.snd f' g' ≫ g') (pullback.snd f g ≫ g) b := by
        simpa only [pullback.snd_comp_eq_toBase] using sqt
      exact ht.of_bot hY sqg
    have he := relativeKunneth_baseChange_pasting Λ
      (pullback.snd_comp_eq_toBase f g) (pullback.snd_comp_eq_toBase f' g')
      (IsPullback.of_hasPullback f g) (IsPullback.of_hasPullback f' g')
      sqf sqg sqq ⟨hX⟩ sqt K L
    simpa only [relativeKunnethIso, leftDerivedUpperStarCompPathIso,
      derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      rightDerivedLowerShriekBaseChangeIso_hom, Functor.mapIso_hom,
      tensorIso_hom, MonoidalCategory.tensorHom_def, externalProduct, derivedTensor,
      curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc] using he
  · intro _
    have := quasiCompact_pullback_snd f g
    have := quasiCompact_pullback_toBase f g
    have he := relativeKunneth_inv_forgetSupports Λ (IsPullback.of_hasPullback f g)
      (pullback.toBase f g) (pullback.snd_comp_eq_toBase f g) K L
    have ht := congrArg (fun z ↦ (relativeKunnethIso Λ f g K L).hom ≫ z) he
    simpa only [relativeKunnethIso, externalProduct, rightDerivedLowerShriek,
      Category.assoc, Iso.hom_inv_id_assoc] using ht
  · intro X₀ Y₀ Z W aX aY iZ iW _ _ _ _ _ _ _ _ K₀ L₀ hK₀ hL₀
    unfold relativeKunnethClosedRestrictionMap
    infer_instance


end AlgebraicGeometry.Etale
