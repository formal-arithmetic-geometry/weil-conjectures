/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Exactness of the étale inverse image

For an arbitrary morphism of schemes `g : Z ⟶ Y` the inverse image
`g^* = (g)^*[A] : Sh(Y_ét, A) ⥤ Sh(Z_ét, A)` with values in a Grothendieck abelian category `A`
(for instance abelian groups, or modules over a ring) is exact. It is the composite of the
inclusion of sheaves into presheaves, the left Kan extension along the opposite of the base
change functor `b_g : Y_ét ⥤ Z_ét`, and sheafification, and each of these is left exact:

- `b_g` preserves finite limits (`AlgebraicGeometry.Etale.preservesFiniteLimits_overPullback`);
- hence the presheaf inverse image, the left Kan extension along `b_gᵒᵖ`, is left exact, being
  computed by filtered colimits, which are exact in `A`
  (`AlgebraicGeometry.Etale.preservesFiniteLimits_lan_overPullback`);
- sheafification is exact and limits of sheaves are computed on the underlying presheaves
  (`AlgebraicGeometry.Etale.preservesFiniteLimits_presheafToSheaf`).

Right exactness of `g^*` holds because it is a left adjoint.

## Main statements

- `AlgebraicGeometry.Etale.preservesFiniteLimits_and_preservesFiniteColimits_upperStar`:
  `g^*` is exact.
- `AlgebraicGeometry.Etale.preservesColimitsOfSize_upperStar`: `g^*` preserves all colimits.
- `AlgebraicGeometry.Etale.shortExact_map_upperStar`: `g^*` sends short exact sequences to
  short exact sequences.
-/

@[expose] public section

universe v w u u'

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- **Base change between small étale sites commutes with finite limits.** The small étale
sites `Y_ét` and `Z_ét` have finite limits, and the base change functor
`W ↦ Z ×_Y W : Y_ét ⥤ Z_ét` along any morphism `g : Z ⟶ Y` preserves them.
This is blueprint `lem-weil-pbc-etale-base-change-finite-limits`. -/
@[stacks 021D]
theorem Etale.preservesFiniteLimits_overPullback :
    HasFiniteLimits Y.Etale ∧ HasFiniteLimits Z.Etale ∧
      PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ g) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **The presheaf inverse image is left exact.** The presheaf inverse image along the base
change functor `b_g : Y_ét ⥤ Z_ét`, i.e. the left Kan extension along `b_gᵒᵖ`, is left
adjoint to restriction `G ↦ G ∘ b_gᵒᵖ`, and it preserves finite limits: since `b_g` preserves
finite limits, its values are filtered colimits, which are exact in the Grothendieck abelian
category `A`.
This is blueprint `lem-weil-pbc-presheaf-pullback-left-exact`. -/
@[stacks 00VC]
theorem Etale.preservesFiniteLimits_lan_overPullback :
    Nonempty ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan ⊣
        ((Functor.whiskeringLeft _ _ A).obj (MorphismProperty.Over.pullback @Etale ⊤ g).op)) ∧
      PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
        (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  ⟨⟨(MorphismProperty.Over.pullback @Etale ⊤ g).op.lanAdjunction A⟩, inferInstance⟩

/-- **Sheafification is exact, and limits of sheaves are computed sectionwise.** On the small
étale site of `Y`, the inclusion of `A`-valued sheaves into presheaves preserves all limits,
and sheafification preserves finite limits and all colimits.
This is blueprint `lem-weil-pbc-sheafification-exact`. -/
@[stacks 00WJ]
theorem Etale.preservesFiniteLimits_presheafToSheaf :
    PreservesLimits (sheafToPresheaf Y.smallEtaleTopology A) ∧
      PreservesFiniteLimits (presheafToSheaf Y.smallEtaleTopology A) ∧
        PreservesColimits (presheafToSheaf Y.smallEtaleTopology A) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Exactness of inverse image**: for an arbitrary morphism of schemes `g : Z ⟶ Y`, the
inverse image `g^* : Sh(Y_ét, A) ⥤ Sh(Z_ét, A)` preserves finite limits and finite colimits,
i.e. it is exact. Left exactness is `AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar`
(inclusion into presheaves, left exact presheaf inverse image, exact sheafification), and
right exactness holds because `g^*` is left adjoint to `g_*`. For `A` the category of abelian
groups this is the exactness of `u⁻¹ : Ab(Y_ét) ⥤ Ab(Z_ét)`.
This is blueprint `prop-weil-pbc-inverse-image-exact`. -/
@[stacks 03Q1]
theorem Etale.preservesFiniteLimits_and_preservesFiniteColimits_upperStar :
    PreservesFiniteLimits (g)^*[A] ∧ PreservesFiniteColimits (g)^*[A] :=
  ⟨inferInstance, inferInstance⟩

/-- The inverse image `g^*` on étale sheaves sends short exact sequences to short exact
sequences (`AlgebraicGeometry.Etale.preservesFiniteLimits_and_preservesFiniteColimits_upperStar`).
-/
theorem Etale.shortExact_map_upperStar {S : ShortComplex (Sheaf Y.smallEtaleTopology A)}
    (hS : S.ShortExact) : (S.map (g)^*[A]).ShortExact :=
  hS.map_of_exact (g)^*[A]

/-- **Inverse image commutes with colimits**: for an arbitrary morphism of schemes `g : Z ⟶ Y`,
the inverse image `g^* : Sh(Y_ét, A) ⥤ Sh(Z_ét, A)` preserves all colimits, being left adjoint
to the direct image `g_*` (`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`). For `A` the
category of abelian groups, this says that `colim_i g⁻¹ F_i ⟶ g⁻¹ (colim_i F_i)` is an
isomorphism for every small diagram `F` of abelian sheaves on `Y_ét`.
This is blueprint `lem-weil-pbc-inverse-image-preserves-colimits`. -/
@[stacks 0038]
theorem Etale.preservesColimitsOfSize_upperStar : PreservesColimitsOfSize.{v, w} (g)^*[A] :=
  (Etale.upperStarLowerStarAdjunction A g).leftAdjoint_preservesColimits

end AlgebraicGeometry
