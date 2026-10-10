/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

/-!
# Isomorphisms in `D(X_proét)` are local

Let `g i : W i ⟶ X` be a pro-étale covering family. A pro-étale sheaf on `X` whose pullbacks
to all the `W i` vanish is zero (`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar`): its
sections over any weakly étale `V ⟶ X` restrict injectively to the base changes
`V ×_X W i`, over which they are sections of the pullbacks. Since the pullbacks are exact and
commute with the cohomology sheaves, a morphism of `D(X_proét)` is an isomorphism as soon as its
derived pullbacks to all the `W i` are
(`AlgebraicGeometry.ProEtale.isIso_of_isIso_leftDerivedUpperStar_map`).

## Main results

- `AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar`: a sheaf vanishing locally is zero.
- `AlgebraicGeometry.ProEtale.isIso_of_isIso_upperStar_map`: a morphism of sheaves which is
  locally an isomorphism is an isomorphism.
- `AlgebraicGeometry.ProEtale.isIso_of_isIso_leftDerivedUpperStar_map`: the derived pullbacks
  along a pro-étale covering family jointly reflect isomorphisms.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}} {g : ∀ i, W i ⟶ X}

/-- The base change `V ×_X W` of a weakly étale `X`-scheme `V` along a weakly étale
`g : W ⟶ X` is the image of a weakly étale `W`-scheme under the localization functor. -/
noncomputable def baseChangeIsoOverMap {W : Scheme.{u}} (g : W ⟶ X) [hg : WeaklyEtale g]
    (V : X.ProEt) :
    (MorphismProperty.Over.map ⊤ hg).obj
        (ProEt.mk (pullback.snd V.hom g)) ≅ ProEt.baseChange g V :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    simp [ProEt.baseChange, ProEt.mk, pullback.condition])

/-- **A pro-étale sheaf vanishing locally is zero.** If the pullbacks of `E` along the members
of a pro-étale covering family vanish, then `E` vanishes. -/
lemma isZero_of_isZero_upperStar (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (E : Sheaf (Scheme.ProEt.topology X) A) (hE : ∀ i, IsZero ((g i)^*[A].obj E)) :
    IsZero E := by
  have hw (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hg (.mk i)
  -- the sections of `E` over the base changes `V ×_X W i` vanish
  have hZ (i : ι) (V : X.ProEt) : IsZero (E.obj.obj (op (ProEt.baseChange (g i) V))) := by
    have h₁ : IsZero ((localizationRestriction A (g i) (hw i)).obj E) :=
      (hE i).of_iso ((upperStarIsoLocalizationRestriction A (g i) (hw i)).app E).symm
    have h₂ : IsZero (((localizationRestriction A (g i) (hw i)).obj E).obj.obj
        (op (ProEt.mk (pullback.snd V.hom (g i))))) :=
      ((sheafToPresheaf _ A).map_isZero h₁).obj _
    exact h₂.of_iso (E.obj.mapIso (baseChangeIsoOverMap (g i) V).op)
  rw [IsZero.iff_id_eq_zero]
  apply (sheafToPresheaf _ A).map_injective
  ext V
  have := ProEt.ofArrows_baseChange_mem_topology V.unop g hg
  exact E.property.hom_ext_ofArrows _ this fun i ↦ (hZ i V.unop).eq_of_tgt _ _

/-- **Isomorphisms of pro-étale sheaves are local.** A morphism of sheaves whose pullbacks along
the members of a pro-étale covering family are isomorphisms is an isomorphism. -/
lemma isIso_of_isIso_upperStar_map (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {E F : Sheaf (Scheme.ProEt.topology X) A} (φ : E ⟶ F)
    (hφ : ∀ i, IsIso ((g i)^*[A].map φ)) : IsIso φ := by
  have : Mono φ := Preadditive.mono_of_isZero_kernel _ <|
    isZero_of_isZero_upperStar hg _ fun i ↦
      (isZero_kernel_of_mono ((g i)^*[A].map φ)).of_iso
        (PreservesKernel.iso (g i)^*[A] φ)
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _ <|
    isZero_of_isZero_upperStar hg _ fun i ↦
      (isZero_cokernel_of_epi ((g i)^*[A].map φ)).of_iso
        (PreservesCokernel.iso (g i)^*[A] φ)
  exact isIso_of_mono_of_epi φ

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **Isomorphisms in `D(X_proét)` are local.** The derived pullbacks along the members of a
pro-étale covering family jointly reflect isomorphisms: a morphism `f : K ⟶ L` of `D(X_proét)` is
an isomorphism as soon as every `Lg_i^* f` is. Isomorphisms are detected on cohomology sheaves,
which commute with the exact pullbacks. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (f : K ⟶ L)
    (hf : ∀ i, IsIso (L((g i)^*[A]).map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_upperStar_map hg _ fun i ↦ ?_
  have : IsIso ((L((g i)^*[A]) ⋙ DerivedCategory.homologyFunctor _ n).map f) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map (L((g i)^*[A]).map f)))
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso A (g i) n) f).2 this

end ProEtale

end AlgebraicGeometry
