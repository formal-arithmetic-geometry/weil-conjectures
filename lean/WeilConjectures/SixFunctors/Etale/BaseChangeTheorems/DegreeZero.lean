/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.BaseChange.GlobalSections

import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion

/-!
# Sections of étale sheaves on proper schemes over a henselian base

Let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` proper, with closed fibre
`i : Y₀ = Y ×_A A/I ⟶ Y`. For every étale sheaf `F` on `Y`, restriction
`Γ(Y, F) ⟶ Γ(Y₀, F|_{Y₀})` is an isomorphism. Over a strictly henselian local ring `A` the
closed fibre may be replaced by the closed geometric fibre `Z_s = Z ×_A κ̄`, where `κ̄` is an
algebraic closure of the residue field `κ`: as `κ` is separably closed, `κ̄/κ` is purely
inseparable and `Z_s ⟶ Z₀` is a universal homeomorphism.

These degree-zero comparisons compute the stalks of a direct image along a proper morphism,
and are the input of the underived proper base change
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`.

## Main definitions

- `AlgebraicGeometry.Etale.projectiveLineClosedFibreRestriction`: the restriction
  `Γ(ℙ¹_A, F) ⟶ Γ(ℙ¹_κ, F₀)` to the closed fibre of the projective line.

## Main statements

- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`: the comparison
  over a henselian pair.
- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre`: the comparison
  with the closed geometric fibre over a strictly henselian local ring.

## References

- Stacks Project, Lemma 59.91.2, <https://stacks.math.columbia.edu/tag/0A0C>
- Stacks Project, Lemma 59.82.2, <https://stacks.math.columbia.edu/tag/09ZF>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The strictly henselian setup for the projective line.** For a local ring `A` with
residue field `κ` — in the application `A` is strictly henselian — let `X = ℙ¹_A`, let
`X₀ = ℙ¹_κ` be its closed fibre, and for an étale sheaf `F` on `X` let `F₀` be its inverse
image on `X₀`. This is the restriction map `res_F : Γ(X, F) ⟶ Γ(X₀, F₀)`.
(blueprint: `def-weil-pbc-strict-henselian-setup`) -/
noncomputable def Etale.projectiveLineClosedFibreRestriction (A : Type u) [CommRing A]
    [IsLocalRing A]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj F ⟶
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F) :=
  globalSectionsUpperStarMap _ _ F

/-- **Étale henselian restriction in degree zero.** Let `(A, I)` be a henselian pair, let
`p : Y ⟶ Spec A` be proper, and let `i : Y₀ ⟶ Y` be the closed fibre over `Spec (A ⧸ I)`.
For every étale sheaf `F` of `Λ`-modules on `Y`, restriction `Γ(Y, F) ⟶ Γ(Y₀, F|_{Y₀})` is an
isomorphism.

The proof has two stages: the Zariski comparison on `Y` and on all its finite covers, from
the connectedness of the closed fibres
(`AlgebraicGeometry.Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter`) and the
spectral restriction criterion; and the passage to étale sheaves by finite-refinement descent
(`AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale`) along the
finite-pullback identities
(`AlgebraicGeometry.Etale.globalSectionsUpperStarMap_identities`). The affine case is
`AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_of_henselianRing`.
(blueprint: `lemma-weil-pbc-etale-degree-zero`) -/
@[stacks 0A0C]
theorem Etale.isIso_globalSectionsUpperStarMap_of_henselianRing {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y Y₀ : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    (i : Y₀ ⟶ Y) (p₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)
  have : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  have hrange : Set.range i = p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    have hi := Scheme.image_preimage_eq_of_isPullback h.flip (Set.univ : Set (Spec
      (.of (A ⧸ I))))
    have hquot : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
        PrimeSpectrum.zeroLocus (I : Set A) := by
      change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
      rw [range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective),
        Ideal.mk_ker]
    simpa only [Set.preimage_univ, Set.image_univ, hquot] using hi
  apply Etale.isIso_globalSectionsUpperStarMap_of_finite_connected_closed_intersections Λ i
  intro X' q hq C hC hC'
  rw [hrange, ← Set.preimage_comp]
  exact ((q ≫ p).spectralSpace_and_isClosed_and_isConnected_inter I).2.2 C hC hC'

/-- The pullback of global sections along a universal homeomorphism is an isomorphism: the
pullback is then an equivalence of categories of étale sheaves
(`AlgebraicGeometry.Etale.isEquivalence_upperStar`), so the unit of `f^* ⊣ f_*` is an
isomorphism. -/
instance Etale.isIso_globalSectionsUpperStarMap_of_isUniversalHomeomorphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsUniversalHomeomorphism f]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f G) := by
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) f
  unfold globalSectionsUpperStarMap
  infer_instance

/-- **Degree-zero comparison over a strictly henselian base.** Let `A` be a strictly henselian
local ring with residue field `κ`, let `s : Spec κ̄ ⟶ Spec A` be the closed geometric point
given by an algebraic closure `κ̄` of `κ`, and let `p : Z ⟶ Spec A` be proper. For every étale
sheaf `F` of `Λ`-modules on `Z`, restriction `Γ(Z, F) ⟶ Γ(Z_s, F|_{Z_s})` to the closed
geometric fibre `Z_s = Z ×_A κ̄` is an isomorphism.

As `κ` is separably closed, `κ̄/κ` is purely inseparable, so `Z_s ⟶ Z₀ = Z ×_A κ` is a universal
homeomorphism and induces an isomorphism on sections; the comparison for `Z₀` is
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`. The algebraic
closure matters: a geometric point with a transcendental field of constants gives larger
sections, e.g. for `𝔾_m` on a point.
(blueprint: `lemma-weil-pbc-proper-strict-henselian-h0`) -/
theorem Etale.isIso_globalSectionsUpperStarMap_geometricFibre (A : Type u) [CommRing A]
    [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of A)) [IsProper p] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (pullback.fst p
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))))) F) := by
  let κ := IsLocalRing.ResidueField A
  let s₀ : Spec (.of κ) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let t : Spec (.of (AlgebraicClosure κ)) ⟶ Spec (.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ)))
  have hs : Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure κ))) = t ≫ s₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq A κ,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hs]
  let i₀ := pullback.fst p s₀
  let v := (pullbackLeftPullbackSndIso p s₀ t).inv ≫ pullback.fst (pullback.snd p s₀) t
  have hv : v ≫ i₀ = pullback.fst p (t ≫ s₀) := by
    simp [v, i₀]
  have : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i₀ F) :=
    Etale.isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal A) p i₀
      (pullback.snd p s₀) (IsPullback.of_hasPullback p s₀) F
  have : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (v ≫ i₀) F ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) v i₀).hom.app F)) := by
    rw [globalSectionsUpperStarMap_comp]
    infer_instance
  have := IsIso.of_isIso_comp_right
    (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (v ≫ i₀) F)
    ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) v i₀ (v ≫ i₀) rfl).hom.app F))
  rw [← hv]
  exact this

end AlgebraicGeometry
