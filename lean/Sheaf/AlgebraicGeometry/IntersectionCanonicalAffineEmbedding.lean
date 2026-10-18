/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.AlgebraicGeometry.RingedSubspace
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.Topology.SpectralLimitPullbackSections
import Sheaf.Topology.SetsInverseImageComposition
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.Sheaves.Stalks
import Sheaf.AlgebraicGeometry.QuasiAffineOpenAffinizationSquare
import Sheaf.Topology.FilteredSpectrumTopologicalLimit

/-!
# Canonical affine embedding of an intersection of quasi-compact opens

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`, including its final assertion.
(blueprint: lem-a1-intersection-canonical-affine-embedding)
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open LocallyRingedSpace

/-- The canonical map of a nonempty intersection of quasi-compact opens of an
ind-quasi-affine scheme identifies it, with its inverse-image structure sheaf, with an
intersection of quasi-compact opens of the spectrum of its sections. Its restriction to
any ambient open inside the intersection is an open immersion, and the construction is
natural under scheme isomorphisms preserving the subsets.

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`.
(blueprint: lem-a1-intersection-canonical-affine-embedding)

Proof:
1. Finite intersections of quasi-compact opens are quasi-compact: their union is quasi-affine,
   and its canonical affine embedding reduces this to the affine quasi-separated case
   (lem-trf-quasi-affine-canonical-affine-embedding, lem-weil-pbc-affine-scheme-qcqs).
   Close the family under finite intersections below one chosen member. The resulting
   directed spectral system has topological limit E (lem-weil-pbc-qcqs-scheme-spectral).
2. Spectral-limit descent of sections (lem-weil-pbc-spectral-limit-pullback-sections),
   inverse-image composition (lem-weil-pbc-sets-inverse-image-composition), and the
   underlying-set ring-sheafification comparison identify C with the filtered colimit
   of the stage section rings. Representatives and equality are computed at a common
   stage by lem-pc-filtered-colimit-commrings-elementwise.
3. Inverse image preserves stalks (lem-weil-pbc-topological-inverse-image-stalk), so the
   subspace is locally ringed. The affine adjunction
   (lem-a1-locally-ringed-space-affine-adjunction) gives the unique normalized map j and
   its restriction formula on every ambient open L contained in E.
4. Each stage embeds as a quasi-compact open of its affinization. The filtered spectrum
   limit (lem-a1-filtered-spectrum-topological-limit) identifies j topologically with
   the intersection of the inverse images of these opens; these are quasi-compact opens.
5. The stalk map C_q to O_Y,e is onto already from a fixed stage. For injectivity,
   represent a/b at a common stage; a zero germ is killed by an element outside the
   stage prime (def-weil-pbc-localization-at-prime), which remains outside q. Thus all
   stalk maps are isomorphisms (lem-weil-pbc-spec-domain-stalks-function-field).
6. The homeomorphism and stalk isomorphisms identify the structure sheaves by
   lem-weil-pbc-sets-sheaf-iso-on-stalks, hence give an isomorphism of locally ringed spaces.
7. For W open in Y and contained in E, the stage affinization squares are cartesian
   (lem-a1-quasi-affine-open-affinization-square). Passing to the filtered spectrum limit
   shows j(W) is the inverse image of its open image at a fixed stage. The sheaf
   identification makes the restriction an open immersion; W need not be quasi-compact.
8. A scheme isomorphism carrying E onto E' restricts, by inverse-image functoriality,
   to the indicated isomorphism of ringed subspaces. The two affine composites correspond
   to the same section-ring homomorphism, so the affine adjunction identifies them. -/
theorem intersection_canonical_affine_embedding
    (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → Scheme.IsQuasiAffine U.toScheme)
    (I : Type v) [Nonempty I] (U : I → Y.Opens)
    (hU : ∀ i : I, IsCompact (U i : Set Y))
    (E : Set Y) (hE : E = ⋂ i : I, (U i : Set Y)) :
    ∃ hlocal : ∀ x : E,
      IsLocalRing ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.stalk x),
    ∃ j : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ⟶
      (Spec ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace,
      (toSpecΓ ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)) ≫
        j.c.app (op ⊤) = 𝟙 _) ∧
      (∀ j' : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ⟶
        (Spec ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace,
        toSpecΓ ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)) ≫
          j'.c.app (op ⊤) = 𝟙 _ → j' = j) ∧
      (∃ (V : Set (Spec
          ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).Opens),
        V.Nonempty ∧ (∀ W ∈ V, IsCompact (W : Set (Spec
          ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))))) ∧
        ∃ hF : ∀ x : (⋂₀ (SetLike.coe '' V) : Set (Spec
            ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)))),
          IsLocalRing ((ringedSubspace
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V))).presheaf.stalk x),
        ∃ e : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ≅
          locallyRingedSubspace
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V)) hF,
          e.hom.toShHom ≫ ringedSubspaceι
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V)) = j.toShHom) ∧
      (∀ (W : Y.Opens) (hW : (W : Set Y) ⊆ E),
        ∃ l : W.toScheme.toLocallyRingedSpace ⟶
          locallyRingedSubspace Y.toLocallyRingedSpace E hlocal,
          (∀ x : W, l.base x = ⟨x.val, hW x.property⟩) ∧
          (l.toShHom ≫ ringedSubspaceι Y.toLocallyRingedSpace E = W.ι.toLRSHom.toShHom) ∧
          (l ≫ j = ΓSpec.locallyRingedSpaceAdjunction.homEquiv _ _
            (LocallyRingedSpace.Γ.map l.op).op) ∧
          IsOpenImmersion (Scheme.Hom.mk (l ≫ j))) ∧
      (∀ (Y' : Scheme.{u}) (E' : Set Y')
          (hlocal' : ∀ x : E',
            IsLocalRing ((ringedSubspace Y'.toLocallyRingedSpace E').presheaf.stalk x))
          (e : Y ≅ Y') (he : e.hom '' E = E'),
        ∃ a : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ≅
          locallyRingedSubspace Y'.toLocallyRingedSpace E' hlocal',
          (∀ x : E, (a.hom.base x).val = e.hom x.val) ∧
          (a.hom.toShHom ≫ ringedSubspaceι Y'.toLocallyRingedSpace E' =
            ringedSubspaceι Y.toLocallyRingedSpace E ≫ e.hom.toLRSHom.toShHom) ∧
          a.hom ≫ (locallyRingedSubspace Y'.toLocallyRingedSpace E' hlocal').toΓSpec =
            j ≫ Spec.locallyRingedSpaceMap (LocallyRingedSpace.Γ.map a.hom.op)) := by
  sorry

end AlgebraicGeometry
