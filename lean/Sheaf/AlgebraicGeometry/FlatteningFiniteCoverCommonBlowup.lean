module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.StrictTransformComposition
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.BaseChange
import WeilConjectures.Blowup.BlowupUniversal
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# A common flattening blowup for a finite affine cover

Source: Stacks Project, flat.tex, Tag 081R, first proof paragraph;
divisors.tex, Tags 080A, 080I (2), 080F (1), and flat.tex, Tag 080Y
(blueprint: lem-trf-flattening-finite-cover-common-blowup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace AlgebraicGeometry

/-- The product of the centers attached to a finite affine cover, including the empty product.
Source: Stacks Project, flat.tex, Tag 081R, and divisors.tex, Tag 080A
(blueprint: lem-trf-flattening-finite-cover-common-blowup). -/
def finiteCoverCenter {T : Scheme.{u}} {r : ℕ} (I : Fin r → T.IdealSheafData) :
    T.IdealSheafData :=
  ∏ i, I i

/-- The product of all centers other than the specified one; an empty product is the unit ideal.
Source: Stacks Project, divisors.tex, Tag 080A
(blueprint: lem-trf-flattening-finite-cover-common-blowup). -/
def finiteCoverRemainingCenter {T : Scheme.{u}} {r : ℕ}
    (I : Fin r → T.IdealSheafData) (i : Fin r) : T.IdealSheafData :=
  ∏ k ∈ Finset.univ.erase i, I k

/-- A product of flattening centers works simultaneously on a finite affine cover.
Source: Stacks Project, flat.tex, Tag 081R, proof paragraph 1, expanded by divisors.tex,
Tags 080A, 080I (2), and 080F (1), and flat.tex, Tag 080Y
(blueprint: lem-trf-flattening-finite-cover-common-blowup).

Proof:
1. Products of finite generating lists show that the total and remaining centers are finite
   type. Their restrictions to U are unit ideals. The inclusion of U is quasi-compact by
   lem-weil-pbc-qcqs-morphism-permanence (1). Thus the total center is admissible. Apply
   thm-nagata-blowup-product-ideal and def-nagata-blowup-product-comparison to each factor
   and its remaining product. This produces the further blowup and its factorization.
   If r = 0, W is empty and the unit-ideal blowup is the identity.
2. The zero set of a product is the union of the zero sets. Extension pulls back the zero
   set. Outside the first center thm-nagata-global-blowup-complement gives an isomorphism,
   proving the displayed support identity without surjectivity on the center.
3. Apply lem-trf-strict-transform-composition using that identity and factorization.
   By thm-nagata-strict-transform-is-blowup the second transform is a blowup. The flat
   comparison thm-nagata-blowup-flat-base-change identifies it with the ordinary pullback.
   The comparisons in def-nagata-blowup-flat-base-change-map and
   def-nagata-strict-transform-blowup-comparison have the same projections: uniqueness in
   thm-nagata-blowup-universal-property identifies them. Base change preserves flatness
   and local finite presentation by lem-weil-pbc-flat-morphism-base-change and
   lem-weil-pbc-qcqs-morphism-permanence (3).
4. The strict transform is the scheme-theoretic image of the open part over the complement
   of the total center. That open immersion is quasi-compact, since the ideal is finite
   type, and quasi-separated. Apply lemma-nagata-scheme-image-restrict-open to the opens
   W_i times T^b. Their restrictions are exactly the individual strict transforms; this
   gives the specified open immersions, their projection identities and the covering.
5. Flatness and local finite presentation are local on this covering, so hold globally
   by def-weil-flat-morphism and def-sbc-locally-finite-presentation.
6. The source W is qcqs by lem-weil-pbc-qcqs-morphism-permanence (2). The global transform
   is a blowup of W by thm-nagata-strict-transform-is-blowup, hence proper by
   lemma-nagata-blowup-proper, quasi-compact by def-weil-proper-morphism and
   def-weil-finite-type-morphism, and quasi-separated by lem-pc-separated-quasi-separated.
   Thus it and T^b are qcqs by permanence (2), and their structural morphism is qcqs by
   permanence (1). Together with local finite presentation this is finite presentation.
   No step requires U to be dense. -/
theorem flattening_finiteCover_commonBlowup
    {T W : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (U : T.Opens) (hU : IsCompact (U : Set T)) (g : W ⟶ T)
    [QuasiCompact g] [QuasiSeparated g]
    (r : ℕ) (V : Fin r → W.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : (⨆ i, V i) = ⊤)
    (I : Fin r → T.IdealSheafData) (hI : ∀ i, (I i).ofFiniteType)
    (hIU : ∀ i, (I i).comap U.ι = ⊤)
    (hflat : ∀ i, Flat (strictTransformMap ((V i).ι ≫ g)
      (I i).blowupMap (I i).support.compl))
    (hlfp : ∀ i, LocallyOfFinitePresentation (strictTransformMap ((V i).ι ≫ g)
      (I i).blowupMap (I i).support.compl)) :
    (∃ B : IsAdmissible T U, B.I = finiteCoverCenter I) ∧
    (∀ i, ∃ q : (finiteCoverCenter I).blowup ⟶ (I i).blowup,
      (∃ e : (finiteCoverCenter I).blowup ≅
          ((finiteCoverRemainingCenter I i).comap (I i).blowupMap).blowup,
        e.hom ≫ ((finiteCoverRemainingCenter I i).comap (I i).blowupMap).blowupMap = q) ∧
      q ≫ (I i).blowupMap = (finiteCoverCenter I).blowupMap ∧
      ((finiteCoverCenter I).support : Set T) = ((I i).support : Set T) ∪
        (I i).blowupMap ''
          (((finiteCoverRemainingCenter I i).comap (I i).blowupMap).support :
            Set (I i).blowup) ∧
      ∃ φ : (finiteCoverCenter I).strictTransform ((V i).ι ≫ g) ≅
          pullback (strictTransformMap ((V i).ι ≫ g) (I i).blowupMap (I i).support.compl) q,
        φ.hom ≫ pullback.fst _ q ≫
            strictTransformToSource ((V i).ι ≫ g) (I i).blowupMap (I i).support.compl =
          strictTransformToSource ((V i).ι ≫ g) (finiteCoverCenter I).blowupMap
            (finiteCoverCenter I).support.compl ∧
        φ.hom ≫ pullback.snd _ q =
          strictTransformMap ((V i).ι ≫ g) (finiteCoverCenter I).blowupMap
            (finiteCoverCenter I).support.compl) ∧
    (∃ j : ∀ i, (finiteCoverCenter I).strictTransform ((V i).ι ≫ g) ⟶
          (finiteCoverCenter I).strictTransform g,
      (∀ i, IsOpenImmersion (j i) ∧
        j i ≫ strictTransformToSource g (finiteCoverCenter I).blowupMap
            (finiteCoverCenter I).support.compl =
          strictTransformToSource ((V i).ι ≫ g) (finiteCoverCenter I).blowupMap
            (finiteCoverCenter I).support.compl ≫ (V i).ι ∧
        j i ≫ strictTransformMap g (finiteCoverCenter I).blowupMap
            (finiteCoverCenter I).support.compl =
          strictTransformMap ((V i).ι ≫ g) (finiteCoverCenter I).blowupMap
            (finiteCoverCenter I).support.compl) ∧
      ∀ x, ∃ (i : Fin r) (y : (finiteCoverCenter I).strictTransform ((V i).ι ≫ g)),
        j i y = x) ∧
    Flat (strictTransformMap g (finiteCoverCenter I).blowupMap
      (finiteCoverCenter I).support.compl) ∧
    LocallyOfFinitePresentation (strictTransformMap g (finiteCoverCenter I).blowupMap
      (finiteCoverCenter I).support.compl) ∧
    QuasiCompact (strictTransformMap g (finiteCoverCenter I).blowupMap
      (finiteCoverCenter I).support.compl) ∧
    QuasiSeparated (strictTransformMap g (finiteCoverCenter I).blowupMap
      (finiteCoverCenter I).support.compl) := by
  sorry

end AlgebraicGeometry
