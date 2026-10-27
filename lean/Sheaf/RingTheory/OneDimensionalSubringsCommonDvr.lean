module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.RingTheory.KrullAkizukiNoetherian

/-!
# A common discrete valuation overring criterion

Source: Stacks Project, Varieties, Tag 09N0, in Situation 09MY; used in Tag 09NJ.
(blueprint: lem-trf-one-dimensional-subrings-common-dvr-criterion).
-/

@[expose] public section

universe u

namespace Subring

/-- Two subrings of a common fraction field, the first Noetherian of dimension one,
have a nonsurjective tensor multiplication map exactly when a DVR contains both.

Source: Stacks Project, Varieties, Tag 09N0, in Situation 09MY.

Proof:
1. Let C be the image of the tensor multiplication map. Tensor generation shows that
   its elements are the finite sums of products ab, so it is a unital subring containing
   A and B (def-weil-pbc-module-tensor-product, def-weil-field). If the map is not
   surjective, C is proper. It cannot be a field, since it contains A and hence would
   contain every fraction of A, which exhausts K.
2. Choose a nonzero nonunit c in C. Its principal ideal is proper, so
   lem-weil-pbc-proper-ideal-contained-in-maximal supplies a maximal ideal m containing
   c. In particular m is nonzero.
3. Realize C_m as the subring of K consisting of r/s with r in C and s outside m
   (def-weil-pbc-localization-at-prime); cross multiplication proves injectivity.
   The nonzero element c/1 belongs to its maximal ideal. Apply
   lemma-nagata-local-domain-valuation-dominates to obtain a valuation overring V
   dominating C_m. Then c/1 remains a nonzero nonunit, so V is not a field, and V
   contains both A and B.
4. Apply lem-sc-krull-akizuki-noetherian with R = A, D = V and the identity finite
   field extension K/K. Thus V is Noetherian. The valuation-ring criterion
   lem-trf-noetherian-valuation-ring-dvr makes V a DVR. Since V contains A, every
   element of K is a fraction of elements of V; its fraction field is K.
5. Conversely, if a DVR O contains A and B, every finite sum of products ab lies in
   O, so the image lies in O. A DVR is not a field (def-sc-discrete-valuation-ring),
   hence O is a proper subring of K, and the tensor multiplication map is not
   surjective.
(blueprint: lem-trf-one-dimensional-subrings-common-dvr-criterion). -/
theorem not_surjective_tensorProduct_iff_exists_common_dvr
    {K : Type u} [Field K] (A B : Subring K)
    [IsFractionRing A K] [IsFractionRing B K] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) :
    ¬ Function.Surjective
      (Algebra.TensorProduct.lift A.subtype.toIntAlgHom B.subtype.toIntAlgHom
        (fun _ _ => Commute.all _ _)) ↔
      ∃ O : Subring K, IsDiscreteValuationRing O ∧ IsFractionRing O K ∧ A ≤ O ∧ B ≤ O := by
  sorry

end Subring
