module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithfully flat local comparison through a common field

Source: Stacks Project, Varieties, Tag 0384, reverse implication; Fields, Tag 0H7K;
Algebra, Tags 00HQ, 00HT, and 00HR
(blueprint: lem-trf-common-field-local-faithful-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

namespace Algebra

/-- Two arbitrary extensions of a field admit a common extension with a prime above a
prescribed prime after scalar extension. The other contraction lies above the same prime
of the original algebra, and the canonical map of the corresponding local rings is
faithfully flat and local. Both maps before localization are faithfully flat as well.

Source: Stacks Project, Varieties, Tag 0384, reverse implication; Fields, Tag 0H7K;
Algebra, Tags 00HQ, 00HT, and 00HR
(blueprint: lem-trf-common-field-local-faithful-comparison).

Proof plan:
1. Apply lem-weil-common-extension-fields to E/k and L/k to obtain a field F and
   k-algebra embeddings iE and iL. Their restrictions to k agree.
2. For H = E or L, identify (R tensor[k] H) tensor[H] F with R tensor[k] F by
   (r tensor h) tensor f mapping to r tensor (iH(h) * f). Its inverse sends
   r tensor f to (r tensor 1) tensor f. Balancing and multiplicativity follow from
   lem-weil-pbc-algebra-tensor-pushout-universal-property; equality on pure tensors
   extends by def-weil-pbc-module-tensor-product. The identification carries the
   inclusion to TensorProduct.map (AlgHom.id k R) iH.
3. Apply lem-weil-pbc-field-extension-base-change-faithfully-flat over H to F/H and
   R tensor[k] H. Transport along step 2 to obtain faithful flatness of both maps
   to R tensor[k] F, using def-weil-pbc-faithfully-flat-ring-map.
4. By lem-weil-pbc-faithfully-flat-surjective-spectrum choose Q above q along the
   L-map, and contract Q along the E-map to P. Both composites from R send r to
   r tensor 1, so P and q have the same contraction to R.
5. By lem-weil-pbc-flat-local-ring-maps the E-map induces a flat local ring map at
   P and Q, with the fraction formula given by Localization.localRingHom_mk'.
   By def-weil-pbc-localization-at-prime a fraction belongs to the maximal ideal
   exactly when its numerator belongs to the original prime. The definition of P
   therefore gives the stated equality of inverse images of maximal ideals.
6. Apply lem-weil-pbc-flat-local-hom-faithfully-flat to this flat local map. Together
   with steps 1, 3, and 4 this proves every assertion, without any finiteness or
   Noetherian hypothesis. -/
theorem exists_common_field_local_faithful_comparison
    (k : Type u) (E : Type v) (L : Type w) (R : Type t)
    [Field k] [Field E] [Field L] [CommRing R]
    [Algebra k E] [Algebra k L] [Algebra k R] (q : PrimeSpectrum (R ⊗[k] L)) :
    ∃ (F : Type (max v w)) (_ : Field F) (_ : Algebra k F)
      (iE : E →ₐ[k] F) (iL : L →ₐ[k] F)
      (Q : PrimeSpectrum (R ⊗[k] F)) (P : PrimeSpectrum (R ⊗[k] E))
      (hP : P.asIdeal = Q.asIdeal.comap
        (Algebra.TensorProduct.map (AlgHom.id k R) iE).toRingHom),
      Q.asIdeal.comap (Algebra.TensorProduct.map (AlgHom.id k R) iL).toRingHom =
        q.asIdeal ∧
      P.asIdeal.comap (algebraMap R (R ⊗[k] E)) =
        q.asIdeal.comap (algebraMap R (R ⊗[k] L)) ∧
      RingHom.FaithfullyFlat
        (Algebra.TensorProduct.map (AlgHom.id k R) iL).toRingHom ∧
      RingHom.FaithfullyFlat
        (Algebra.TensorProduct.map (AlgHom.id k R) iE).toRingHom ∧
      RingHom.FaithfullyFlat (Localization.localRingHom P.asIdeal Q.asIdeal
        (Algebra.TensorProduct.map (AlgHom.id k R) iE).toRingHom hP) ∧
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)).comap
        (Localization.localRingHom P.asIdeal Q.asIdeal
          (Algebra.TensorProduct.map (AlgHom.id k R) iE).toRingHom hP) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) := by
  sorry

end Algebra
