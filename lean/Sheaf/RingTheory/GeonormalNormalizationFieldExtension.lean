module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Sheaf.RingTheory.FlatIntegralTotalFractions

/-!
# Geometrically normal normalization under field extension

Source: Stacks Project, varieties.tex, Tag 0C3N,
lemma-normalization-and-change-of-fields, affine comparison and normality paragraph
(blueprint: lem-sfb-geonormal-normalization-field-extension).

Tensor factors are reversed using the canonical symmetry, so the extension field
acts through Mathlib's standard left tensor algebra. `FractionRing` denotes the
total quotient ring, including for rings with zero divisors and the zero ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- A finite geometrically normal normalization commutes with field extension,
with its canonical fraction formula and tower and principal-localization compatibility.

Source: Stacks Project, varieties.tex, Tag 0C3N,
lemma-normalization-and-change-of-fields, affine comparison and normality paragraph
(blueprint: lem-sfb-geonormal-normalization-field-extension).

Proof:
1. Geometric reducedness gives reducedness before and after scalar extension.
   The map A -> E tensor A is flat by
   lem-weil-pbc-field-extension-base-change-faithfully-flat. The balanced tensor
   identification (E tensor A) tensor_A B = E tensor B follows from
   lem-weil-pbc-algebra-tensor-pushout-universal-property.
2. Apply lem-per-flat-integral-total-fractions to A, E tensor A and B.
   Geometric normality identifies its image with the integral closure. The pure
   tensor formula gives the E-algebra structure and specifies the canonical map.
3. For E -> F the tensor map E tensor A -> F tensor A is flat by the same
   field-extension lemma. Regular denominators stay regular by the flat
   total-fraction lemma. Both composites on e tensor b, with b = a/s, are the
   fraction phi(e) tensor a divided by 1 tensor s. Tensor generation proves
   tower compatibility, including identity maps and iterated towers.
4. A principal localization of a normal ring is normal: its local ring at a
   prime is the local ring of the original ring at the contracted prime.
   Construct the inverse fraction maps by
   lem-weil-pbc-ring-localization-universal-property and use
   def-weil-pbc-localization-at-prime and def-weil-pbc-normal-ring.
5. Principal localizations are flat by lem-weil-pbc-localization-flat and remain
   reduced. Apply lem-per-flat-integral-total-fractions to A -> A_f and
   E tensor A -> (E tensor A)_(1 tensor f). The normality in step 4 identifies
   the localized normalization. The tensor and localization universal properties
   identify E tensor B_f with (E tensor B)_(1 tensor f).
6. These identifications send e tensor (b/f^n) to (e tensor b)/(1 tensor f)^n.
   Consequently the displayed localized comparison square commutes, first on
   pure tensors and then by localization uniqueness. No inversion of f in Q(A)
   is used: f may be a zero divisor or zero. All maps for the zero algebra are
   the unique maps of zero rings.
-/
theorem geonormal_normalization_fieldExtension
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (hred : ∀ (E : Type (max u v)) [Field E] [Algebra k E], IsReduced (E ⊗[k] A))
    (B : Subalgebra A (FractionRing A)) (hB : B = integralClosure A (FractionRing A))
    [Module.Finite A B]
    (hnormal : ∀ (E : Type (max u v)) [Field E] [Algebra k E],
      ∀ (p : Ideal (E ⊗[k] B)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∃ hregular : ∀ (E : Type (max u v)) [Field E] [Algebra k E],
        nonZeroDivisors A ≤ (nonZeroDivisors (E ⊗[k] A)).comap
          (Algebra.TensorProduct.includeRight : A →ₐ[k] E ⊗[k] A).toRingHom,
      ∃ j : ∀ (E : Type (max u v)) [Field E] [Algebra k E],
          E ⊗[k] B →ₐ[E] FractionRing (E ⊗[k] A),
        (∀ (E : Type (max u v)) [Field E] [Algebra k E],
          Function.Injective (j E) ∧
          Set.range (j E) = (integralClosure (E ⊗[k] A) (FractionRing (E ⊗[k] A)) : Set _) ∧
          ∀ (e : E) (b : B), j E (e ⊗ₜ[k] b) =
            algebraMap (E ⊗[k] A) (FractionRing (E ⊗[k] A)) (e ⊗ₜ[k] (1 : A)) *
            IsLocalization.map (FractionRing (E ⊗[k] A))
              (Algebra.TensorProduct.includeRight : A →ₐ[k] E ⊗[k] A).toRingHom
              (hregular E) (b : FractionRing A)) ∧
        (∀ (E F : Type (max u v)) [Field E] [Field F] [Algebra k E] [Algebra k F]
            (φ : E →ₐ[k] F),
          ∃ htower : nonZeroDivisors (E ⊗[k] A) ≤
              (nonZeroDivisors (F ⊗[k] A)).comap
                (Algebra.TensorProduct.map φ (AlgHom.id k A)).toRingHom,
            ∀ c : E ⊗[k] B,
              IsLocalization.map (FractionRing (F ⊗[k] A))
                (Algebra.TensorProduct.map φ (AlgHom.id k A)).toRingHom htower (j E c) =
              j F (Algebra.TensorProduct.map φ (AlgHom.id k B) c)) ∧
        (∀ (E : Type (max u v)) [Field E] [Algebra k E] (f : A),
          ∃ hlocal : nonZeroDivisors (E ⊗[k] A) ≤
              (nonZeroDivisors (Localization.Away ((1 : E) ⊗ₜ[k] f))).comap
                (algebraMap (E ⊗[k] A) (Localization.Away ((1 : E) ⊗ₜ[k] f))),
            ∃ (jlocal : E ⊗[k] Localization.Away (algebraMap A B f) →ₐ[E]
                FractionRing (Localization.Away ((1 : E) ⊗ₜ[k] f)))
              (ρ : E ⊗[k] Localization.Away f ≃ₐ[E]
                Localization.Away ((1 : E) ⊗ₜ[k] f))
              (ι : E ⊗[k] Localization.Away (algebraMap A B f) ≃ₐ[E]
                Localization.Away ((1 : E) ⊗ₜ[k] algebraMap A B f)),
              Function.Injective jlocal ∧
              Set.range jlocal = (integralClosure
                (Localization.Away ((1 : E) ⊗ₜ[k] f))
                (FractionRing (Localization.Away ((1 : E) ⊗ₜ[k] f))) : Set _) ∧
              (∀ (e : E) (a : A),
                ρ (e ⊗ₜ[k] algebraMap A (Localization.Away f) a) =
                  algebraMap (E ⊗[k] A)
                    (Localization.Away ((1 : E) ⊗ₜ[k] f)) (e ⊗ₜ[k] a)) ∧
              (∀ (e : E) (b : B),
                ι (e ⊗ₜ[k] algebraMap B (Localization.Away (algebraMap A B f)) b) =
                  algebraMap (E ⊗[k] B)
                    (Localization.Away ((1 : E) ⊗ₜ[k] algebraMap A B f)) (e ⊗ₜ[k] b)) ∧
              ∀ c : E ⊗[k] B,
                jlocal (ι.symm (algebraMap (E ⊗[k] B)
                  (Localization.Away ((1 : E) ⊗ₜ[k] algebraMap A B f)) c)) =
                IsLocalization.map (FractionRing (Localization.Away ((1 : E) ⊗ₜ[k] f)))
                  (algebraMap (E ⊗[k] A) (Localization.Away ((1 : E) ⊗ₜ[k] f)))
                  hlocal (j E c)) := by
  sorry
