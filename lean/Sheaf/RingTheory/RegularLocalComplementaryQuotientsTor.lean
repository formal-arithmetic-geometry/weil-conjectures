/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Length
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular

/-! # Tor for complementary regular local quotients

Source: Stacks Project, intersection.tex, Tag 0B1I, proof of lemma-transversal
(blueprint: lem-trf-regular-local-complementary-quotients-tor).

The two augmentations below are specified on degree-zero generators. Their
quasi-isomorphism assertions express the quotient resolution and its canonical
homology identification after tensoring. The degree-zero Tor comparison is
normalized through Mathlib's canonical map from the zeroth left derived functor.
The alternating sum is taken through degree `r`, the length of the Koszul resolution;
all subsequent Tor modules vanish, and every length in the sum is finite.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct BigOperators

namespace RingTheory

/-- Complementary regular local quotients have only the residue field as their Tor.
Source: Stacks Project, intersection.tex, Tag 0B1I, proof of lemma-transversal
(blueprint: lem-trf-regular-local-complementary-quotients-tor).

Proof:
1. Apply `lem-weil-pbc-regular-local-quotient-kernel-parameters` to `A,I` to choose
   parameters with a prefix of length `c` generating `I`. The quotient dimension
   formula of `lem-weil-pbc-regular-local-generators-regular-sequence` gives
   `s = r+s-c`, hence `c=r`. That lemma makes the full list regular. Its first `r`
   injectivity conditions make the prefix weakly regular, and the prefix quotient
   is nonzero because it surjects onto the residue field. Thus the prefix is regular.
2. In `B=A/J`, the images of this prefix generate the maximal ideal, because
   `I+J=m`. They are `r` generators and `dim B=r`. Apply
   `lem-weil-pbc-regular-local-generators-regular-sequence` again to get regularity
   over `B`. Its successive quotients and scalar multiplications are the same
   whether regarded over `B` or over `A`.
3. By `lem-weil-pbc-regular-sequence-koszul-regular`, the positive homology of the
   Koszul complex vanishes. The exterior-power basis gives finite free terms and
   zero terms above `r`. Its degree-one differential has image `I`, and degree zero
   is `A`, so the quotient augmentation is a quasi-isomorphism resolving `A/I`.
4. Apply the same Koszul-regularity lemma with coefficient module `B`. Positive
   tensor homology vanishes. In degree zero the differential has image `IB`, so
   the quotient augmentation identifies homology with `B/IB=A/(I+J)`. Its formula
   is the class of a product, and `I+J=m` identifies this quotient with the residue
   field by the quotient map, fixing the canonical normalization.
5. Compute `Tor'` from the free resolution in step 3, using
   `def-weil-pbc-tor-modules`. Step 4 gives zero positive Tor and the residue field
   in degree zero; Mathlib's `fromLeftDerivedZero` fixes the usual tensor-product
   normalization. The residue field is a simple `A`-module, since every nonzero
   element generates it; its length is one by `def-weil-pbc-module-length`.
   All positive Tor modules have length zero, so the alternating length sum is one.
   When `r=0`, `I=0`, `J=m`, and the complex is `A[0]`; when `s=0`, the prefix is
   the full parameter list and `I=m`. Every construction includes the empty list.
-/
theorem regularLocal_complementary_quotients_tor
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (r s : ℕ) (hdim : ringKrullDim A = ((r + s : ℕ) : WithBot ℕ∞))
    (I J : Ideal A) (hI : I ≠ ⊤) (hJ : J ≠ ⊤)
    [IsRegularLocalRing (A ⧸ I)] [IsRegularLocalRing (A ⧸ J)]
    (hIdim : ringKrullDim (A ⧸ I) = (s : WithBot ℕ∞))
    (hJdim : ringKrullDim (A ⧸ J) = (r : WithBot ℕ∞))
    (htrans : I ⊔ J = IsLocalRing.maximalIdeal A) :
    ∃ (f : Fin (r + s) → A) (g : Fin r → A),
      g = (fun i ↦ f (Fin.castAdd s i)) ∧
      IsLocalRing.IsRegularSystemOfParameters (List.ofFn f) ∧
      I = Ideal.span (Set.range g) ∧
      RingTheory.Sequence.IsRegular A (List.ofFn g) ∧
      RingTheory.Sequence.IsRegular (A ⧸ J)
        (List.ofFn (fun i ↦ Ideal.Quotient.mk J (g i))) ∧
      (∀ n : ℕ, Module.Free A ((ExteriorAlgebra.koszulComplex A r g).X n) ∧
        Module.Finite A ((ExteriorAlgebra.koszulComplex A r g).X n)) ∧
      (∀ n : ℕ, r < n → IsZero ((ExteriorAlgebra.koszulComplex A r g).X n)) ∧
      (∃ ε : ExteriorAlgebra.koszulComplex A r g ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ I)),
        QuasiIso ε ∧ ∀ x : ⋀[A]^0 (Fin r →₀ A),
          ε.f 0 x = Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) ∧
      (∀ n : ℕ, 0 < n →
        IsZero ((ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J)).homology n)) ∧
      (∃ δ : ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J) ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ (I ⊔ J))),
        QuasiIso δ ∧ ∀ (x : ⋀[A]^0 (Fin r →₀ A)) (a : A),
          δ.f 0 (x ⊗ₜ[A] Ideal.Quotient.mk J a) =
            Ideal.Quotient.mk (I ⊔ J) (exteriorPower.zeroEquiv A (Fin r →₀ A) x * a)) ∧
      (∃ e : ModuleCat.of A (A ⧸ (I ⊔ J)) ≅ ModuleCat.of A (IsLocalRing.ResidueField A),
        ∀ a : A, e.hom (Ideal.Quotient.mk (I ⊔ J) a) = IsLocalRing.residue A a) ∧
      (∀ i : ℕ, 0 < i → IsZero
        (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J)))) ∧
      (∃ eTensor : ModuleCat.of A ((A ⧸ I) ⊗[A] (A ⧸ J)) ≅
          ModuleCat.of A (IsLocalRing.ResidueField A),
        ∃ eTor : (((Tor' (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
            (ModuleCat.of A (A ⧸ J))) ≅ ModuleCat.of A (IsLocalRing.ResidueField A),
          (∀ a b : A, eTensor.hom
            (Ideal.Quotient.mk I a ⊗ₜ[A] Ideal.Quotient.mk J b) =
              IsLocalRing.residue A (a * b)) ∧
          eTor.hom =
            (Functor.fromLeftDerivedZero
              ((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J)))).app
                (ModuleCat.of A (A ⧸ I)) ≫ eTensor.hom) ∧
      (∀ i : ℕ, Module.length A
        (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J))) ≠ ⊤) ∧
      (∑ i ∈ Finset.range (r + 1), (-1 : ℤ) ^ i *
        (Module.length A
          (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
            (ModuleCat.of A (A ⧸ J)))).toNat) = 1 := by
  sorry

end RingTheory
