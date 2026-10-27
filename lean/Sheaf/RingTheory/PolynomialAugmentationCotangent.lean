/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.RingTheory.CotangentTransitivityTriangle
import Sheaf.RingTheory.PolynomialCotangentIdentification
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.RingTheory.RegularSequenceConormal

/-!
# Cotangent complex of the integer polynomial augmentation

Source: Stacks Project, Cotangent Complex, Tag 08SI (lemma-special-case),
with the conormal comparison of lemma-surjection
(blueprint: lem-trf-cotangent-polynomial-special-case).

The target is Mathlib's actual conormal module, placed in degree `-1`, namely
`(J/J²)[1]`. The isomorphism is normalized on standard relation cycles. The
integer scalar action on the conormal module is the coefficient action, which
agrees with the action through the augmentation quotient `P/J ≃ ℤ`.

The integers are taken as `ULift.{u} ℤ`, so that the statement is available in
every universe of the recorded standard cotangent complex, as its citers
(for example lem-trf-koszul-quotient-cotangent-vanishing) require. For `u = 0`
this is the integer ring itself up to the canonical ring isomorphism.

## Main declarations

* `augmentationIdeal`, `augmentationArrow`: the prescribed ideal and ring map.
* `augmentationModel`, `relationVector`: standard complex and its relation vectors.
* `conormalHomologyMap`: the degree `-1` normalization of the isomorphism.
* `exists_canonical_iso_and_basis`: canonical derived isomorphism, basis and zero case.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Algebra.CotangentResolution

namespace Algebra.PolynomialAugmentationCotangent

/-- The ideal `J = (x₁,…,xₙ)` in the integer polynomial ring, including `J = 0`
for `n = 0`. Source: Stacks, Tag 08SI
(blueprint: lem-trf-cotangent-polynomial-special-case). -/
def augmentationIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) (ULift.{u} ℤ)) :=
  Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) (ULift.{u} ℤ)))

/-- The actual augmentation `ℤ[x₁,…,xₙ] → ℤ`, sending each variable to zero.
Source: Stacks, Tag 08SI
(blueprint: lem-trf-cotangent-polynomial-special-case). -/
def augmentationArrow (n : ℕ) : Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom
    (MvPolynomial.eval₂Hom (RingHom.id (ULift.{u} ℤ)) (fun _ : Fin n ↦ 0)))

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The standard differential complex for the polynomial augmentation.
Source: Stacks, Tags 08PN and 08SI
(blueprint: lem-trf-cotangent-polynomial-special-case). -/
def augmentationModel (C : Coherence.{u}) (n : ℕ) :=
  differentialComplex (C.differentials (C.standard (augmentationArrow n)))

/-- The degree `-1` standard relation vector `1 ⊗ d([C(a)] - [0])` for `a ∈ J`.
Its faces have zero differential: one is a base constant and the other is zero.
The cast uses the prescribed polynomial coordinates of the standard resolution.
Source: Stacks, lemma-surjection and Tag 08SI
(blueprint: lem-trf-cotangent-polynomial-special-case). -/
def relationVector (C : Coherence.{u}) (n : ℕ) (a : augmentationIdeal n) :
    (augmentationModel C n).X (-1) :=
  complexGenerator (C.differentials (C.standard (augmentationArrow n))) 1 1
    (_root_.cast (congrArg (fun T : CommRingCat.{u} ↦ (T : Type u))
      ((C.standard_spec (augmentationArrow n)).1 1).symm)
      (MvPolynomial.X (MvPolynomial.C (a : MvPolynomial (Fin n) (ULift.{u} ℤ))) -
        MvPolynomial.X (MvPolynomial.C (0 : MvPolynomial (Fin n) (ULift.{u} ℤ)))))

/-- The degree `-1` map of a conormal isomorphism, transported to the homology
of the concrete standard complex and the actual module `J/J²`.
Source: Stacks, lemma-surjection and Tag 08SI
(blueprint: lem-trf-cotangent-polynomial-special-case). -/
def conormalHomologyMap (C : Coherence.{u}) (n : ℕ)
    (e : cotangentComplex C (augmentationArrow n) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of (ULift.{u} ℤ))) (-1)).obj
        (ModuleCat.of (ULift.{u} ℤ) (augmentationIdeal n).Cotangent)) :
    (augmentationModel C n).homology (-1) ⟶
      ModuleCat.of (ULift.{u} ℤ) (augmentationIdeal n).Cotangent :=
  (DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} (CommRingCat.of (ULift.{u} ℤ))) (-1)).inv.app
      (augmentationModel C n) ≫
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (CommRingCat.of (ULift.{u} ℤ))) (-1)).map e.hom ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (CommRingCat.of (ULift.{u} ℤ))) (-1)).hom.app
        (ModuleCat.of (ULift.{u} ℤ) (augmentationIdeal n).Cotangent)

/-- The polynomial augmentation has canonical cotangent complex `(J/J²)[1]`;
the variable classes form an integer basis of `J/J²`. The normalization sends
each standard relation cycle for `a ∈ J` to the class of `a`. For `n = 0`, both
derived objects are zero.
Source: Stacks, Tag 08SI (lemma-special-case), with lemma-surjection
(blueprint: lem-trf-cotangent-polynomial-special-case).

Proof:
1. Apply lem-trf-cotangent-transitivity-triangle to `ℤ → P → ℤ`. This gives
   `L[P/ℤ] ⊗ᴸ[P] ℤ → L[ℤ/ℤ] → L[ℤ/P] → (L[P/ℤ] ⊗ᴸ[P] ℤ)[1]`.
2. By lem-trf-smooth-cotangent-identification the first cotangent complex is
   `Ω[P/ℤ][0]`. The basis of lem-weil-pbc-polynomial-ring-kahler-basis-any-variables
   makes it free on `dxᵢ`; its derived tensor is its ordinary tensor with `ℤ`.
3. The constant polynomial resolution for the identity `ℤ → ℤ` has zero
   differential module. The comparison of lem-trf-cotangent-resolution-coherence
   therefore makes the middle cotangent complex zero, also when `n = 0`.
4. Rotate the triangle to identify `L[ℤ/P]` with the shifted tensor in step 2.
   The boundary map gives the canonical identification.
5. Successive quotients by preceding variables are polynomial rings over `ℤ`,
   so each next variable is a non-zero-divisor. Apply
   lem-weil-pbc-regular-sequence-conormal-free to get the basis `[xᵢ]` of `J/J²`.
   Send `1 ⊗ dxᵢ` to `[xᵢ]` and compose its shifted isomorphism with step 4.
   The surjection conormal comparison sends the standard cycle
   `1 ⊗ d([C(a)] - [0])` to `[a]`; its two faces have zero differential.
   This is the asserted normalization. When `n = 0`, the basis is empty,
   `J/J² = 0`, and the displayed derived isomorphism makes both sides zero. -/
theorem exists_canonical_iso_and_basis (C : Coherence.{u}) (n : ℕ) :
    (∃ e : cotangentComplex C (augmentationArrow n) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of (ULift.{u} ℤ))) (-1)).obj
          (ModuleCat.of (ULift.{u} ℤ) (augmentationIdeal n).Cotangent),
      ∀ a : augmentationIdeal n,
        ∃ z : (augmentationModel C n).cycles (-1),
          (augmentationModel C n).iCycles (-1) z = relationVector C n a ∧
            conormalHomologyMap C n e ((augmentationModel C n).homologyπ (-1) z) =
              (augmentationIdeal n).toCotangent a) ∧
      (∃ b : Module.Basis (Fin n) (ULift.{u} ℤ) (augmentationIdeal n).Cotangent,
        ∀ i : Fin n, b i = (augmentationIdeal n).toCotangent
          ⟨MvPolynomial.X i, Ideal.subset_span ⟨i, rfl⟩⟩) ∧
      (n = 0 → IsZero (cotangentComplex C (augmentationArrow n)) ∧
        IsZero ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (CommRingCat.of (ULift.{u} ℤ))) (-1)).obj
          (ModuleCat.of (ULift.{u} ℤ) (augmentationIdeal n).Cotangent))) := by
  sorry

end Algebra.PolynomialAugmentationCotangent
