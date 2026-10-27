/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.DerivedNakayamaResolution
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Abelian.Images

/-! # Classical cohomology of integral-image Koszul complexes

Source: HRS Theorem 6.2(3) and Section 7.1.1; Stacks Tag 09AK.
(blueprint: lem-sfb-integral-image-koszul-classical).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The cohomology of the literal Koszul complex of an actual integral image is classical.
Source: HRS Theorem 6.2(3), Section 7.1.1, and Stacks Tags 09AK and 099V.
(blueprint: lem-sfb-integral-image-koszul-classical).

Proof: use the one-stratum stratification to make L and M constructible. Identify the
finite extension E with an embedded finite subextension of an algebraic closure of Q_l,
and transport its valuation integers, scalar presentations and condensed coefficients
along this isomorphism to apply the published Noetherian constructible-heart theorem.
That heart is closed under kernels and cokernels, hence under the actual image
ker(M -> coker f), which is canonically isomorphic to image f. The finite-model quotient
calculation at index n-1 (since n>=1) gives finite constructible B/pi^n-module cohomology
in degrees -1 and 0. Principal reduction identifies the underlying two-term complex with the
literal scalar complex below; its scalar endomorphism agrees with the chosen resolution
scalar because both have the same sectionwise multiplication formula. Constructible
comparison over the finite discrete ring B/pi^n makes these cohomology sheaves classical.
Forgetting their scalar action gives the displayed abelian comparison antecedents.
In other degrees the two-term complex has zero homology, which is the pullback of zero.
This includes zero maps, empty S, torsion images and n=1. No closed-image convention is used.
-/
theorem integral_image_koszul_classical
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) S)) (f : L ⟶ M)
    (hL : HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S L)
    (hM : HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S M)
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ q : ℤ, (comparisonUpperStar Ab.{u + 1} S).essImage
      ((HomologicalComplex.double
        (((DerivedNakayama.scalarOnModules ℓ E S
          ((DerivedNakayama.derived_nakayama_resolution ℓ E).choose ^ n)).app
            (image f)).hom) (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0)
        (by decide)).homology q) := by sorry

end AlgebraicGeometry.ProEtale
