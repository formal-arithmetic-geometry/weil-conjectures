/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import Sheaf.SixFunctorsBasics.BrownHypotheses
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
import Sheaf.Paper.RationalExceptionalRestriction
import WeilConjectures.Compactification.Dense
import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.SixFunctors.IntegralBrownAdjoint
import Sheaf.SixFunctors.IntegralExceptionalRestriction

/-!
# Existence of the exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-existence/_section.md,
and det-existence-localizing.proof.md and det-existence-restriction.proof.md
(blueprint: sk-thm-existence).

The lower shriek is the existing restriction of the actual compactification composite.
All categories are full subcategories of the ordinary unbounded module-object derived
category, with the recorded finite constant-model constructibility convention.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

local notation "S(" T ")" =>
  (constantModelBoundedConstructible Λ T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K)
local notation "L(" T ")" => localizingClosureProEtale Λ T

/-- The four existence assertions, including restriction of the same Brown right adjoint.
The witnesses for triangulation and coproducts install the inherited structures before
compactness or exactness is asserted. The small skeletal family has exactly one object
in each isomorphism class of Dctf and generates the localizing category. Preservation
of Dctf by both adjoints means that the displayed adjunction restricts along the fully
faithful inclusions, with the same Hom equivalences. For each of the five non-finite
coefficient objects, the final clause identifies Dctf and Dbc as ambient object properties.

Source: blueprint main-20261015, sk-thm-existence, clauses 1--4 and final paragraph
(blueprint: sk-thm-existence).

Proof:
1. Apply sk-lem-brown-hypotheses to X. It gives compactness of every Dctf object
   in its closure and a small skeleton of compact generators, together with the
   triangulated and coproduct structures required by Brown representability.
2. Both schemes are qcqs: their structure maps are quasi-compact and separated
   over the affine scheme Spec k. Separated cancellation and locally-finite-type
   cancellation show that f is separated and locally of finite type; quasi-compactness
   of X and quasi-separatedness of Y show that f is quasi-compact. Apply Nagata to f.
   For its chosen compactification, det-sf-comp-coherence-single gives preservation
   of both closures, exactness, direct sums and Dctf. The comparisons of
   det-sf-comp-coherence-cocycle identify the functors from other compactifications.
3. Apply sk-prop-sf-existence once to this exact sum-preserving functor. Brown
   representability produces its right adjoint. Transposing the shift comparison
   gives a coherent shift comparison for that adjoint, which is exact.
4. For finite A, sk-prop-sf-rf-shriek-preservation gives preservation of Dctf by
   this right adjoint. For O_E, det-prop-int-brown-adjoint identifies it with the
   integral Brown adjoint and sk-thm-int-restriction gives preservation. For E and
   the algebraic closure use sk-thm-restriction for the same general right adjoint.
   Z_l and Q_l are the cases E = Q_l. Restrict the Hom equivalences along the full
   Dctf inclusions; their naturality and triangle identities are unchanged.
5. For the five non-finite coefficients, apply
   det-def-localizing-closure-ctf-equals-bc to X and Y, using their qcqs property.
   Thus Dctf = Dbc as ambient full subcategories, so all four conclusions apply
   to Dbc as well. No such equality, regularity or Gorenstein condition is imposed
   for finite A. The zero ring and the empty schemes are included.
-/
theorem exceptionalInverseImage_exists
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ (hX : L(X.left).IsTriangulated) (hY : L(Y.left).IsTriangulated)
      (hSX : S(X.left) ≤ L(X.left)) (hSY : S(Y.left) ≤ L(Y.left))
      (h : ∀ K, L(X.left) K → L(Y.left)
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj K))
      (sX : HasCoproducts.{u + 1} L(X.left).FullSubcategory)
      (sY : HasCoproducts.{u + 1} L(Y.left).FullSubcategory),
      (fun [triX : L(X.left).IsTriangulated] [triY : L(Y.left).IsTriangulated]
          [sumsX : HasCoproducts.{u + 1} L(X.left).FullSubcategory]
          [sumsY : HasCoproducts.{u + 1} L(Y.left).FullSubcategory] ↦
        (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
          IsCompactObject.{u + 1} ((ObjectProperty.ιOfLE hSX).obj K)) ∧
        (LocallySmall.{u + 1} (ConstantModelConstructibleFiniteTor Λ X.left) ∧
          ∃ (I : Type (u + 1)) (E : I → ConstantModelConstructibleFiniteTor Λ X.left),
          (∀ K, ∃ i, Nonempty (E i ≅ K)) ∧
          (∀ i j, Nonempty (E i ≅ E j) → i = j) ∧
          IsTriangulatedGeneratingFamily (fun i ↦ (ObjectProperty.ιOfLE hSX).obj (E i))) ∧
        (localizingLowerShriek Λ (compactificationOverField f) h).IsTriangulated ∧
        (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
          (localizingLowerShriek Λ (compactificationOverField f) h)) ∧
        (∀ K : L(X.left).FullSubcategory, S(X.left) K.obj →
          S(Y.left) ((localizingLowerShriek Λ (compactificationOverField f) h).obj K).obj) ∧
        (∀ c : Compactification f.left, Nonempty
          ((localizingLowerShriek Λ (compactificationOverField f) h) ⋙ L(Y.left).ι ≅
            L(X.left).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)) ∧
        (∃ G : L(Y.left).FullSubcategory ⥤ L(X.left).FullSubcategory,
          ∃ s : G.CommShift ℤ,
            (fun [comm : G.CommShift ℤ] ↦
              G.IsTriangulated ∧
              Nonempty (localizingLowerShriek Λ (compactificationOverField f) h ⊣ G) ∧
              (∀ N : L(Y.left).FullSubcategory, S(Y.left) N.obj → S(X.left) (G.obj N).obj))
              (comm := s)) ∧
        ((Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
          (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
          (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))) →
          S(X.left) = constantModelBoundedConstructible Λ X.left ∧
          S(Y.left) = constantModelBoundedConstructible Λ Y.left))
        (triX := hX) (triY := hY) (sumsX := sX) (sumsY := sY) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
