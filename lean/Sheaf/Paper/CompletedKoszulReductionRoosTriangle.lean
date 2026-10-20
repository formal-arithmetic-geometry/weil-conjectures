/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted

/-! # The normalized quotient Roos triangle on explicit Koszul completion

Source: blueprint order 1248; Stacks Tags 091Z and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Explicit Koszul completion carries a quotient Roos triangle with normalized unit.
This assertion holds before imposing completeness on the input object.

Source: blueprint Koszul reconstruction, order 1248; Stacks Tags 091Z and 099M
(blueprint: lem-weil-pbc-completed-koszul-reduction-roos-triangle).
Proof: form D : AdicCoefficientDatum A with exactly d's inherited complete datum
and quotient-finiteness certificates; intrinsicPresentationDatum D is definitionally d.
Let B = intrinsicPresentationModulesBack T D and C = B.mapHomologicalComplex(M.complex).
The inverse of B.mapDerivedCategoryFactors at M.complex, followed by the image of
M.realization, realizes C as B.mapDerivedCategory(K). Apply
completedKoszulQuotientComparison to D, C and this realization. This supplies a
unit-normalized isomorphism from intrinsicCompletion to the derived strict quotient
limit. Its source comparison ultimately uses the Noetherian Koszul augmentations:
their cones are pro-zero, also after derived tensor by the K-flat representative,
and their derived inverse limit vanishes.

Apply G = intrinsicPresentationModules T D to the resulting derived comparison.
The completed coefficient ring comparison is an isomorphism, so G and B are exact
inverse equivalences. Their round trips are identity on underlying sections.
Use completedIntrinsicCompletion_descends and the round trip G(C) ≅ M.complex to
identify the transported Koszul fiber and its unit with the exact fiber in this
statement. The representative comparisons supplied by descent preserve the unit;
its naturality and the scalar-equivalence triangle identities give this equality
also for the round trip, rather than just an unnormalized object isomorphism.

At every quotient level, use the finite coefficient comparison induced by constants
and the universal K-flat scalar-extension comparisons to identify the transported
strict quotient tower with adicDatumModelTower T d M. The transition squares hold
because both maps send s tensor m to the quotient of s tensor m. The normalized
ordinary scalar comparisons determine these maps, so the level comparisons form an
isomorphism of the whole derived sequence. Apply completedRlim_roos to the source
strict derived tower. Exact inverse coefficient restrictions preserve products and
distinguished triangles. Transport its two product vertices through that sequence
isomorphism and its first vertex through the Koszul comparison to obtain p and δ.

The source completion unit is the derived constant-limit adjunction unit followed
by the strict quotient augmentation. Its nth evaluation is the ordinary quotient
unit, since every Koszul augmentation sends 1 to 1 and has zero homotopy component.
The normalization in adicDatumAdjunction_exists identifies this with the derived
scalar adjunction unit after the specified model restriction and reduction maps.
The equality from completedKoszulQuotientComparison and the unit-preserving descent
therefore give precisely the displayed equation for each n.
The empty list of generators, zero quotient, and empty scheme use the same normalized
maps and triangles; neither flatness of the quotient nor constancy of a reduced tower
is required. -/
theorem completedKoszulReductionRoosTriangle {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = d.ideal) :
    ∃ (p : completedIntrinsicCompletion T d r f M.complex ⟶
        ∏ᶜ (fun n : ℕ ↦ (adicDatumModelTower T d M).obj (op n)))
      (δ : (∏ᶜ (fun n : ℕ ↦ (adicDatumModelTower T d M).obj (op n))) ⟶
        (completedIntrinsicCompletion T d r f M.complex)⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (adicDatumModelTower T d M).map
          (homOfLE (Nat.le_succ n)).op)
        (completedIntrinsicCompletion T d r f M.complex) p δ ∧
      ∀ n : ℕ,
        completedIntrinsicCompletionMap T d r f M.complex M.realization ≫
          p ≫ Pi.π (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)) n ≫
          (adicDatumModelRestriction T d M n).hom ≫
          (adicDatumRestriction T (adicDatumProjection T d n)).map
            (adicDatumModelReductionIso T d M n).inv =
          (adicDatumAdjunction T (adicDatumProjection T d n)).unit.app K := by
  sorry

end AlgebraicGeometry.Scheme
