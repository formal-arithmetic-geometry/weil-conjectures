/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Sheaf.Paper.SfOpenClosedTriangleData
public import Sheaf.CategoryTheory.StageSystemFunctorDescent

/-! # Scalar coherence of normalized recollement presentations

Source: blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, coefficient passage in the
triangle and Hom-vanishing paragraphs
(blueprint: lem-sf-normalized-recollement-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Scalar extension intertwines the normalized rational open and closed terms,
coherently over towers, preserving the given counit and unit.
Source: blueprint localization proof, triangle and Hom-vanishing paragraphs;
coefficient passage in the proof of common-stage descent
(blueprint: lem-sf-normalized-recollement-scalar-coherence).
Proof: use the ordinary tensor comparison for the completed closed inverse-image
and direct-image unit. Exact coefficient extension carries the kernel of that unit
to the kernel of the extended unit, with its kernel inclusion. The universal property
of the kernel makes these comparisons natural and gives their tower equation from
the tensor associator equation. The closed comparison is the composite pullback and
direct-image comparison; compatibility of adjunction mates gives its unit square.
Compare each supplied integral presentation with these ordinary terms using its
normalization on representative complexes. Essential surjectivity of the complex
localization and naturality extend the map squares and the isomorphisms to every
integral object. Conjugation transports the tower equations. Apply raw scalar
localization to the comparisons and squares, then conjugate by the supplied rational
normalization isomorphisms. The conjugating maps cancel in each tower equation and
each square. This yields exactly the two comparisons and four conditions below.
No descended functor, distinguished triangle, or common-stage Hom assertion is
part of this lemma. The construction uses no finite-field structure on k and works
for zero objects and empty open or closed complements. -/
theorem sfNormalizedRecollement_scalar_coherence
    (k : Type u) [Field k] (_hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X))
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L))
    (hPQ : ∀ L, SfIntegralRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
        (sfRecollementNoetherian k X) (P L) ∧
      SfRationalRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (P L) (Q L)) :
    ∃ (a : ∀ {L M : AlgebraicallyClosedCoefficients.Index l Ω} (h : L ≤ M),
        (Q L).openTerm ⋙ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ⋙ (Q M).openTerm)
      (c : ∀ {L M : AlgebraicallyClosedCoefficients.Index l Ω} (h : L ≤ M),
        (Q L).closedTerm ⋙ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ⋙ (Q M).closedTerm),
      CategoryTheory.StageSystem.pairFunctorCoherent
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
        (fun L ↦ (Q L).openTerm) a ∧
      CategoryTheory.StageSystem.pairFunctorCoherent
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
        (fun L ↦ (Q L).closedTerm) c ∧
      (∀ {L M : AlgebraicallyClosedCoefficients.Index l Ω} (h : L ≤ M) K,
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).map
            ((Q L).counit.app K) =
          (a h).hom.app K ≫ (Q M).counit.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K)) ∧
      ∀ {L M : AlgebraicallyClosedCoefficients.Index l Ω} (h : L ≤ M) K,
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).map
            ((Q L).unit.app K) ≫ (c h).hom.app K =
          (Q M).unit.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K) := by sorry

end WeilConjectures
