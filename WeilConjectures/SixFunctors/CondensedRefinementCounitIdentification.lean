/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.NormalizedGammaRefinementEquality
public import WeilConjectures.AlgebraicGeometry.FiniteProperLocalizing
public import WeilConjectures.SixFunctors.ProjectionRefinementDescent
import WeilConjectures.SixFunctors.ProjectionRefinementNormalization

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
open WeilConjectures
open WeilConjectures.ProjectionRefinementDescent

namespace WeilConjectures

/-- The finite-level comparison, identity, and cocycle package used by the refinement
identification.  It is the common-refinement consequence on the bounded-constructible
subcategory, with every comparison pinned by `theta`.

Source: `lem-sf-projection-refinement-descent`, finite-level comparison-cocycle clause;
blueprint: `lem-sf-condensed-refinement-counit-identification`.
-/
def finiteLevelRefinementConsequences
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E]
    [FiniteDimensional ℚ_[C.l] E] (n : ℕ)
    (_S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    {X Y : AmbientProperOpen.Spaces D} (f : X ⟶ Y) [QuasiCompact f.hom.left]
    [LocallyOfFiniteType f.hom.left] [IsSeparated f.hom.left] : Prop :=
  let Rho := ∀ c d : Compactification f.hom.left,
    (ProjectionRefinementDescent.boundedConstructible C.l E n X.obj.left).ι ⋙
      ProjectionRefinementDescent.image C.l E n c ≅
    (ProjectionRefinementDescent.boundedConstructible C.l E n X.obj.left).ι ⋙
      ProjectionRefinementDescent.image C.l E n d
  ∃ rho : Rho,
    (∀ (c d b : Compactification f.hom.left) (r₀ : b.Refinement c)
      (s₀ : b.Refinement d)
      (K₀ : (ProjectionRefinementDescent.boundedConstructible C.l E n X.obj.left).FullSubcategory)
      (O₀ : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X.obj.left)
      (e₀ : refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n)
        X.obj.left O₀ ≅ K₀.obj),
      (rho c d).app K₀ =
        (theta C.l E n r₀ K₀.obj O₀ e₀).symm ≪≫ theta C.l E n s₀ K₀.obj O₀ e₀) ∧
    (∀ c : Compactification f.hom.left, rho c c = Iso.refl _) ∧
    (∀ (c d b : Compactification f.hom.left), rho c d ≪≫ rho d b = rho c b)

set_option maxHeartbeats 10000000 in
-- The full finite-level comparison package elaborates through large derived-category terms.
/-- The finite quotient identification of the clopen refinement counit with the
normalized proper/open refinement comparison.  The equality on the ordinary condensed
category is stated before restriction; the finite descent comparison is stated on every
`ProperOpenDerived` object and every retained origin witness.  The final existential is
the finite-level isomorphism, common-refinement independence, identity normalization,
and cocycle package of `finite_descent`.

Proof steps from the source:
1. Specialize the ambient refinement construction to the discrete condensed ring `A_n`;
the clopen adjunct is the native reindexing map.
2. For the square `(j₁,j₂,1_X,u)`, the normalized `CondensedOpenProper.gamma` is the
same adjunct as the clopen projector, by the mate-transpose, clopen-localization, and
pullback-coherence calculations; this also covers empty and identity refinements.
3. Apply `Rp₂*` and the canonical direct-image compositor.  Derived-composition
normalization identifies the compositor in the counit construction with the one in the
descent construction, so the two natural transformations agree on the whole ordinary
category.
4. The finite-level isomorphism, common-refinement independence, identity normalization,
and cocycle laws supplied by `finite_descent` transport along the equality of the two maps.
Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/`
`prop-sf-pf-coherence.proof.md`, independence of compactification and refinement paragraphs.
(blueprint: `lem-sf-condensed-refinement-counit-identification`).
-/
theorem condensed_refinement_counit_identification
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E]
    [FiniteDimensional ℚ_[C.l] E] (n : ℕ)
    (S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    {X Y : AmbientProperOpen.Spaces D}
    (f : X ⟶ Y) [QuasiCompact f.hom.left] [LocallyOfFiniteType f.hom.left]
    [IsSeparated f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂)
    (P : Pasting (finiteDiscreteCondensedCoefficient
      (Padic.coefficientExtensionRing C.l E (n + 1)))) :
    And
      (normalizedGammaRefinement
        (finiteDiscreteCondensedCoefficient
          (Padic.coefficientExtensionRing C.l E (n + 1))) r P =
        CompactificationReindexing.refinement
          (finiteDiscreteCondensedCoefficient
            (Padic.coefficientExtensionRing C.l E (n + 1))) r)
      (And
        (∀ (K : ProperOpenDerived (Coefficient C.l E n) X.obj.left)
          (O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X.obj.left)
          (e : refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n)
            X.obj.left O ≅ K),
          (theta C.l E n r K O e).inv =
            RefinementProjection.finiteComparison D (Coefficient C.l E n) r K)
        (finiteLevelRefinementConsequences D C E n S f)) := by
  refine ⟨?_, ?_⟩
  · apply normalizedGammaRefinement_transport _ r P
    exact normalizedGammaAdjunct_eq_refinementAdjunct _ r P
  · refine ⟨?_, ?_⟩
    · intro K O e
      exact ProjectionRefinementDescent.normalized_refinement_inverse D C E n r K O e
    · unfold finiteLevelRefinementConsequences
      obtain ⟨rho, hn, hc, ht⟩ :=
        (ProjectionRefinementDescent.finite_descent D C E n S (f := f.hom.left)).2.2
      refine ⟨rho, hn, ?_, hc⟩
      intro c
      ext K
      have hcc := congrArg (fun q => q.hom.app K) (hc c c c)
      apply (cancel_mono ((rho c c).hom.app K)).1
      simpa [Iso.trans_hom] using hcc

end WeilConjectures
