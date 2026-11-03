/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData

/-! # Refinement comparisons before total inverse limit

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-direct-image.proof.md,
paragraph (2) (blueprint: lem-sp-integral-image-tower-refinement-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite proper/open refinement comparisons assemble on the actual image towers;
their total limits commute with the specified integral refinement maps.

Source: the current direct-image proof, paragraph (2), compactification independence
(blueprint: lem-sp-integral-image-tower-refinement-compatibility).

Proof: give the geometric tower calculus the section-preserving evaluation coordinates
of the supplied presentation. Reduction of a constructible integral complex is a
normalized constructible tower with uniform finite-Tor bounds. The finite comparisons
are the proper/open refinement maps of compactification_coherence. The geometric
calculus constructs their whole-system comparisons and proves identity, cocycle and
common-refinement independence before taking limits. In particular this step does not
infer equality of derived morphisms from equality of their evaluations. Normalize the
scalar pullback comparison on quotient tensor generators. Taking its proper counit
mate and the inverse open unit mate identifies reduction of the actual integral
refinement component with the same system refinement map. Transpose this equality
through the normalized reduction/limit adjunction and use unit naturality. It is the
last displayed equality, with the actual reconstruction maps at both ends. Naturality
in the integral input is inherited from the whole-system transformations. All source
and target categories here precede total inverse limit; no integral coherence theorem
or integral proper projection formula is used. Empty schemes and identity refinements
satisfy the same generator and triangle equations. -/
theorem integral_image_tower_refinement_compatibility
    (s : Presentation l E) (q : ReductionGeometry l E s)
    (hq : OpenReductionIsIso l E s q) (L : ∀ T : Scheme.{u}, Limit l E s T)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (_v : ∀ c : Compactification f, CanonicalTowerComparison l E s q hq c) :
    ∃ τ : ∀ c₁ c₂ : Compactification f,
        (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙
            red l E s X ⋙ towerShriek l E s c₁ ≅
          (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙
            red l E s X ⋙ towerShriek l E s c₂,
      (∀ c : Compactification f, τ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, τ c₁ c₂ ≪≫ τ c₂ c₃ = τ c₁ c₃) ∧
      ∀ (c : Compactification.BoundaryCompactification f)
        (r : Compactification.DenseBoundaryCompactification f) (h : r.obj ⟶ c)
        (M : Constructible l E X),
        reconstruction l E s c.obj.obj (L Y) q hq M ≫
            (lim l E s Y (L Y)).map ((τ c.obj.obj r.obj.obj.obj).hom.app M) =
          CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h M.obj ≫
            reconstruction l E s r.obj.obj.obj (L Y) q hq M := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
