/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Refinement.IntegralRefinementPastingData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralNormalizedRefinementPasting
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteTorRefinementDiagram

/-! # The composition component of normalized integral refinement pasting -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
section OverProjection
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (o : Operations l E) (S : Realizations l E D o)
  {X Y : Over (Spec (CommRingCat.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
  (P : IntegralRefinementPastingData l E D hl f)

include S in
/-- The composition component of normalized integral refinement pasting.
Source: `integralNormalizedRefinementPasting` and finite-Tor diagram admissibility.
(blueprint: lem-sf-integral-refinement-composition-pasting-projection).
Proof: extract all eighteen domain witnesses from the common Tor interval, apply
normalized pasting to the fields of the data and normalization records, and take
its composition conjunct. -/
theorem integralRefinementCompositionPastingProjection
    (hnormalization : IntegralRefinementPastingData.Normalized l E D hl f P) :
    ∀ (c d b : Compactification f.left) (v : c.Refinement d) (w : d.Refinement b),
      P.ρ (v.comp w) = P.ρ v ≪≫ P.ρ w := by
  have hDiagram (c : Fin 3 → Compactification f.left)
      (v : (c 0).Refinement (c 1)) (w : (c 1).Refinement (c 2))
      (K : finiteTorConstructibleIntegralCategory l E X.left) (q : Fin 18) :
      (refinementDiagramWords f c v w (fun _ ↦ inferInstance) q).2.domain l E o
        (fun _ ↦ K.obj) :=
    integralFiniteTorRefinementDiagram l E D hl o S f c v w (fun _ ↦ inferInstance) K q
  exact (integralNormalizedRefinementPasting l E D hl o S f P.F P.r P.ρ P.e
    P.compatible P.transpose hnormalization.equation hDiagram).2.1

end OverProjection
end WeilConjectures.IntegralSystemRealization
