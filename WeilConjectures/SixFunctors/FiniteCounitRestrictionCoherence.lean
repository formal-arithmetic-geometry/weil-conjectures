/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteCounitRestrictionData

/-! # Identity and composition of the finite restriction transitions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteCounitRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [hsep : IsSeparated (X ↘ Spec (.of D.k))]
  (c : Compactification (X ↘ Spec (.of D.k)))

include hft hqc hsep

/-- The sheaf transitions d and v respect the canonical restriction unit and compositor;
applying integral restriction and point sections also makes the d transitions coherent.
Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2,
final sentences, expanded in step 6 of lem-coef-finite-counit-restriction-square
(blueprint: lem-coef-finite-counit-restriction-coherence).

Proof: first work on the ordinary etale categories at the retained compactification c.
The counit-defined exceptional comparisons satisfy the unit and quotient cocycle of
lem-coef-finite-dualizing. For a different compactification these equations transport
through the canonical compact-support comparison and its counit equation. Naturality
and the successive-quotient identity for the compact-support coefficient comparison
therefore give the unit and cocycle for b = F(u)c. Transpose these identities through
the scalar adjunctions: naturality of their units identifies the iterated transpose
with the transpose for the composite quotient, using the canonical restriction
compositor. Transport by valueOrigin and pbcDerivedComparisonRestrict; naturality
cancels the intermediate origin isomorphisms and yields the first and third clauses.
The same argument on the regular coefficient object, where the scalar unit is
multiplication, gives the second and fourth clauses for v. Finally restrict all
finite coefficients to the integral ring. The two ways to compose restriction
compositors agree, since both are induced by the identity on underlying sections.
The identity compositor likewise agrees with restrictionUnit. Thus applying the
same exact point-sections functor to d gives its displayed identity and composition
in D(R). All scalar maps are the actual quotients, so this also covers equal levels
and nonflat quotients; no strict tower or arbitrary representative is chosen. -/
theorem restriction_coherence (hl : l ≠ D.p) :
    (∀ n : ℕ,
      transition l E D X c (le_refl n) ≫
        (restrictionUnit l E D n).hom.app (value l E D X c n) = 𝟙 _) ∧
    (∀ n : ℕ,
      unitTransition l E D (le_refl n) ≫
        (restrictionUnit l E D n).hom.app (𝟙_ _) = 𝟙 _) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      transition l E D X c (hmn.trans hrm) ≫
        (restrictionComp l E D hrm hmn).inv.app (value l E D X c n) =
      transition l E D X c hrm ≫
        (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
          (finiteDualizingQuotient l E hrm)).map (transition l E D X c hmn)) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      unitTransition l E D (hmn.trans hrm) ≫
        (restrictionComp l E D hrm hmn).inv.app (𝟙_ _) =
      unitTransition l E D hrm ≫
        (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
          (finiteDualizingQuotient l E hrm)).map (unitTransition l E D hmn)) ∧
    (∀ n : ℕ, sectionTransition l E D X c (le_refl n) = 𝟙 _) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
        sectionTransition l E D X c (hmn.trans hrm) =
          sectionTransition l E D X c hrm ≫ sectionTransition l E D X c hmn) := by
  sorry

end WeilConjectures.FiniteCounitRestriction
