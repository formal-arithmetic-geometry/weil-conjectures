module

public import Sheaf.Paper.SystemCompactSupportRestrictionData

/-! # Open coefficient restriction coherence

Source: Stacks, sites-modules.tex, Tags 03DI and 03DJ, and the coefficient-composition
argument, step 4 (blueprint: lem-sp-system-open-restriction-coherence).

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- Section-normalized open comparisons on whole systems satisfy coefficient composition
and identity before finite evaluation.

Source: Stacks, sites-modules.tex, Tags 03DI and 03DJ, and the coefficient-composition
argument, step 4 (blueprint: lem-sp-system-open-restriction-coherence).

Proof: the constant coefficient maps commute with geometric pullback by naturality of
constant sheaves. The identity on sections constructs the ordinary push square; its
adjunction transpose is invertible: the two inverse-image functors have the same
underlying sheaf, and naturality identifies their transported scalar actions.
This gives each GeometricSquare, with its specified
mate normalization. On the site localized at the subterminal open, extension by zero is
the sheafification of the direct sum over maps into that open. There is either one such
map or none. Restriction preserves the original module in the first case and zero in
the second. The identity on these summands commutes with the horizontal coefficient
transitions, so it gives an ordinary system comparison. The summand adjunction proves
the displayed open-unit normalization. For two coefficient maps both comparison words
are the identity on each summand, with action through the composite coefficient map;
the section conditions on c identify their restriction associators. Sheafification
uniqueness gives their equality as whole-system maps. Exact localization preserves this
pasting equation and yields the stated derived cocycle. For an identity coefficient map
the same summand calculation gives the ordinary unitor equation, whose exact localization
is the displayed derived unit equation. Empty opens, identity opens and nonflat maps use
the same formula; no evaluation faithfulness is involved. -/
theorem systemOpenRestrictionCoherence (l : ℕ) [Fact l.Prime]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (c : RestrictionIdentifications.{u} l) :
    ∃ (g : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings), GeometricSquare a j)
      (o : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings), OpenComparison (g B C a)),
      (∀ (B C D : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings)
        (L : VaryingRing.Derived (levels D) (steps D) X),
        (VaryingRing.J (levels B) (steps B) j).map ((c.rho X a b).hom.app L) ≫
            (o B D (a ≫ b)).derived.hom.app L =
          (o B C a).derived.hom.app ((derivedRestriction X b).obj L) ≫
            (derivedRestriction Z a).map ((o C D b).derived.hom.app L) ≫
            (c.rho Z a b).hom.app ((VaryingRing.J (levels D) (steps D) j).obj L)) ∧
      (∀ (B : Etale.SystemProjection.Coefficients.{u} l)
        (L : VaryingRing.Derived (levels B) (steps B) X),
        (o B B (𝟙 B.rings)).derived.hom.app L ≫
            (c.derivedUnit Z B).hom.app ((VaryingRing.J (levels B) (steps B) j).obj L) =
          (VaryingRing.J (levels B) (steps B) j).map
            ((c.derivedUnit X B).hom.app L)) := by
  sorry

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
