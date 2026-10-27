module

public import Sheaf.Paper.SystemCompactSupportRestrictionData
import Sheaf.Paper.SystemProperRestrictionData
import Sheaf.Paper.SystemProperRestrictionLaws

/-! # Proper coefficient restriction coherence

Source: Stacks, sites-cohomology.tex, Tag 0D6E; derived.tex, Tag 070Y; and the
coefficient-composition argument, steps 2, 3 and 6
(blueprint: lem-sp-system-proper-restriction-coherence).

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

/-- The normalized proper comparisons on whole coefficient systems are coherent.

Source: Stacks, sites-cohomology.tex, Tag 0D6E; derived.tex, Tag 070Y; and the
coefficient-composition argument, steps 2, 3 and 6
(blueprint: lem-sp-system-proper-restriction-coherence).

Proof: naturality of constant sheaves gives the commuting structural ring square.
The identity on sections gives the ordinary direct-image comparison, and its inverse
adjunction mate gives the invertible inverse-image comparison, constructing g. On small
representatives of the two sequence sites, restriction is the direct image of the
identity-site ringed morphism with the given structural map. The two composites with p
are the same ringed morphism. Apply unbounded derived pushforward composition to both
factorizations, identifying the derived exact restriction with its termwise localization.
The ratio of the two composition comparisons constructs q. On a target-coefficient
K-injective H and a source-coefficient K-injective resolution v of its restriction,
the resolution equation for composition is precisely q.normalized: the image of v is
a quasi-isomorphism and the component is its inverse after the displayed quotient
identifications. To compose two coefficient maps, take a common K-injective resolution
of the successive restrictions; naturality and cancellation of the three invertible
resolution maps give the proper cocycle. Equivalently apply the normalized-derived-
comparison composition theorem in the identical-carrier model, then transport its exact
restriction comparisons to c using the identity section formulas. This never assumes
that a restriction preserves K-injectives. For the identity map choose the identity
resolution of each K-injective H. The normalization gives the unitor equation on QH.
Every derived object is isomorphic to such a QH; naturality and cancellation transport
the equation to every object. The same argument proves uniqueness of the normalized
comparison. All statements concern whole derived systems, including unbounded objects
and nonflat coefficient maps. -/
theorem systemProperRestrictionCoherence (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (c : RestrictionIdentifications.{u} l) :
    ∃ (g : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings), GeometricSquare a p)
      (q : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings), ProperComparison (g B C a)),
      (∀ (B C D : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings)
        (M : VaryingRing.Derived (levels D) (steps D) Z),
        (VaryingRing.P (levels B) (steps B) p).map ((c.rho Z a b).hom.app M) ≫
            (q B D (a ≫ b)).iso.hom.app M =
          (q B C a).iso.hom.app ((derivedRestriction Z b).obj M) ≫
            (derivedRestriction Y a).map ((q C D b).iso.hom.app M) ≫
            (c.rho Y a b).hom.app ((VaryingRing.P (levels D) (steps D) p).obj M)) ∧
      (∀ (B : Etale.SystemProjection.Coefficients.{u} l)
        (M : VaryingRing.Derived (levels B) (steps B) Z),
        (q B B (𝟙 B.rings)).iso.hom.app M ≫
            (c.derivedUnit Y B).hom.app ((VaryingRing.P (levels B) (steps B) p).obj M) =
          (VaryingRing.P (levels B) (steps B) p).map
            ((c.derivedUnit Z B).hom.app M)) := by
  obtain ⟨g, ⟨q⟩⟩ := systemProperRestrictionData l p c
  obtain ⟨hcomp, hunit⟩ := systemProperRestrictionLaws l p c g q
  exact ⟨g, q, hcomp, hunit⟩

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
