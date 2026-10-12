module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed

/-!
# Integral covers with trivial étale cohomology

Source: Stacks Project, Lemma 09ZD (label `lemma-integral-cover-trivial-cohomology`),
part (1), etale-cohomology.tex line 14467
(blueprint: lem-weil-pbc-integral-cover-trivial-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- An affine scheme admits an integral surjective cover whose closed subschemes have
vanishing positive-degree étale cohomology with finite constant coefficients.  The
proof follows Stacks Lemma 09ZD(1): construct the cover from the integral closure of a
polynomial presentation in an algebraic closure of its fraction field, then apply
Lemma 09ZC to closed subschemes. (blueprint: lem-weil-pbc-integral-cover-trivial-cohomology)

Proof steps: the polynomial presentation and integral-closure construction use
`def-weil-affine-spectrum`, `lem-weil-pbc-polynomial-ring-domain`,
`def-weil-algebraic-closure`, and `lem-weil-pbc-integral-closure-algebraic-extension-normal`;
integrality uses `lem-weil-pbc-spec-integral-ring-map-integral`; surjectivity uses
`pqf-lem-lying-over`; and the vanishing assertion uses
`lem-weil-pbc-gabber-absolutely-algebraically-closed`, together with the stated
closed-immersion, constant-sheaf, and étale-cohomology notions.
-/
theorem exists_integral_cover_trivial_cohomology (X : Scheme.{u}) [IsAffine X] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X),
      IsIntegralHom π ∧ Surjective π ∧
      ∀ (Z' : Scheme.{u}) (i : Z' ⟶ X') [IsClosedImmersion i],
        ∀ (M : Type (u + 1)) [AddCommGroup M] [Finite M] (q : ℤ),
          1 ≤ q →
            IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} Z' q).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                  (AddCommGrpCat.of M)))) := by
  sorry

end AlgebraicGeometry
