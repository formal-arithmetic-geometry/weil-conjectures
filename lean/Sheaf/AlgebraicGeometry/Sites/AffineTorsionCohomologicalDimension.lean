module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.AlgebraicGeometry.TorsionFilteredUnion
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Affine torsion cohomological dimension bound

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-sc-affine-torsion-cd`, affine part of the proof of
`thm-sc-finite-type-torsion-cd` (blueprint: thm-sc-affine-torsion-cd).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The affine finite-type step in the torsion cohomological-dimension bound.

Source: the affine bound `thm-sc-affine-torsion-cd` in the blueprint subsection
`sec-smooth-purity/sk-prop-sf-cbc`, with its proof by induction on dimension; also
Stacks Project, Tag 0F0V (https://stacks.math.columbia.edu/tag/0F0V).

Proof: the cited affine theorem gives torsion cohomological dimension at most
`dim X + c` for a nonempty affine finite-type scheme. Its finite-type hypothesis
is exactly local finite type together with quasi-compactness of the structure
morphism. Noether normalization makes the Krull dimension finite. The bound
`hX` makes that dimension at most `d`, so `q > d + c` implies `q > dim X + c`
and the cited theorem gives the required vanishing. If X is empty, every object
of its small etale site is empty, the empty covering forces every abelian sheaf
to have zero sections, and hence its section functor and all its derived
functors vanish. Thus this case also satisfies the displayed bound. Torsion here
means locally torsion sections, as in the cited theorem, without a uniform
annihilator. No affine theorem is currently available as a Lean declaration;
this statement records precisely this affine stage, rather than the global bound.
(blueprint: new-thm-sc-affine-torsion-cd-bound)
-/
theorem subsingleton_H_of_two_mul_add_lt_of_isAffine {K : Type u} [Field K] (c d : ℕ)
    (hK : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    [IsAffine X] (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : d + c < q) : Subsingleton (Sheaf.H F q) := by
  sorry

end AlgebraicGeometry.Scheme
