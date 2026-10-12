module

public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Passage from positive-integer annihilated sheaves to torsion sheaves.
Source: Stacks Project, Tag 0A4B, proof, filtered-colimit reduction, transposed to
global cohomology using Tag 03Q5 (the constant-scheme case of Theorem 09YQ).
See https://stacks.math.columbia.edu/tag/0A4B and
https://stacks.math.columbia.edu/tag/03Q5.
(blueprint: lem-weil-pbc-pullback-iso-torsion-colimit)

Proof: Index the kernels F[n] of multiplication by positive n by divisibility.
This is a nonempty filtered poset: 1 is an object and nm bounds n and m. The
kernel equation and cancellation of its inclusion show n times its identity is
zero. The torsion hypothesis says the cocone of these inclusions with vertex F
is a colimit cocone. Inverse image preserves it, since it is a left adjoint.
Cohomology on each qcqs scheme preserves these filtered colimit cocones (Tag
03Q5); the natural Ext-to-derived comparison gives the same fact for Sheaf.H.
Naturality of cohomologyMap makes the stagewise pullback maps a natural
transformation between the cohomology diagrams. The bounded-torsion hypothesis
makes every component bijective. Their inverses also commute with transitions,
by composing the naturality square with the inverse maps. Thus the induced
map of colimits is invertible. Naturality with the kernel inclusions identifies
that map with cohomologyMap u F q, so the latter is bijective for every q.
This also covers F = 0 and q = 0. -/
theorem pullback_cohomology_bijective_of_torsion_colimit
    {X Y : Scheme.{u}} (u : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hbounded : ∀ (n : ℕ), 0 < n →
      ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        n • 𝟙 G = 0 → ∀ (q : ℕ),
          Function.Bijective (cohomologyMap u G q))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) :
    ∀ (q : ℕ), Function.Bijective (cohomologyMap u F q) := by
  sorry

end AlgebraicGeometry.Etale
