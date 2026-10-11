import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.Paper.PQFCohomology

/-! # Serre's quasi-compact vanishing criterion

Source: Stacks Project, Cohomology of Schemes, Lemma Tag 01XF
(blueprint: lem-pqf-quasicompact-h1-zero).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A quasi-compact scheme whose first cohomology vanishes on every
quasi-coherent ideal sheaf is affine.

Source: Stacks Project, Cohomology of Schemes, Lemma Tag 01XF, lines 283--388
(blueprint: lem-pqf-quasicompact-h1-zero).

Proof: (1) For a closed point `x`, choose an affine neighbourhood `U` and
the reduced closed subschemes on `X \ U` and `(X \ U) ∪ {x}`.  Their ideal
sheaves have quotient restricting to the residue field at `x` and supported
at `x`; the long exact sequence and the H¹ hypothesis lift its unit to a
global section whose principal open is an affine neighbourhood of `x`.
(2) The union of affine principal opens contains every closed point.  A
quasi-compact scheme is Kolmogorov, so a nonempty complement would contain a
closed point; hence finitely many such principal opens cover `X`.
(3) The sections defining this cover give a surjection from a finite free
module sheaf to `\mathcal O_X`.  Filter its kernel by the summands.  Each
successive quotient is a quasi-coherent ideal, so induction with the long
exact sequence gives H¹-vanishing for the kernel.
(4) The long exact sequence then makes the corresponding global sections
generate the unit ideal of `Γ(X, \mathcal O_X)`.
(5) The affine basic-open unit-ideal criterion applied to this finite cover
concludes that `X` is affine.  The proof uses
`lem-weil-pbc-reduced-induced-closed-subscheme`,
`lem-sc-quasi-compact-kolmogorov-closed-point`,
`lem-weil-pbc-derived-functor-long-exact`, and
`lem-weil-pbc-affine-unit-ideal-basic-opens`.
-/
theorem quasiCompact_affine_of_h1_ideal_zero (X : Scheme.{u})
    [QuasiCompact (𝟙 X)]
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)) :
    IsAffine X := by
  sorry

end AlgebraicGeometry
