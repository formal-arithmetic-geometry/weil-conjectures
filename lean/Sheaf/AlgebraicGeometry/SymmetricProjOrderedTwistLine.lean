/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace

/-! # Existence of the ordered global twist line

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-line).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

/-- The local normalized affine comparisons glue to a global line isomorphism.

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-line).

Proof: on each affine base chart, use the supplied polynomial and normalized
Proj comparison to identify the standard degree-one frame with the chart frame
of the tautological quotient.  The ratio on overlaps is the ratio of the same
homogeneous generators, so the local isomorphisms satisfy the cocycle condition.
Glue them, together with their local inverses, by the sheaf gluing theorem.
The resulting global map is an isomorphism.  The argument also covers the
zero-dimensional and empty-chart cases.
-/
theorem exists_ordered_twist_line (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (hRel : eRel.hom ≫ RelativeProjectiveSpace.π S r =
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
    (hAffine : ∀ V : S.affineOpens,
      ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (hθ : θ.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
      RelativeProjectiveSpace.π S r)
    (hθAffine : ∀ V : S.affineOpens, RelativeProjectiveSpace.IsIntegralProjComparison
      S r V (RelativeProjectiveSpace.affineToIntegral S r θ V)) :
    ∃ t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line, True := by
  sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
