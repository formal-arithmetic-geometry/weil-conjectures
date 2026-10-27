/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace

/-! # Coordinate compatibility for the ordered twist line

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-coordinates).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

/-- The glued ordered twist line carries the prescribed coordinate quotients.

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-coordinates).

Proof: on every standard affine chart, the generator equation of the normalized
quotient identifies the basis quotient with the degree-one frame.  The supplied
integral Proj comparison sends the standard coordinate to that same generator.
Since morphisms from the unit module are local, the equality descends from the
standard charts and remains valid for all coordinates, including r = 0 and
empty charts.
-/
theorem ordered_twist_coordinate_compatibility (S : Scheme.{u}) (E : S.Modules)
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
      S r V (RelativeProjectiveSpace.affineToIntegral S r θ V))
    (t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line) :
    ∀ i : ULift.{u} (Fin (r + 1)),
      (Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
        (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
      ((Scheme.Modules.boundaryPullbackComparison
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
            (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
          (Scheme.Modules.unit _) ≪≫
        Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
      (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom := by
  sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
