import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.Separable
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension
import Sheaf.TraceFormula.SmoothSeparableHypersurfaceSlice
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Smooth fibre point admits an étale immersion slice

Source: Stacks Project, Tag 057G, lemma-slice-smooth.
(blueprint: lem-trf-smooth-point-etale-immersion)

The theorem records the existence of an immersed scheme through a closed smooth-fibre point
whose structural morphism is étale and whose fibre over the image point is a singleton.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A smooth morphism admits an étale immersion slice through a closed fibre point with
finite separable residue-field extension.  The proof follows Stacks Project, Tag 057G.
Step 1 bounds the fibre dimension using local finite presentation and affine finite type.
Step 2 handles dimension zero using an étale neighbourhood and an isolated fibre point.
Step 3 cuts by a smooth hypersurface and verifies the induction hypotheses.
(blueprint: lem-trf-smooth-point-etale-immersion)
Step 4 composes the resulting immersion with the closed-open immersion into X. -/
theorem Smooth.exists_etale_immersion_slice
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (hx : IsClosed {f.asFiber x})
    (h : letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (S.residueField (f x)) (X.residueField x) ∧
      Algebra.IsSeparable (S.residueField (f x)) (X.residueField x)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z), IsImmersion i ∧ i z = x ∧
      Etale (i ≫ f) ∧
      Set.range ((i ≫ f).fiberι (f x)) = Set.singleton z := by
  sorry

end AlgebraicGeometry
