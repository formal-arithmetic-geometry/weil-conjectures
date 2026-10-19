/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.InvertibleSectionRing
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree
import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
import Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Degree one on a genus-zero proper curve

Source: Stacks Project, `curves.tex`, Tag 0C6T, lemma-genus-zero-positive-degree,
with degree `d = 1` (the image in the projective line is the whole line).
(blueprint: lem-trf-pointed-genus-zero-projective-line)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper integral curve with trivial structure cohomology and a degree-one invertible
module is the projective line over its field.

Source: Stacks Project, `curves.tex`, Tag 0C6T, lemma-genus-zero-positive-degree,
with degree `d = 1`.
(blueprint: lem-trf-pointed-genus-zero-projective-line)

Proof plan. The curve is Noetherian of topological dimension one, so coherent cohomology
is finite-dimensional and vanishes above degree one. Euler characteristic gives two
independent sections of the degree-one module. A nonzero section has a zero scheme of
 dimension zero, and the associated cokernel has one-dimensional global sections and
 no higher cohomology. A generator lifts to a second section, and induction gives the
 binary monomial basis in every tensor power. The resulting section ring is the graded
 polynomial ring in two variables. The canonical Proj map is an open immersion into
 `ProjectiveLine (Spec k)`; properness makes its image closed, and irreducibility of
 the two standard charts makes the image the whole projective line. -/
theorem isProjectiveLine_of_genus_zero_degree_one (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsIntegralCurve (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))]
    (h₀ : Function.Bijective (Scheme.globalSectionsRingHom k (X := C)))
    (h₁ : Subsingleton ((RingedSpace.moduleCohomology C.toRingedSpace 1).obj
      (Scheme.Modules.unit C)))
    (M : C.Modules) [M.IsInvertible]
    (hdeg : Scheme.Modules.degree k M = 1) :
    Nonempty (Over.mk (C ↘ Spec (.of k)) ≅
      Over.mk (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) := by
  sorry

end AlgebraicGeometry
