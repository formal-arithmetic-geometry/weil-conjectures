/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Affine.ChartAlgebra
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Reducedness and finite type of a Noetherian blowup

Source: Stacks Project, Divisors, Tags 0808 and 02NS; Morphisms, Tag 01T6;
Properties, Tag 01OV (blueprint: lem-per-reduced-noetherian-blowup-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The ordinary blowup of a coherent quasi-coherent ideal on a reduced Noetherian scheme
is of finite type, reduced and Noetherian. `IsNoetherian` is equivalent to the existence
of a finite affine cover by spectra of Noetherian rings. No condition on the support of
the ideal is imposed; the zero ideal, unit ideal and empty scheme are included.

Source: Stacks Project, Divisors, Tags 0808 and 02NS; Algebra, Tag 052S;
Morphisms, Tag 01T6; Properties, Tag 01OV
(blueprint: lem-per-reduced-noetherian-blowup-geometry).

Proof:
1. Coherence implies finite type (pqf-def-coherent). Apply lemma-nagata-blowup-proper;
   properness includes local finite type and implies quasi-compactness
   (def-weil-proper-morphism), hence the blowup map is of finite type.
2. The finite Noetherian affine cover makes X locally Noetherian (pqf-def-locnoeth).
   Affines are quasi-compact (lem-weil-pbc-affine-scheme-qcqs), so a finite union of
   these is quasi-compact. Apply lem-weil-pbc-finite-type-over-noetherian to the blowup
   map. Its source is locally Noetherian and quasi-compact; a finite subcover of its
   Noetherian affine cover gives precisely the stated Noetherian convention.
3. Use the given finite affine cover in def-nagata-global-blowup and its glue data and
   local model (def-nagata-global-blowup-glue-data, def-nagata-global-blowup-local-model).
   The gluing embeddings cover (lem-weil-pbc-glue-schemes), and
   prop-nagata-global-blowup-cover-independent identifies this presentation with W.
   Each affine ideal is finitely generated (def-weil-pbc-noetherian-ring).
   The charts Spec A[I/a] cover by prop-nagata-affine-blowup-chart-cover; for I = 0
   one may use the single generator 0.
4. Each base ring A is reduced (def-pc-reduced-scheme). For c = x/a^n in A[I/a]
   (def-nagata-blowup-chart-ring), c^m = 0 with m positive gives a^N*x^m = 0
   (def-weil-ring-localization-away). Choose e with e*m at least N. Then
   (a^e*x)^m = 0, hence a^e*x = 0 by reducedness of A, and c = 0 by localization.
   This works for zero divisors without cancellation.
5. Each chart is reduced by lem-weil-pbc-affine-scheme-reduced-iff. Every stalk of W
   is a stalk of an open chart, hence reduced. Apply def-pc-reduced-scheme.
6. For I = 0 all charts are spectra of the zero ring, so W is empty. For I = A the
   chart at 1 is Spec A, with identity structure map. An empty base gives an empty
   blowup. Zero rings and reduced rings with several components require no exception.
-/
theorem reducedNoetherian_blowup_geometry (X : Scheme.{u}) [IsReduced X] [IsNoetherian X]
    (J : X.IdealSheafData) (hJ : RingedSpace.IsCoherent X.toRingedSpace J.toModules) :
    (LocallyOfFiniteType J.blowupMap ∧ QuasiCompact J.blowupMap) ∧
      IsReduced J.blowup ∧ IsNoetherian J.blowup := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
