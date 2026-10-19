/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Complement
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Integrality and projectivity of an ordinary finite-type blowup

Source: Stacks Project, Divisors, Tags 02ND and 02NS(1)
(blueprint: lem-per-integral-blowup-projective-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A nonzero quasi-coherent finite-type ideal on an integral scheme has integral
ordinary blowup, whose structural morphism is projective in the projective-bundle sense.
Source: Stacks Project, Divisors, Tags 02ND and 02NS(1)
(blueprint: lem-per-integral-blowup-projective-geometry).

Proof:
1. Restrict the global gluing construction (def-nagata-global-blowup,
def-nagata-global-blowup-glue-data and def-nagata-global-blowup-local-model) to a
nonempty affine open Spec A, using lem-weil-pbc-relative-glueing-affine-opens. The local
model is def-nagata-affine-blowup. Finite type gives generators f_i of the ideal I.
By prop-nagata-affine-blowup-chart-cover its charts have rings A[I/f_i] from
def-nagata-blowup-chart-ring. Nonzero generators give subrings of A localized at f_i,
hence domains (Tag 052R); zero generators give empty charts. There is a nonzero generator:
a nonzero ideal sheaf on an integral scheme is nonzero at the generic point, since local
rings embed in the function field, and that point belongs to every nonempty affine open.
2. The center complement U is nonempty and dense. By thm-nagata-global-blowup-complement
the blowup over U is U itself. In each nonempty chart it contains the dense basic open
D(f_i). Thus this irreducible open is dense in the blowup. The domain charts make the
blowup reduced, and its dense irreducible open makes it irreducible. This is integrality
as in def-pc-integral-scheme.
3. Form the quasi-coherent sheaf Rees algebra (def-nagata-sheaf-rees-algebra). The
universal property in lem-weil-pbc-quasi-coherent-symmetric-algebra gives Sym(I) to Rees(I).
With lem-weil-pbc-symmetric-algebra-graded this is a graded surjection: on every affine
open its degree n part sends products of n ideal sections to their product in I^n,
and these products generate I^n. The affine restriction of def-nagata-relative-proj,
prop-nagata-relative-proj-functoriality clause 1 and uniqueness of relative gluing identify
its relative Proj with the ordinary blowup, with matching transition maps. Clause 3 of
prop-nagata-relative-proj-functoriality gives a closed immersion into P(I) over the base.
Since I is quasi-coherent of finite type, this is def-trf-projective-bundle-morphism.
-/
theorem integral_blowup_projectiveBundle
    {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral T]
    (I : T.IdealSheafData) (_hI : I ≠ ⊥)
    (_hft : I.toModules.IsQuasiCoherentFiniteType) :
    AlgebraicGeometry.IsIntegral I.blowup ∧ AlgebraicGeometry.IsProjectiveBundle I.blowupMap := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
