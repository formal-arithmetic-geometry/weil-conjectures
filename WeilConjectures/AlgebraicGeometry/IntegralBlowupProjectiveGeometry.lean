/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleMorphism
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Complement
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Integrality and projectivity of an ordinary blowup

Source: Stacks Project, Divisors, Tags 02ND and 02NS(1)
(blueprint: lem-sfb-integral-blowup-projective-geometry).

The finite-type condition is expressed on every affine open, as in the node.
Projectivity uses the projective-bundle convention, allowing a quasi-coherent
finite-type module that need not be locally free.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The ordinary blowup of an integral scheme in a nonzero quasi-coherent finite-type
ideal is integral, and its structure morphism is projective in the projective-bundle sense.

Source: Stacks Project, Divisors, Tags 02ND and 02NS(1)
(blueprint: lem-sfb-integral-blowup-projective-geometry).

Proof:
1. Over a nonempty affine open V = Spec A, write I(V) = (f_0, ..., f_r).
   The global blowup restricts to the affine blowup Proj(Rees_A(I(V))), by
   def-nagata-global-blowup, def-nagata-global-blowup-local-model,
   def-nagata-global-blowup-glue-data, def-nagata-affine-blowup, and
   lem-weil-pbc-relative-glueing-affine-opens. By
   prop-nagata-affine-blowup-chart-cover and def-nagata-blowup-chart-ring,
   its charts are Spec A[I(V)/f_i]. The ideal I(V) is nonzero: a nonzero stalk
   embeds into the function field, so the ideal is nonzero at the generic point,
   which belongs to V. For a nonzero f_i, the chart ring embeds into A localized
   at f_i and is a domain (Stacks 052R); a zero f_i gives an empty chart.
2. The complement U of the ideal's zero locus contains the generic point and
   is a nonempty dense integral open. By thm-nagata-global-blowup-complement,
   its inverse image is isomorphic to U. It meets each nonempty chart in the
   dense basic open D(f_i). Hence it is dense in the blowup. The domain charts
   give reducedness; the dense irreducible open gives irreducibility and
   nonemptiness. Apply def-pc-integral-scheme.
3. The sheaf Rees algebra of def-nagata-sheaf-rees-algebra has degree n equal
   to I^n and degree zero equal to the structure sheaf. By
   lem-weil-pbc-quasi-coherent-symmetric-algebra and
   lem-weil-pbc-symmetric-algebra-graded, the degree-one inclusion induces the
   graded surjection Sym(I) onto Rees(I): on affines it sends a symmetric product
   to the product in I(V)^n, whose elements are sums of such products.
   Clause 1 of prop-nagata-relative-proj-functoriality identifies the relative
   Proj of the Rees algebra with the affine blowups on each affine open.
   Their transition maps are the same coefficientwise localizations, so
   lem-weil-pbc-relative-glueing-affine-opens identifies their glued scheme
   with the global blowup, over the base. Clause 3 of
   prop-nagata-relative-proj-functoriality turns the graded surjection into a
   closed immersion of the blowup into Proj(Sym(I)) = P(I). Finite type of I
   gives precisely def-trf-projective-bundle-morphism. -/
theorem isIntegral_blowup_and_isProjectiveBundle
    {T : Scheme.{u}} [IsIntegral T] (I : T.IdealSheafData)
    (hI : I ≠ ⊥) (hfinite : ∀ U : T.affineOpens, (I.ideal U).FG) :
    IsIntegral I.blowup ∧ IsProjectiveBundle I.blowupMap := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
