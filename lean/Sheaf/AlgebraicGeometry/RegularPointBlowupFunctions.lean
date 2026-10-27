/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Blowup.Gluing
import WeilConjectures.Blowup.Affine.Defs
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.FlatBaseChange
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularSequencePowers
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper

/-! # Regular functions under a regular point blowup

Source: Stacks Project, Resolution of Surfaces, Tag 0AGS, clause (4) at n = 0;
Cohomology of Schemes, Tag 02KH, and Divisors, Tags 0804 and 0805
(blueprint: lem-sfb-regular-point-blowup-functions).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blowing up a reduced closed point of a Noetherian regular scheme of dimension at most
two preserves its structure sheaf, provided the exceptional fibre is nonempty.
The centre is the vanishing ideal of the closed singleton, hence has the reduced induced
scheme structure. The natural transformation in the conclusion is the canonical map
O_T to b_* O_W. Its components are the pullback ring maps on every open, and its
naturality is precisely compatibility with restrictions; its inverse is natural as well.

Source: Stacks Project, Resolution of Surfaces, Tag 0AGS(4), n = 0, with flat base change
Tag 02KH; Divisors, Tags 0804 and 0805
(blueprint: lem-sfb-regular-point-blowup-functions).

Proof plan:
1. Choose a regular affine neighbourhood V = Spec R of x, with maximal ideal p.
   The glued local model and cover independence identify Y = b inverse V with the
   affine blowup of p over R (def-nagata-global-blowup-local-model,
   def-nagata-global-blowup-glue-data, prop-nagata-global-blowup-cover-independent).
   R is Noetherian, so p is finitely generated. By thm-nagata-global-blowup-proper,
   Y to V is proper, hence separated, of finite type and quasi-compact; it is
   quasi-separated by lem-pc-separated-quasi-separated. Put M = Gamma(Y, O_Y),
   with its R-algebra structure given by pullback.
2. For every multiplicative subset S of R, localization is flat
   (lem-weil-pbc-localization-flat, lem-weil-pbc-flat-ring-map-iff-flat-affine).
   Apply lem-pc-flat-base-change-cohom in degree zero to the quasi-coherent
   structure module. Its pullback is the structure module, via the local formula
   B tensor_B C to C, b tensor c maps to bc, with inverse c maps to 1 tensor c.
   The comparison M tensor_R S inverse R to Gamma(Y base-changed to S inverse R, O)
   sends m tensor a/s to (a/s)m, hence respects products and coefficients. Identify
   its source with S inverse M by m tensor a/s maps to am/s. All identifications
   commute with further localization.
3. Taking S to be powers of h gives Gamma(b inverse D(h), O) = M_h. The D(h)
   containing x form a neighbourhood basis (lem-weil-pbc-spec-localization-away-basic-open,
   lem-weil-pbc-principal-localization-open-immersion). Thus the stalk of b_* O at x
   is M_p: m/h^n maps to its fraction; every m/s is represented on D(s); a fraction
   vanishing at p is killed by some u outside p and vanishes after restricting to D(hu).
   The affine stalk identification gives A = O_{T,x} = R_p, and beta_x is the
   coefficient map A to M_p (lem-weil-pbc-affine-open-stalk-localization,
   def-weil-pbc-module-stalk).
4. Apply step 2 with S = R minus p. Blowup flat base change identifies the resulting
   scheme Z with the blowup of the maximal ideal m = pA over Spec A, respecting
   coefficients (def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-flat-base-change).
   Exchange fibre-product factors if necessary. The one-element affine cover and
   cover independence identify this global blowup with Proj of the Rees algebra,
   so the affine chart statements apply. Beta_x is now A to Gamma(Z, O_Z).
5. By def-weil-regular-scheme, A is regular local, and it is a domain by
   lem-sc-regular-local-domain. Its dimension is at most two: chains of primes in
   R_p contract strictly to chains in R, and the corresponding irreducible closed
   subsets of V have strict closures in T. This uses the localization definitions,
   lem-weil-pbc-spec-irreducible-closed-subsets-primes and the topological dimension
   bound. No equidimensionality or connectedness is required.
6. In dimension zero, m is zero. The single generator 0 gives a blowup chart with
   ring A[0/0], a subalgebra of the zero ring A_0, so Z is empty. Its closed fibre
   is the original fibre over x, contradicting the hypothesis. In dimension one,
   a generator t of m is a nonzerodivisor by
   lem-weil-pbc-regular-local-generators-regular-sequence. The single chart ring
   A[m/t] is A: every a/t with a = tc is c, and A embeds in A_t. The chart cover
   (prop-nagata-affine-blowup-chart-cover) gives the coefficient isomorphism.
7. In dimension two, choose regular parameters s,t. They form a regular sequence
   by lem-weil-pbc-regular-local-generators-regular-sequence and are nonzero.
   The two charts cover Z and have rings C_s = A[m/s] inside A_s and C_t = A[m/t]
   inside A_t (def-nagata-blowup-chart-ring, prop-nagata-affine-blowup-chart-cover).
8. These are the homogeneous opens D_+(sT) and D_+(tT). Their intersection in each
   chart inverts the other coordinate ratio. The maps to A_{st} send homogeneous
   fractions aT^n/(sT)^n to a/s^n, and similarly for t. The homogeneous-localization
   and chart maps (def-nagata-homogeneous-away-to-chart,
   def-nagata-affine-blowup-chart-map, prop-nagata-affine-blowup-chart) therefore
   identify the two restrictions. A global section has chart values with equal
   images in A_{st}.
9. Write these values a/s^r and b/t^q, with r,q positive. Since A is a domain,
   equality in A_{st} gives t^q a = s^r b. By lem-weil-pbc-regular-sequence-powers,
   t^q is a nonzerodivisor modulo s^r. Hence a = s^r e for some e in A;
   cancellation then gives b = t^q e. The chart rings embed in their ambient
   localizations, so both chart sections equal the coefficient e.
10. Sheaf uniqueness on the two charts makes the global section the pullback of e.
    This proves surjectivity. A coefficient vanishing on Z vanishes in A_s and is
    zero by the domain property and s nonzero, proving injectivity. Thus the
    canonical coefficient map is a ring isomorphism in every permitted dimension.
11. This proves beta_x invertible. Off x, thm-nagata-global-blowup-complement gives
    invertibility on every stalk. Stalk injectivity gives injectivity on sections
    by sheaf uniqueness. Stalk surjectivity gives neighbourhood preimages of any
    section; shrink to equality of their images, use injectivity on overlaps,
    then glue. Thus every beta_U is a ring isomorphism. Naturality follows from
    def-weil-locally-ringed-space-morphism, and cancellation in its naturality
    squares gives naturality of the inverses, proving the sheaf isomorphism. -/
theorem isIso_structureSheafMap_point_blowup
    (T : Scheme.{u}) [CompactSpace T] (hregular : IsRegularScheme T)
    (hdim : topologicalKrullDim T ≤ 2) (x : T) (hx : IsClosed ({x} : Set T))
    (hfibre : Set.Nonempty
      ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap ⁻¹' {x})) :
    IsIso (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap.toLRSHom.toHom.c := by
  sorry

end AlgebraicGeometry
