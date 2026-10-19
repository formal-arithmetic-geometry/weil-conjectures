/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Compactification.StrictTransform
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.CurveIntersectionBlowupDecrease
import Sheaf.AlgebraicGeometry.SurfaceCodimensionOneCartierPart
import Sheaf.AlgebraicGeometry.SurfaceCurveRegularizationByBlowups
import Sheaf.AlgebraicGeometry.SurfacePointBlowupGeometry
import Sheaf.AlgebraicGeometry.SurfacePointIdealPrincipalization

/-!
# Embedded SNC resolution on a regular excellent surface

Source: Stacks Project, Resolution of Surfaces, Tag 0BIC, with Tags 0BIB, 0AHH,
0BI4, 0BI5 and 0BI7 (blueprint: lem-per-embedded-surface-curve-resolution).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A proper closed subscheme of an integral regular excellent Noetherian surface with
an ample invertible module becomes Cartier with strict normal crossings reduced support
after finitely many blowups at reduced closed points of its successive inverse images.
Every intermediate scheme is regular. The composite is H-projective and an isomorphism
away from finitely many closed points of the original closed subscheme.

The closed subscheme is encoded by its quasi-coherent ideal `Z`; properness is `Z ≠ ⊥`.
The tower retains each ideal and its actual blowup, obtained by gluing affine Rees Proj
schemes. Strict normal crossings uses the regular-intersection criterion of ILO VIII
4.2.2(i), equivalent on a regular surface to local products of distinct regular parameters.
In particular components have codimension one, can have dimension zero, and at most two
pass through any point. Length zero and the empty divisor are permitted.

Source: Stacks Project, Tag 0BIC (blueprint: lem-per-embedded-surface-curve-resolution).

Proof plan, following the eight steps of the node:
1. Factor the ideal of Z into an effective Cartier ideal and an ideal supported on a
   finite set of codimension-two closed points, by
   lem-per-surface-codimension-one-cartier-part. Unit ideals cover the empty case.
2. Principalize the latter by lem-per-surface-point-ideal-principalization. The point
   blowup geometry lemma preserves integral regular excellent Noetherian surfaces and
   ampleness. Cartier total transform preserves the first factor; the product of their
   nonzerodivisor generators makes the total transform effective Cartier thereafter.
3. There are finitely many reduced components. Regular local UFD factorization makes
   them codimension one. Zero-dimensional components are already regular and disjoint
   from the others. Excellence gives finite normalization for dimension-one components;
   lem-per-surface-curve-regularization-by-blowups regularizes their strict transforms.
4. A later point blowup preserves a previously regular curve by
   lem-per-surface-curve-intersection-blowup-decrease, or by the complement isomorphism
   if it misses the curve. Exceptional components are regular projective lines. Thus
   all components of the Cartier total transform are eventually regular.
5. Intersections of distinct curves form a finite set. Decrease lexicographically the
   maximum intersection multiplicity and the number of incidences attaining it, using
   lem-per-surface-curve-intersection-blowup-decrease. New exceptional intersections
   have multiplicity one, so finitely many blowups make all intersections transverse.
6. Blow up each point on at least three components. Old branches separate above it,
   since a remaining intersection would have positive multiplicity less than one.
   Their intersections with the exceptional curve are distinct and transverse. The
   number of points on three or more components strictly decreases.
7. At one branch lift a parameter from the regular quotient local ring; together with
   its prime local equation it generates the ambient maximal ideal. At two branches,
   intersection length one says their equations generate the maximal ideal. UFD
   factorization identifies the reduced union ideal with their product. These are the
   local regular parameter and regular-intersection descriptions of strict crossings.
8. All chosen centres are in the current inverse image of Z. Each point blowup is
   H-projective, and ampleness persists, so H-projective composition applies. Proper
   closedness makes the images of the finitely many centres closed points of Z. The
   blowup-complement isomorphisms compose to the isomorphism off this finite set. -/
theorem exists_embedded_surface_curve_resolution
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hRegular : IsRegularScheme X)
    (hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hDim : topologicalKrullDim X = 2)
    (hAmple : ∃ (L : X.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple X L hL)
    (Z : X.IdealSheafData) (hZ : Z ≠ ⊥) :
    ∃ A : OrdinaryBlowupTower X,
      (∀ i : Fin (A.length + 1), IsRegularScheme (A.level i)) ∧
      (∀ i : Fin A.length, ∃ p : A.level i.castSucc,
        IsClosed ({p} : Set (A.level i.castSucc)) ∧
          (A.center i).radical = A.center i ∧
          ((A.center i).support : Set (A.level i.castSucc)) = {p} ∧
          p ∈ (Z.comap (A.toBase i.castSucc)).support) ∧
      (Z.comap (A.toBase (Fin.last A.length))).IsInvertible ∧
      IsStrictNormalCrossingsBoundary (Z.comap (A.toBase (Fin.last A.length))).radical ∧
      IsHProjective (A.toBase (Fin.last A.length)) ∧
      ∃ F : Closeds X, Set.Finite (F : Set X) ∧
        (∀ x ∈ F, IsClosed ({x} : Set X)) ∧
        (F : Set X) ⊆ Z.support ∧
        IsIso ((A.toBase (Fin.last A.length)) ∣_ F.compl) := by
  sorry

end AlgebraicGeometry
