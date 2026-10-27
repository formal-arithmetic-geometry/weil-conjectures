/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry
import Sheaf.AlgebraicGeometry.SurfaceRationalMapPointResolution
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import Sheaf.AlgebraicGeometry.PointBlowdownFactorization

/-!
# Point-blowup factorization of proper birational surface morphisms

Source: Stacks Project, Resolution of Surfaces, Tag 0C5R,
`lemma-proper-birational-regular-surfaces`
(blueprint: lem-sfb-proper-birational-surface-factorization).

The finite tower is the existing `OrdinaryBlowupTower`; its centers are the
vanishing ideals of closed singletons, giving their reduced scheme structures.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper birational morphism between integral regular Noetherian surfaces is a
finite composition of blowups of reduced closed points, up to isomorphism over its
target. A length-zero tower represents an isomorphism.

Source: Stacks Project, Resolution of Surfaces, Tag 0C5R,
`lemma-proper-birational-regular-surfaces`
(blueprint: lem-sfb-proper-birational-surface-factorization).

Proof plan:
1. By lem-sfb-exceptional-curve-count, the set B(f) of contracted curves is finite
   and is empty exactly when f is an isomorphism. Induct strongly on its cardinality.
   If it is empty, use the length-zero tower. Otherwise choose a closed point y
   outside the maximal isomorphism open; its local dimension is two.
2. Blow up the reduced point y. By lem-sfb-regular-point-blowup-geometry the new
   target Y' is integral, regular and Noetherian, and its blowup map b is proper
   and an isomorphism off y. Its closed dense image makes b surjective. The local
   dimension bound, with equality at a closed point above y, gives dimension two
   by def-kun-topological-krull-dimension.
3. Over the dense open X minus f inverse y, the inverse of b defines a rational
   lift. Apply lem-sfb-surface-rational-map-point-resolution to obtain a tower
   over X with centers over y and a map h from its top to Y'. Choose minimum
   length. Properness of blowups and composition (lemma-nagata-blowup-proper,
   lem-weil-pbc-proper-composition) and their complement isomorphisms
   (thm-nagata-global-blowup-complement) make the partial composites proper,
   birational and surjective. The map h is proper by
   lemma-nagata-proper-to-separated-target and birational on the common dense open.
4. If the source tower has positive length, let a be its final point blowup and
   E its exceptional fibre. Properness and the complement isomorphism make a
   surjective, so E is nonempty. The identity b h = f p induces E to F, the
   exceptional fibre of b. If its image has more than one point,
   lem-sfb-point-exceptional-isomorphism-neighbourhood gives h inverse F = E.
   Surjectivity of the partial composites then makes f inverse y a singleton.
5. By rem-pc-regular-normal, Y is normal. Integrality makes X reduced, and the
   dense-open isomorphism gives the generic-point and stalk isomorphisms needed
   by lem-sfb-normal-modification-codimension-one. Its finite-fibre clause puts
   y in the isomorphism open, a contradiction. Thus h(E) is one point.
6. By lem-sfb-point-blowdown-factorization, h descends uniquely across a.
   Uniqueness also makes the descended map a Y-morphism. This contradicts
   minimality of the source tower, so it has length zero and gives a lift g:X to Y'.
7. The lift g is proper by lemma-nagata-proper-to-separated-target and birational
   on the common dense open. By lem-sfb-exceptional-curve-count, B(g) is a proper
   subset of B(f). Apply induction to g and append b. Transport the resulting
   tower's top along its isomorphism over Y, giving the stated equality with f.
-/
theorem exists_point_blowup_factorization_of_proper_birational
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
    (hX : IsRegularScheme X) (hY : IsRegularScheme Y)
    (hdimX : topologicalKrullDim X = 2) (hdimY : topologicalKrullDim Y = 2)
    (f : X ⟶ Y) [IsProper f]
    (hbirational : ∃ (V : X.Opens) (U : Y.Opens),
      Dense (V : Set X) ∧ Dense (U : Set Y) ∧
      ∃ e : V.toScheme ≅ U.toScheme, V.ι ≫ f = e.hom ≫ U.ι) :
    ∃ (A : OrdinaryBlowupTower Y) (e : X ≅ A.level (Fin.last A.length)),
      e.hom ≫ A.toBase (Fin.last A.length) = f ∧
      ∀ i : Fin A.length, ∃ (p : A.level i.castSucc) (hp : IsClosed ({p} : Set _)),
        A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ := by
  sorry

end AlgebraicGeometry
