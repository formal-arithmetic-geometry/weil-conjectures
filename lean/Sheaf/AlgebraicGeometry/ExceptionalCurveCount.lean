/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Blowup.Gluing
import Mathlib.Topology.Sober
import Mathlib.Topology.NoetherianSpace
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.AlgebraicGeometry.LocalSurfaceMaximalBlowupGeometry
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry

/-!
# The finite exceptional-curve induction measure

Source: Stacks Project, Resolution of Surfaces, Tag 0C5R,
`lemma-proper-birational-regular-surfaces`, first proof paragraph
(blueprint: lem-sfb-exceptional-curve-count).

The two definitions spell out the union of isomorphism opens and the set B(f)
introduced in this node. Curves are subsets of the source, so strict containment
compares the very same curves before and after a target point blowup.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The union of all target opens over which the entire morphism is an isomorphism.
Source: Stacks Project, Tag 0C5R, first proof paragraph
(blueprint: lem-sfb-exceptional-curve-count). -/
noncomputable def Scheme.Hom.isomorphismOpen {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Opens :=
  sSup {U : Y.Opens | IsIso (f ∣_ U)}

/-- B(f): the irreducible closed one-dimensional subsets of the source contracted
by f to a single point. Dimension is that of the subspace, and the image is an
actual singleton, with no rationality condition on the point.
Source: Stacks Project, Tag 0C5R, first proof paragraph, the curves in fibres
(blueprint: lem-sfb-exceptional-curve-count). -/
noncomputable def Scheme.Hom.exceptionalCurves {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set (Set X) :=
  {C | IsClosed C ∧ IsIrreducible C ∧ topologicalKrullDim C = 1 ∧
    ∃ y : Y, f '' C = {y}}

/-- The bad-point set and contracted-curve set of a proper birational morphism of
integral regular Noetherian surfaces are finite. Every bad point is closed of local
dimension two, the curve set is empty exactly for an isomorphism, and factoring
through the blowup of a bad reduced point strictly decreases that set.

Source: Stacks Project, Tag 0C5R, `lemma-proper-birational-regular-surfaces`,
first proof paragraph (blueprint: lem-sfb-exceptional-curve-count).

Proof:
1. Integrality and scheme sobriety (def-pc-integral-scheme, lem-sc-scheme-sober)
identify the generic points and their stalks on the given dense-open isomorphism.
Apply lem-sfb-normal-modification-codimension-one. Regular local rings of dimension
one are DVRs (lem-sc-regular-dim1-dvr); regular rings are normal
(rem-pc-regular-normal). Thus points outside the isomorphism open have local
dimension two, since lem-sc-scheme-stalk-dimension-generalization-chains bounds
local dimensions by the surface dimension (def-kun-topological-krull-dimension).
2. The bad set S is closed. A strict specialization of a local-dimension-two point
would extend a generalization chain to length three, impossible on a surface.
Sobriety distinguishes the point closures. Hence every point of S is closed;
lem-sc-noetherian-closed-points-finite makes S finite, including when it is empty.
3. Z = f inverse-image S is a proper closed subset, missing the generic point.
By lem-sc-noetherian-closed-subset-finite-components it has finitely many closed
irreducible components D_i. Each has dimension at most one: a length-two chain
inside a proper component, followed by X, contradicts dimension two. Its image is
irreducible in a finite set of closed points, hence a singleton. Every component
of dimension one therefore belongs to B(f).
4. Conversely a contracted curve cannot lie above the isomorphism open: a fibre
there is a singleton. Such a curve lies in Z, hence in a component D_i by the finite
component cover and irreducibility. Strict inclusion would extend a length-one
chain inside the curve first by D_i and then by X, contradicting dimension two.
Thus B(f) is precisely the finite set of one-dimensional components of Z.
5. If B(f) is empty, all these components have dimension zero. By sobriety their
generic points are unique; any other point would give a proper nonempty closed
irreducible subset and a length-one chain. The components are therefore singletons,
so all fibres over S are finite. Normality and clause (3) of
lem-sfb-normal-modification-codimension-one put S in the isomorphism open. Thus S
is empty and f is an isomorphism. The converse follows from singleton fibres.
6. For f = b composed with g, every curve contracted by g is contracted by f.
7. Localize Y at y. The canonical Spec of the local ring map is flat and is the
identity on the closed stalk (lem-weil-pbc-spec-local-ring-canonical-morphism).
The reduced point pulls back to the maximal ideal. The maps of
def-nagata-blowup-flat-base-change-map and thm-nagata-blowup-flat-base-change
identify the fibre of b with that of this local maximal-ideal blowup, hence with
the projective line over the residue field by lem-sfb-local-surface-maximal-blowup-geometry.
Its underlying closed subset is b inverse-image {y} (def-pc-scheme-fibre).
8. The two domain polynomial charts of def-sc-p1-standard have nonempty overlap,
so this projective line is irreducible. The primes (0) and (t) show it has more
than one point over any residue field. Its underlying subset E is proper in Y':
the complement isomorphism in lem-sfb-regular-point-blowup-geometry preserves the
generic point, which does not map to the closed point y.
9. Proper birational g has closed dense image, hence is surjective. Its inverse
image of E is proper closed and has finitely many components. Their closed images
cover E, so irreducibility makes one image all of E. That component has dimension
at most one by the surface chain argument, and cannot have dimension zero since
sobriety would make it a singleton. It is consequently a curve contracted by f
but not by g. Together with step 6 this proves strict containment.
-/
theorem exceptional_curve_count_of_proper_birational
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
    (hX : IsRegularScheme X) (hY : IsRegularScheme Y)
    (hdimX : topologicalKrullDim X = 2) (hdimY : topologicalKrullDim Y = 2)
    (f : X ⟶ Y) [IsProper f]
    (hbirational : ∃ (V : X.Opens) (U : Y.Opens),
      Dense (V : Set X) ∧ Dense (U : Set Y) ∧
      ∃ e : V.toScheme ≅ U.toScheme, V.ι ≫ f = e.hom ≫ U.ι) :
    ((f.isomorphismOpen : Set Y)ᶜ).Finite ∧
    (∀ y : Y, y ∉ f.isomorphismOpen →
      IsClosed ({y} : Set Y) ∧ ringKrullDim (Y.presheaf.stalk y) = 2) ∧
    f.exceptionalCurves.Finite ∧
    (f.exceptionalCurves = ∅ ↔ IsIso f) ∧
    ∀ (y : Y), y ∉ f.isomorphismOpen → ∀ (hy : IsClosed ({y} : Set Y))
      (g : X ⟶ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup),
      IsProper g →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup →
      IsRegularScheme (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup →
      IsNoetherian (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup →
      topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup = 2 →
      (∃ (V : X.Opens)
        (U : (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup.Opens),
        Dense (V : Set X) ∧
        Dense (U : Set (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup) ∧
        ∃ e : V.toScheme ≅ U.toScheme, V.ι ≫ g = e.hom ≫ U.ι) →
      g ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowupMap = f →
      g.exceptionalCurves ⊂ f.exceptionalCurves := by
  sorry

end AlgebraicGeometry
