module

public import Sheaf.AlgebraicGeometry.SurfacePointBlowupData
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Topology.NoetherianSpace
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import Sheaf.AlgebraicGeometry.LocalSurfaceMaximalBlowupGeometry
import Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup
import Sheaf.AlgebraicGeometry.SmoothSectionAffineCoordinates
import Sheaf.FieldTheory.FiniteInseparableElement
import Sheaf.FieldTheory.InseparableTensorNilpotent
import Sheaf.RingTheory.RegularRingUniversallyCatenary
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.Blowup.Proper
import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.Etale.LocalDimension
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalRing.UniqueFactorization
import WeilConjectures.RingTheory.SmoothFibreRegularLocal

/-! # Fibre defects under point blowups of regular surfaces

Source: Stacks Project, resolve.tex, Tags 0AGQ and 0AGR; models.tex, Tags 0CDC and
0CDD; divisors.tex, Tag 080E. The multiplicity and inseparability calculations are
those of lem-sfb-point-blowup-fibre-defects
(blueprint: lem-sfb-point-blowup-fibre-defects).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SurfacePointBlowup

/-- Geometry, exceptional coefficient, nodal cases, and finiteness of a point blowup.
The projective-line isomorphism is over the actual centre residue field. Connectedness
is a property of the blowup map, with no connectedness condition on the surface family.
Source: Stacks Project, resolve.tex, Tags 0AGQ and 0AGR; models.tex, Tags 0CDC and 0CDD
(blueprint: lem-sfb-point-blowup-fibre-defects).

Proof plan:
1. Finite type over the Noetherian DVR gives a Noetherian total space. Its regular
   irreducible components are disjoint open integral surfaces. Universal catenarity,
   the dimension formula and Zariski's lemma show that the centre has a two-dimensional
   regular local ring and finite residue extension (node proof Step 1).
2. Localize at the centre and use flat base change of blowups, the local regular-surface
   maximal-ideal blowup theorem, and the complement isomorphism. This proves regularity
   and identifies the exceptional fibre with the projective line (Step 2).
3. For parameters a,b, the associated graded ring is l[a,b]. The nonzero initial form
   of pi has finite degree d >= 1, by Krull intersection. On the a-chart pi=a^d G,
   with G a unit at the exceptional generic point. Its divisor coefficient is d
   (Step 3). On the other chart the same computation agrees.
4. Orders are invariant under pointed etale local maps: maximal ideals extend and
   the associated graded pieces extend by a faithfully flat residue-field extension
   (Step 8). A regular nodal chart is uv=pi, hence pi has order two (Step 9).
5. At a smooth fibre point, flatness and finite presentation give smoothness nearby.
   Its regular one-dimensional fibre local ring implies pi is not in m^2, so d=1
   (Step 10). For separable centre residue extension, an etale slice and a section
   coordinate reduce the blowup to the two charts R'[v] and R'[t,w]/(tw-pi').
   Their geometric fibres are reduced pure curves, smooth except for ordinary nodes.
   Etale source locality transports this near the whole exceptional curve (Steps 11-12).
6. The blowup is an isomorphism off the centre and has projective-line geometric fibre
   at the centre. These fibres are nonempty and connected, with no separability
   assumption (Step 13).
7. Blowup charts embed in the local domain's fraction field. They are torsion free
   over the DVR, hence flat. Properness gives finite type of the blowup map; composition
   and the Noetherian finite-type finite-presentation theorem give finite presentation
   over R, including quasi-compactness and quasi-separatedness. Projectivity follows
   from the projective-affine-base blowup theorem (Step 14).
-/
theorem point_blowup_fibre_geometry (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hregular : IsRegularScheme X) (hpure : X.IsPureDimension 2)
    (p : X) (hp : IsClosed ({p} : Set X)) (hs : f p = IsLocalRing.closedPoint R)
    (π : R) (hπ : Irreducible π) :
    IsRegularScheme (pointIdeal p hp).blowup ∧
    (∃ e : exceptional p hp ≅ ProjectiveLine (Spec (X.residueField p)),
      e.hom ≫ (ProjectiveLine (Spec (X.residueField p)) ↘ Spec (X.residueField p)) =
        exceptionalToField p hp) ∧
    (∃ d : ℕ, 1 ≤ d ∧ HasOrder f p π d ∧
      ∀ η : exceptional p hp, IsGenericPoint η Set.univ →
        coefficient (family f p hp) (exceptionalι p hp η) π = (d : ℕ∞)) ∧
    IsProper (pointIdeal p hp).blowupMap ∧
    Flat (family f p hp) ∧ LocallyOfFinitePresentation (family f p hp) ∧
    QuasiCompact (family f p hp) ∧ QuasiSeparated (family f p hp) ∧
    (IsHProjective f → IsHProjective (family f p hp)) ∧
    GeometricallyConnected (pointIdeal p hp).blowupMap ∧
    (IsNodalNear f {p} →
      ((¬ ∃ U : X.Opens, p ∈ U ∧ Smooth (U.ι ≫ f)) → HasOrder f p π 2) ∧
      ((∃ U : X.Opens, p ∈ U ∧ Smooth (U.ι ≫ f)) →
        HasOrder f p π 1 ∧
        (@Algebra.IsSeparableExtension
          ((Spec (.of R)).residueField (IsLocalRing.closedPoint R))
          (X.residueField p) _ _ (residueMap f p hs).hom.toAlgebra →
          IsNodalNear (family f p hp) (Set.range (exceptionalι p hp))))) := by
  sorry

/-- Strict transforms preserve component coefficients and function fields. A multiplicity
defect gives a nonreduced local ring in the scheme-theoretic special fibre and forces
multiplicity greater than one on the exceptional curve of every subsequent point blowup
centred on that component. The transform chain includes any finite number of blowups.
Source: Stacks Project, divisors.tex, Tag 080E; more-algebra.tex, Tag 0AG0; the divisor
calculation following resolve.tex, Tag 0AGQ
(blueprint: lem-sfb-point-blowup-fibre-defects).

Proof plan:
1. At each later centre the surface remains regular, finite type and flat, and its
   closed special-fibre local rings remain two-dimensional, by induction using the
   local surface theorem at exceptional points and the complement isomorphism
   (node proof Step 2).
2. A component generic point is different from every closed centre. The complement
   isomorphism identifies its ambient DVR and function field with those of its strict
   transform, carrying pi to pi. Iterate this along the chain (Step 4).
3. In a generic DVR, pi=u z^m with m>1 makes the image of z nonzero and nilpotent in
   the special-fibre local ring (Step 5).
4. At any later closed centre on that component, regular local factoriality writes
   pi=h^m v, with h a local prime equation for the component. Thus pi belongs to m_y^m.
   The exceptional-order calculation gives exceptional coefficient at least m>1.
   Induction proves the assertion for every later blowup (Step 5).
-/
theorem point_blowup_component_defects (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hregular : IsRegularScheme X) (hpure : X.IsPureDimension 2)
    (π : R) (hπ : Irreducible π) (C : Scheme.{u}) (i : C ⟶ X)
    (hC : IsSpecialComponent f i) (Y D : Scheme.{u})
    (g : Y ⟶ Spec (.of R)) (j : D ⟶ Y) (r : D ⟶ C)
    (hchain : TransformChain R f g i j r) :
    IsSpecialComponent g j ∧
    ∀ η : D, IsGenericPoint η Set.univ →
      IsGenericPoint (r η) Set.univ ∧ Function.Bijective (r.residueFieldMap η) ∧
      coefficient g (j η) π = coefficient f (i (r η)) π ∧
      (1 < coefficient g (j η) π →
        (∃ z : g.fiber (IsLocalRing.closedPoint R),
          g.fiberι (IsLocalRing.closedPoint R) z = j η ∧
          ¬ _root_.IsReduced ((g.fiber (IsLocalRing.closedPoint R)).presheaf.stalk z)) ∧
        ∀ t : D, ∀ ht : IsClosed ({j t} : Set Y),
          g (j t) = IsLocalRing.closedPoint R →
          ∀ ξ : exceptional (j t) ht, IsGenericPoint ξ Set.univ →
            1 < coefficient (family g (j t) ht) (exceptionalι (j t) ht ξ) π) := by
  sorry

/-- Inseparability of an exceptional projective line persists under arbitrary finite
strict-transform chains. Every later closed centre on it has residue field containing
the original centre field compatibly with the actual residue-field maps, and its new
exceptional curve is again not geometrically reduced. This also covers a smooth
inseparable centre, without assuming a perfect residue field.
Source: Stacks Project, Algebra, Tags 030V and 030W; divisors.tex, Tag 080E;
resolve.tex, Tag 0AGQ (blueprint: lem-sfb-point-blowup-fibre-defects).

Proof plan:
1. The centre field l is finite over the trait residue field k, by Zariski's lemma.
   A finite inseparable extension has a nonzero nilpotent in l tensor_k kbar. It stays
   nonzero in (l tensor_k kbar)[t], so the exceptional projective line is not
   geometrically reduced. It also stays nonzero in l(t) tensor_k kbar by injectivity
   of tensoring vector spaces, so the defect is generic (node proof Step 6).
2. A point blowup off this curve is an isomorphism near it. A point blowup on it has
   strict transform the blowup of the projective line at its reduced closed point.
   That point ideal is invertible, generated on l[t] by an irreducible polynomial
   (and on the other chart at infinity). Its blowup is an isomorphism. Iterate using
   the canonical strict-transform-to-source map (Step 7).
3. The resulting l-structure embeds l into every centre residue field. The embedding
   commutes with the ambient residue map because all maps are the canonical ones.
   These finite residue extensions remain inseparable since they contain an
   inseparable element of l. Their exceptional projective lines are non-geometrically
   reduced by Step 1 (Step 7).
4. For a smooth inseparable original centre, Step 10 gives order one, but Step 1 still
   applies to its exceptional curve. No nodality or separability assumption was used.
-/
theorem point_blowup_inseparable_defects (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hregular : IsRegularScheme X) (hpure : X.IsPureDimension 2)
    (p : X) (hp : IsClosed ({p} : Set X)) (hs : f p = IsLocalRing.closedPoint R)
    (hinsep : ¬ @Algebra.IsSeparableExtension
      ((Spec (.of R)).residueField (IsLocalRing.closedPoint R))
      (X.residueField p) _ _ (residueMap f p hs).hom.toAlgebra)
    (Y D : Scheme.{u}) (g : Y ⟶ Spec (.of R)) (j : D ⟶ Y)
    (r : D ⟶ exceptional p hp)
    (hchain : TransformChain R (family f p hp) g (exceptionalι p hp) j r) :
    ¬ GeometricallyReduced (exceptionalToResidue f p hp hs) ∧
    ¬ GeometricallyReduced (r ≫ exceptionalToResidue f p hp hs) ∧
    ∀ t : D, ∀ ht : IsClosed ({j t} : Set Y),
      ∀ hst : g (j t) = IsLocalRing.closedPoint R,
        (∃ φ : X.residueField p →+* Y.residueField (j t),
          Function.Injective φ ∧
          (j.residueFieldMap t).hom.comp φ = fieldMap (r ≫ exceptionalToField p hp) t ∧
          φ.comp (residueMap f p hs).hom = (residueMap g (j t) hst).hom) ∧
        ¬ GeometricallyReduced (exceptionalToResidue g (j t) ht hst) := by
  sorry

end AlgebraicGeometry.SurfacePointBlowup
