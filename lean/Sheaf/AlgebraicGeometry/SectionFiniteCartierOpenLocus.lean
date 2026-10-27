module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.FibreCartierLocal
import WeilConjectures.AlgebraicGeometry.FinitePushforwardLocallyFree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange

/-!
# The open finite Cartier zero-scheme locus of a line-module morphism

Source: Stacks Project, divisors.tex, Tag 062Y (lemma-fibre-Cartier), especially (3);
pic.tex, Tag 0B9D (lemma-divisors-on-curves); more-morphisms.tex, Tag 02LS
(lemma-characterize-finite); morphisms.tex, Tags 02KB and 04MH.
(blueprint: lem-sfb-section-finite-cartier-open-locus)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The three conditions on the zero scheme in the open-locus assertion: containment in
`U`, the relative effective Cartier condition, and finite local freeness of degree `d`.
The last condition uses the existing finite-locally-free notion: finite, flat, locally of
finite presentation, with every fibre algebra of dimension `d`. By Stacks 02KB and 04MH
this is equivalently finiteness with structure-sheaf pushforward locally free of rank `d`.
This abbreviation bundles these existing predicates and introduces no new geometric data.
Source: Stacks 062Y, 0B9D, 02KB and 04MH.
(blueprint: lem-sfb-section-finite-cartier-open-locus) -/
def FiniteCartierZeroSchemeCondition {Y T : Scheme.{u}} (J : Y.IdealSheafData)
    (p : Y ⟶ T) (U : Y.Opens) (d : ℕ) : Prop :=
  (∀ y : Y, y ∈ J.support → y ∈ U) ∧ J.IsRelativeEffectiveCartier p ∧
    (J.subschemeι ≫ p).IsFiniteLocallyFreeOfDegree d

/-- The universal property of the open finite Cartier zero-scheme locus. The ideal on the
base-changed ambient scheme is the extended ideal, so its subscheme is the scheme-theoretic
pullback, including for nonflat base changes. A map factors through an open precisely when
there is a morphism to that open whose composite with the inclusion is the given map.
Source: the arbitrary-base-change universal property assembled from Stacks 062Y and 02KB.
(blueprint: lem-sfb-section-finite-cartier-open-locus) -/
def IsFiniteCartierZeroLocusOpen {Y T : Scheme.{u}} (J : Y.IdealSheafData)
    (p : Y ⟶ T) (U : Y.Opens) (d : ℕ) (V : T.Opens) : Prop :=
  ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
    (∃ j : T' ⟶ V.toScheme, j ≫ V.ι = h) ↔
      (J.comap (pullback.fst p h)).FiniteCartierZeroSchemeCondition
        (pullback.snd p h) (pullback.fst p h ⁻¹ᵁ U) d

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Modules

/-- The zero scheme of a morphism between invertible modules has a unique open locus on
which it is a finite locally free relative effective Cartier divisor of degree `d` supported
in the prescribed smooth relative curve open. Its universal property holds for every test
scheme; the inverse image of this open represents the same condition after arbitrary base
change. Over a field the condition is precisely an effective Cartier zero scheme of length
`d` supported in that open. Length is the dimension of the global fibre algebra, including
residue-field degrees, rather than the number of support points.

Source: Stacks divisors.tex, Tag 062Y (lemma-fibre-Cartier), (3); pic.tex, Tag 0B9D;
more-morphisms.tex, Tag 02LS; morphisms.tex, Tags 02KB and 04MH.
(blueprint: lem-sfb-section-finite-cartier-open-locus)

Proof:
1. In trivializations the coefficient of `a` changes by a unit, so its principal ideals glue
   to `Hom.zeroLocus a` (def-pc-zero-scheme). Quotients commute with arbitrary scalar
   extension, identifying the extended ideal's subscheme with the pulled-back zero scheme.
2. At a base point with Cartier fibre, lem-pc-recd-fibre-cartier-local spreads the Cartier
   condition near each point of the zero fibre. Adjoin the complement of the zero scheme.
   Properness removes the closed images of the complement of this neighbourhood and of
   the part of the zero scheme outside `U`. This gives a base neighbourhood with a relative
   effective Cartier divisor supported in `U`.
3. On the smooth relative curve open, lem-pc-cartier-criterion gives local quasi-finiteness,
   flatness and local finite presentation. Proper base change and properness of a closed
   immersion make the divisor proper; pqf-lem-proper-lqf-finite makes it finite.
   lem-sc-finite-pushforward-locally-free gives a locally free structure algebra. Relative
   Cartier pullback shows all fibres are Cartier, so these neighbourhoods cover the good
   locus and prove it open.
4. lem-weil-pbc-finite-locally-free-degree-locally-constant cuts out the degree-`d` piece.
   The local pushforward rank equals its fibre algebra dimension by
   lem-weil-pbc-affine-pushforward-base-change. Thus the structure algebra is locally free
   of rank exactly `d` on this piece.
5. A map factoring through this open preserves the relative Cartier condition by
   lem-pc-recd-pullback. It preserves support containment. On affine charts scalar extension
   sends a free rank-`d` algebra module to a free rank-`d` module, proving the forward
   implication for arbitrary, possibly nonflat, maps.
6. Conversely, at a point of a test scheme the field extension of its image's residue
   field is faithfully flat. Relative Cartier pullback makes the extended fibre Cartier;
   lem-trf-faithfully-flat-ltensor-injective-reflection reflects injectivity of coefficient
   multiplication. Faithfully flat surjectivity on spectra reflects support containment.
7. lem-pc-finrank-field-base-change reflects the length `d`. Thus every image point is in
   the degree-`d` piece, so the map factors through it. Residue-field tests give uniqueness.
   Associativity of pullback gives the stated base-change universal property and the
   field-valued formulation. A zero rank algebra is zero and its spectrum is empty; the
   argument therefore includes degree zero, empty opens and the empty base.
-/
theorem existsUnique_finiteCartierZeroLocusOpen
    {Y T : Scheme.{u}} (p : Y ⟶ T) [IsProper p] [Flat p]
    [LocallyOfFinitePresentation p] (U : Y.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ p)]
    (M N : Y.Modules) [M.IsInvertible] [N.IsInvertible] (a : M ⟶ N) (d : ℕ) :
    ∃! V : T.Opens,
      a.zeroLocus.IsFiniteCartierZeroLocusOpen p U d V ∧
      (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        (a.zeroLocus.comap (pullback.fst p h)).IsFiniteCartierZeroLocusOpen
          (pullback.snd p h) (pullback.fst p h ⁻¹ᵁ U) d (h ⁻¹ᵁ V)) ∧
      (∀ (K : Type u) [Field K] (h : Spec (.of K) ⟶ T),
        (∃ j : Spec (.of K) ⟶ V.toScheme, j ≫ V.ι = h) ↔
          (∀ y : (Limits.pullback p h : Scheme.{u}),
            y ∈ (a.zeroLocus.comap (pullback.fst p h)).support →
              y ∈ pullback.fst p h ⁻¹ᵁ U) ∧
          (a.zeroLocus.comap (pullback.fst p h)).IsInvertible ∧
          IsFinite ((a.zeroLocus.comap (pullback.fst p h)).subschemeι ≫ pullback.snd p h) ∧
          ((a.zeroLocus.comap (pullback.fst p h)).subschemeι ≫ pullback.snd p h).finrankΓ = d) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
