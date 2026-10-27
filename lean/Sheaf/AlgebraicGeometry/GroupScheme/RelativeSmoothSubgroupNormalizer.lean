module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.FiniteStability

/-! # Relative normalizers of smooth connected subgroup schemes

Source: Conrad, Reductive group schemes, Proposition 2.1.6, printed pp.61--63.
(blueprint: lem-sfb-relative-smooth-subgroup-normalizer)

The normalizer is characterized by equality of subgroup functors on every scheme
above a test scheme. Base change is stated using the usual pullback functor on
bundled group objects, together with the unique comparison isomorphism over the
ambient group to every other closed representative of the same normalizer.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- The embedding `j` represents the normalizer of `i`: a `W`-point factors through
`j` exactly when its conjugation preserves the image of `H` on every `U → W`.
The equality of ranges, including on nonreduced tests, is equality of subgroup
functors, rather than merely equality on geometric points. For a closed immersion
`j`, the point factorization is unique, and its naturality is given by composition.

Source: Conrad, Proposition 2.1.6, displayed normalizer functor, printed p.61.
(blueprint: lem-sfb-relative-smooth-subgroup-normalizer) -/
def IsRelativeGroupSchemeNormalizer {S : Scheme.{u}} {G H N : Grp (Over S)}
    (i : H ⟶ G) (j : N ⟶ G) : Prop :=
  ∀ (W : Over S) (g : W ⟶ G.X),
    (∃ n : W ⟶ N.X, n ≫ j.hom.hom = g) ↔
      ∀ (U : Over S) (f : U ⟶ W),
        Set.range (fun h : U ⟶ H.X ↦
          (f ≫ g) * (h ≫ i.hom.hom) * (f ≫ g)⁻¹) =
          Set.range (fun h : U ⟶ H.X ↦ h ≫ i.hom.hom)

/-- A smooth finitely presented closed subgroup with nonempty geometrically
connected fibres in a smooth affine group over `Spec A` has a finitely presented
closed normalizer, contains the subgroup canonically, and commutes with arbitrary
scheme base change. There is no flatness or smoothness conclusion for the normalizer.

Source: Conrad, Proposition 2.1.6, printed pp.61--63.
(blueprint: lem-sfb-relative-smooth-subgroup-normalizer)

Proof plan:
1. Apply lem-sfb-smooth-connected-subgroup-noetherian-model to descend the ring,
   groups, embedding and hypotheses to a finitely generated Noetherian subring.
   No representability or limit compatibility of the normalizer is assumed here.
2. At the identity section of H use lem-sfb-smooth-section-finite-jets and
   lem-sfb-smooth-section-universal-jet-density: the infinitesimal neighbourhoods
   D_n are finite locally free and universally weakly schematically dense in H.
3. Apply lem-sfb-finite-locally-free-source-factorization-locus to conjugation by
   g and by its inverse on D_n, obtaining two finitely presented closed loci in G.
4. Sum their ideals in the affine coordinate ring of G. The quotient represents
   their intersection on affine tests. Lem-weil-pbc-scheme-morphism-gluing extends
   this to arbitrary tests. Closed inverse images and universal jet density show
   that the two containment conditions are equivalent to equality of conjugate
   subgroup schemes (lem-weil-pbc-closed-immersion-base-change).
5. Pqf-lem-affine-open-locnoeth and def-weil-pbc-noetherian-ring make the summed
   ideal finitely generated. Lem-weil-pbc-lfp-affine-opens-finite-presentation and
   lem-weil-pbc-finite-presentation-quotient-fg-ideal give finite presentation of
   both the quotient over the base and its closed embedding in G.
6. Multiplication and inversion preserve the normalizing condition. Yoneda
   (lem-pc-yoneda) supplies the group operations; the closed embedding is monic
   (lem-pc-proper-monomorphism-closed), so all group diagrams hold. H normalizes
   itself on every test, giving its unique factorization; the surjection between
   the two quotient coordinate rings makes this inclusion closed.
7. Pull the construction back to Spec A using
   lem-weil-pbc-finite-presentation-base-change-composition and
   lem-weil-pbc-closed-immersion-base-change. The test-point description is
   unchanged under every further base change, including nonflat ones. Yoneda
   gives the unique comparison isomorphism commuting with the embeddings in G.
-/
theorem exists_relative_smooth_subgroup_normalizer
    (A : Type u) [CommRing A] (G H : Grp (Over (Spec (.of A))))
    [IsAffine G.X.left] [Smooth G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (i : H ⟶ G) [IsClosedImmersion i.hom.hom.left]
    [LocallyOfFinitePresentation i.hom.hom.left]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom] :
    ∃ (N : Grp (Over (Spec (.of A)))) (j : N ⟶ G),
      IsClosedImmersion j.hom.hom.left ∧
      LocallyOfFinitePresentation j.hom.hom.left ∧
      LocallyOfFinitePresentation N.X.hom ∧ QuasiCompact N.X.hom ∧
      QuasiSeparated N.X.hom ∧ IsRelativeGroupSchemeNormalizer i j ∧
      (∃! h : H ⟶ N, IsClosedImmersion h.hom.hom.left ∧ h ≫ j = i) ∧
      ∀ (S' : Scheme.{u}) (f : S' ⟶ Spec (.of A)),
        IsRelativeGroupSchemeNormalizer ((Over.pullback f).mapGrp.map i)
          ((Over.pullback f).mapGrp.map j) ∧
        ∀ (N' : Grp (Over S'))
          (j' : N' ⟶ (Over.pullback f).mapGrp.obj G),
          IsClosedImmersion j'.hom.hom.left →
          IsRelativeGroupSchemeNormalizer ((Over.pullback f).mapGrp.map i) j' →
          ∃! e : (Over.pullback f).mapGrp.obj N ≅ N',
            e.hom ≫ j' = (Over.pullback f).mapGrp.map j := by
  sorry

end AlgebraicGeometry
