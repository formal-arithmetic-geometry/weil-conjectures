module

public import Sheaf.AlgebraicGeometry.ProperHilbertPresheaf
public import Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Sheaf.AlgebraicGeometry.NoetherianDvrProperness
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Gluing Hilbert charts and proving projectivity

Source: Grothendieck, Bourbaki Expose 221, proof of Theorem 3.2, pp.260--265,
especially the conclusion following Lemma 3.7. Descent of embedded families is made
explicit using ideal sheaves, as in Stacks Project, Tags 01LH and 01QO.
(blueprint: lem-sfb-hilbert-chart-gluing-projectivity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Affine representing charts and their immersions glue, including their universal ideals.
The fixed-polynomial presheaf is specified as a subfunctor of `properHilbertPresheaf`, with
membership exactly the existing fibre-polynomial predicate. Properness of a closed family
is automatic in the given projective ambient scheme. Its finite presentation is therefore
equivalent to the local finite presentation in `IsProperHilbertFamily`.

The given `jU` is written as the composite into `G`. Its adjoint under `mapPullbackAdj`
is precisely the given morphism into `G_U`. Compatibility is tested on arbitrary common
open restrictions: two test schemes over U and V identified over S give the same map to G.
The isomorphisms `a` in that condition merely allow different presentations of the same
common test scheme. The pullback squares in the conclusion give the chart isomorphisms;
the following uniqueness clause singles out those preserving representation.

The final implication deliberately places the DVR hypothesis after the glued data and the
finite-type immersion. Thus these data exist before that hypothesis is used.

Source: Grothendieck, Bourbaki Expose 221, Theorem 3.2, pp.260--265, conclusion after
Lemma 3.7; Stacks Project, Tags 01LH, 01QO, 0208, 01W6, 01IQ and 01WC.
(blueprint: lem-sfb-hilbert-chart-gluing-projectivity)

Proof (the thirteen steps of the node):
1. For affine V contained in U, fibre products identify the two local representing
   functors. Yoneda full faithfulness gives unique transition isomorphisms; uniqueness
   gives the identity and cocycle equations. Intersections need not be affine.
2. Relative affine-basis gluing (Tag 01LH) gives Y over S. Compatibility of the induced
   transformations and Yoneda faithfulness glue jU to j, by scheme-morphism gluing.
3. Glue compatible embedded families on an arbitrary open cover of an arbitrary test
   scheme. Closed immersions are local on the target. The glued ideal consists of the
   sections whose restrictions lie in every local ideal; the sheaf axiom and the kernel
   description of a closed immersion give existence and uniqueness of this ideal.
4. Flatness and finite presentation are local on the target, and the polynomial can be
   checked in an open containing the image of each geometric point. This is the selected
   flatness/finite-presentation part of lem-trf-structural-fibrewise-open-locality, with
   all extra arrows identities; it imposes no assumptions on the test scheme.
5. On the cover T times_S U, the local representing bijections identify families with
   maps into the charts. The two gluing constructions are inverse and natural. Yoneda
   gives uniqueness of the representing chart identifications.
6. Apply this to the chart identities: their families and ideals glue to the family of
   the identity of Y. Evaluation at the identity and naturality identify every family
   with its pullback. The restriction equations are equalities of actual ideal sheaves.
7. H-projectivity makes G proper, hence separated and finite type. Base change and
   composition with jU make the charts finite type over their affine bases.
8. A finite affine cover of the Noetherian base gives a finite Noetherian open cover of
   Y, using finite-type-over-Noetherian. Thus Y is Noetherian.
9. The pointwise affine criterion makes Y to S and j locally finite type. Their inverse
   images of affine opens are opens in Noetherian Y and hence quasi-compact. Both maps
   are finite type. No DVR hypothesis has been used.
10. Immersion locality near the image applied to the covering G_U makes j an immersion.
11. DVR bijectivity and naturality give existence and uniqueness of lifts for Y to S.
    Apply lem-sfb-noetherian-dvr-properness (Tag 0208), since finite type is already known.
12. A morphism proper over S into an S-separated scheme is proper (Tag 01W6). Thus j is
    proper; a proper immersion is closed (Tag 01IQ).
13. Compose j with a finite projective-space embedding of G. Composition of closed
    immersions gives H-projectivity of Y to S. Properness supplies separatedness and
    finite type. Flatness of E over S was never used. -/
theorem exists_hilbert_chart_gluing_projectivity
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (E : Over S) (n : ℕ) (i : E.left ⟶ ℙ(ULift.{u} (Fin (n + 1)); S))
    [IsClosedImmersion i] (hi : i ≫ (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S) = E.hom)
    (P : NumericalHilbertPolynomial) (F : Subfunctor (properHilbertPresheaf E.hom))
    (hF : ∀ (T : Over S) (I : (properHilbertPresheaf E.hom).obj (op T)),
      I ∈ F.obj (op T) ↔ HasProjectiveFibreHilbertPolynomial E.hom i T I.1 P.1)
    (G : Over S) [IsHProjective G.hom]
    (YU : ∀ U : S.affineOpens, Over U.1.toScheme)
    (jU : ∀ U : S.affineOpens, (Over.map U.1.ι).obj (YU U) ⟶ G)
    (hU : ∀ U : S.affineOpens,
      IsImmersion (((Over.mapPullbackAdj U.1.ι).homEquiv (YU U) G (jU U)).left) ∧
      LocallyOfFiniteType (((Over.mapPullbackAdj U.1.ι).homEquiv (YU U) G (jU U)).left) ∧
      QuasiCompact (((Over.mapPullbackAdj U.1.ι).homEquiv (YU U) G (jU U)).left))
    (eU : ∀ U : S.affineOpens,
      ((Over.map U.1.ι).op ⋙ F.toFunctor).RepresentableBy (YU U))
    (hcompat : ∀ (U V : S.affineOpens) (T : Over U.1.toScheme) (T' : Over V.1.toScheme)
      (a : (Over.map U.1.ι).obj T ≅ (Over.map V.1.ι).obj T')
      (x : F.toFunctor.obj (op ((Over.map V.1.ι).obj T'))),
      (Over.map U.1.ι).map ((eU U).homEquiv.symm (F.toFunctor.map a.hom.op x)) ≫ jU U =
        a.hom ≫ (Over.map V.1.ι).map ((eU V).homEquiv.symm x) ≫ jU V) :
    ∃ (Y : Over S) (e : F.toFunctor.RepresentableBy Y) (j : Y ⟶ G)
      (κ : ∀ U : S.affineOpens, (Over.map U.1.ι).obj (YU U) ⟶ Y),
      IsImmersion j.left ∧ LocallyOfFiniteType j.left ∧ QuasiCompact j.left ∧
      LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
      (∀ U : S.affineOpens,
        IsPullback (κ U).left (YU U).hom Y.hom U.1.ι ∧ κ U ≫ j = jU U ∧
        ∀ (T : Over U.1.toScheme) (g : T ⟶ YU U),
          e.homEquiv ((Over.map U.1.ι).map g ≫ κ U) = (eU U).homEquiv g) ∧
      (∀ (U : S.affineOpens) (a : (Over.map U.1.ι).obj (YU U) ⟶ Y),
        (∀ (T : Over U.1.toScheme) (g : T ⟶ YU U),
          e.homEquiv ((Over.map U.1.ι).map g ≫ a) = (eU U).homEquiv g) → a = κ U) ∧
      (∀ U : S.affineOpens,
        ((eU U).homEquiv (𝟙 (YU U))).1.1 =
          (e.homEquiv (𝟙 Y)).1.1.comap (baseChangeMap E.hom (κ U))) ∧
      (∀ I : (pullback E.hom Y.hom).IdealSheafData,
        (∀ U : S.affineOpens, I.comap (baseChangeMap E.hom (κ U)) =
          ((eU U).homEquiv (𝟙 (YU U))).1.1) → I = (e.homEquiv (𝟙 Y)).1.1) ∧
      (∀ (T : Over S) (g : T ⟶ Y),
        (e.homEquiv g).1.1 = (e.homEquiv (𝟙 Y)).1.1.comap (baseChangeMap E.hom g)) ∧
      ((∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
          (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
          (b : Spec (.of R) ⟶ S),
          Function.Bijective
            (F.toFunctor.map (Over.homMk
              (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b))
              (V := Over.mk b) (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl).op)) →
        IsClosedImmersion j.left ∧ IsHProjective Y.hom ∧ IsProper Y.hom ∧
          IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) := by
  sorry

end AlgebraicGeometry
