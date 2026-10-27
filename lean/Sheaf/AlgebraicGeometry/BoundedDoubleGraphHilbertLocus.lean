/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.AlgebraicGeometry.ProperHilbertPresheaf
public import Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf
public import Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial
public import Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability
import Sheaf.AlgebraicGeometry.GraphsOpenInHilbert
import Mathlib.RingTheory.FinitePresentation

/-!
# The bounded double graph open in a projective Hilbert scheme

Source: Stacks Project, moduli-curves.tex, Tag 0DSQ, final bounded-open argument;
quot.tex, Tags 0D1A and 0D1B
(blueprint: lem-sfb-bounded-double-graph-hilbert-locus).

The fixed polynomial is a hypothesis; there is no restriction on fibre dimension.
All test schemes and base changes below are arbitrary, including nonreduced schemes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/-- The second graph projection, retaining the test-scheme coordinate. This is the
canonical lift of the recorded second projection to `Y_T`.
Source: Stacks, Tag 0D1B (blueprint: lem-sfb-bounded-double-graph-hilbert-locus). -/
def doubleGraphSecondProjection {X Y U : Scheme.{u}} (x : X ⟶ U) (y : Y ⟶ U)
    (T : Over U) : pullback (pullback.fst x y ≫ x) T.hom ⟶ pullback T.hom y :=
  pullback.lift (pullback.snd _ _) (graphSecondProjection x y T) (by
    simp only [graphSecondProjection, Category.assoc]
    exact (pullback.condition (f := pullback.fst x y ≫ x) (g := T.hom)).symm.trans
      (by
        simpa only [Category.assoc] using
          (congrArg (fun a ↦ pullback.fst (pullback.fst x y ≫ x) T.hom ≫ a)
            (pullback.condition (f := x) (g := y)))))

/-- Forgetting the test-coordinate of an over-isomorphism gives the recorded relative
morphism, without choosing an arbitrary map.
Source: Stacks, Tag 0D1A (blueprint: lem-sfb-bounded-double-graph-hilbert-locus). -/
def doubleGraphRelativeMorphism {X Y U : Scheme.{u}} (x : X ⟶ U) (y : Y ⟶ U)
    (T : Over U) (f : Over.mk (pullback.fst T.hom x) ≅ Over.mk (pullback.fst T.hom y)) :
    (relativeMorphismsPresheaf x y).obj (op T) :=
  Over.homMk (f.hom.left ≫ pullback.snd T.hom y) (by
    change (f.hom.left ≫ pullback.snd T.hom y) ≫ y = pullback.snd T.hom x ≫ x
    calc
      (f.hom.left ≫ pullback.snd T.hom y) ≫ y =
          (f.hom.left ≫ pullback.fst T.hom y) ≫ T.hom := by
        simp only [Category.assoc]
        exact congrArg (fun a ↦ f.hom.left ≫ a)
          (pullback.condition (f := T.hom) (g := y)).symm
      _ = pullback.fst T.hom x ≫ T.hom :=
        congrArg (fun a ↦ a ≫ T.hom) f.hom.w
      _ = pullback.snd T.hom x ≫ x := pullback.condition)

/-- The actual closed-graph map of an isomorphism, using the existing graph construction.
Source: Stacks, Tag 0D1A (blueprint: lem-sfb-bounded-double-graph-hilbert-locus). -/
def doubleGraphMap {X Y U : Scheme.{u}} (x : X ⟶ U) (y : Y ⟶ U)
    (T : Over U) (f : Over.mk (pullback.fst T.hom x) ≅ Over.mk (pullback.fst T.hom y)) :
    pullback T.hom x ⟶ pullback (pullback.fst x y ≫ x) T.hom :=
  relativeMorphismGraph x y T (doubleGraphRelativeMorphism x y T f)

/-- The specified projective embedding after base change. The equation `hi` identifies
its structure map with the given one; the construction uses the projective-space
pullback universal property and both canonical projections.
Source: Stacks, Tag 01W6 (blueprint: lem-sfb-bounded-double-graph-hilbert-locus). -/
def doubleGraphBaseChangeEmbedding {E U : Scheme.{u}} (w : E ⟶ U) (m : ℕ)
    (j : E ⟶ ℙ(ULift.{u} (Fin (m + 1)); U))
    (hi : j ≫ (ℙ(ULift.{u} (Fin (m + 1)); U) ↘ U) = w)
    {T : Scheme.{u}} (t : T ⟶ U) : pullback w t ⟶ ℙ(ULift.{u} (Fin (m + 1)); T) :=
  ProjectiveSpace.liftBaseChange (g := t) (pullback.snd w t) (pullback.fst w t ≫ j) (by
    rw [Category.assoc, hi, pullback.condition])

/-- The double graph locus is an open of the fixed projective polynomial component,
Noetherian and quasi-compact, separated and finitely presented over the base. Its
points, including on nonreduced schemes, are exactly isomorphisms and their actual
closed graph ideals. The inverse-projection formula and its two projection identities
are specified. The last clause gives the canonical identifications after every change
of base, using the map/pullback adjunction rather than an arbitrary bijection.

Source: Stacks, Tag 0DSQ, final paragraph; Tags 0D1A and 0D1B
(blueprint: lem-sfb-bounded-double-graph-hilbert-locus).

Proof plan (the eight steps of the node):
1. Apply lem-sfb-projective-hilbert-polynomial-representability to the specified
   embedding. Proper base change, composition and closed-immersion properness show
   that its Hilbert families are precisely properHilbertPresheaf families.
2. Apply lem-sfb-graphs-open-in-hilbert twice, exchanging X and Y for the second
   application. Intersect the opens in the representing scheme, with restricted sheaf.
3. For a closed family with invertible projections recover f = p_X inverse followed
   by p_Y. Its graph has the same two components as the inclusion transported by p_X,
   so the fibre-product universal property gives equality of closed subschemes.
   Conversely a graph has projections identity and f. The two constructions are inverse.
4. At any point of the intersection pass to an algebraic closure of its residue field.
   The fixed-polynomial hypothesis puts it in H_R. The complement has empty inverse
   image, so the intersection factors through the open H_R, including nilpotents.
5. The finite-type stratum over Noetherian U is Noetherian; its open is Noetherian
   and quasi-compact. Locally Noetherian schemes are quasi-separated. The qcqs
   morphism permanence lemma gives quasi-compactness and quasi-separatedness over U.
6. The diagonal of J is the pullback of the closed diagonal of H_R, since its open
   immersion is a monomorphism. Closed immersions survive base change.
7. On affine Noetherian charts, distinguished opens of J have finite-type coordinate
   algebras. Algebra.FinitePresentation.of_finiteType gives finite presentation.
   Together with step 5 this proves finite presentation of J over U.
8. Pull back the universal ideal and both projections. Inverse identities pull back,
   so graph formation and recovery commute with every test morphism. The
   map/pullback adjunction identifies maps into the pulled-back representatives and
   components with the same families. No reducedness or Noetherianity of a test
   scheme or new base is used. -/
theorem exists_bounded_double_graph_hilbert_locus
    {U X Y : Scheme.{u}} [IsAffine U] [IsLocallyNoetherian U]
    (x : X ⟶ U) (y : Y ⟶ U) [IsProper x] [IsProper y] [Flat x] [Flat y]
    [LocallyOfFinitePresentation x] [LocallyOfFinitePresentation y]
    (m : ℕ) (j : pullback x y ⟶ ℙ(ULift.{u} (Fin (m + 1)); U))
    [IsClosedImmersion j]
    (hj : j ≫ (ℙ(ULift.{u} (Fin (m + 1)); U) ↘ U) = pullback.fst x y ≫ x)
    (R : NumericalHilbertPolynomial)
    (hR : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ U)
      (f : Over.mk (pullback.fst t x) ≅ Over.mk (pullback.fst t y)),
      ProjectiveHilbertPolynomial.IsCoordinatePolynomial Ω m
        (doubleGraphMap x y (Over.mk t) f ≫
          doubleGraphBaseChangeEmbedding (pullback.fst x y ≫ x) m j hj t) R.1) :
    ∃ (H : Over U)
      (eH : (properHilbertPresheaf (pullback.fst x y ≫ x)).RepresentableBy H)
      (HP : NumericalHilbertPolynomial → Over U) (ι : ∀ P, HP P ⟶ H),
      Nonempty (IsColimit (Cofan.mk H ι)) ∧
      (∀ P, IsOpenImmersion (ι P).left ∧ IsHProjective (HP P).hom) ∧
      (∀ (P : NumericalHilbertPolynomial) (T : Over U) (a : T ⟶ H),
        HasProjectiveFibreHilbertPolynomial (pullback.fst x y ≫ x) j T
          (eH.homEquiv a).1 P.1 ↔ ∃! b : T ⟶ HP P, b ≫ ι P = a) ∧
      ∃ (HX HY J : Over U) (iX : HX ⟶ H) (iY : HY ⟶ H)
        (pX : J ⟶ HX) (pY : J ⟶ HY) (iJ : J ⟶ H) (r : J ⟶ HP R),
        IsOpenImmersion iX.left ∧ IsOpenImmersion iY.left ∧
        IsPullback pX pY iX iY ∧ pX ≫ iX = iJ ∧ r ≫ ι R = iJ ∧
        IsOpenImmersion r.left ∧ IsNoetherian J.left ∧ CompactSpace J.left ∧
        IsSeparated J.hom ∧ LocallyOfFinitePresentation J.hom ∧
        QuasiCompact J.hom ∧ QuasiSeparated J.hom ∧
        (∀ (T : Over U) (a : T ⟶ H),
          (IsIso ((eH.homEquiv a).1.subschemeι ≫ graphFirstProjection x y T) ↔
            ∃! b : T ⟶ HX, b ≫ iX = a) ∧
          (IsIso ((eH.homEquiv a).1.subschemeι ≫ doubleGraphSecondProjection x y T) ↔
            ∃! b : T ⟶ HY, b ≫ iY = a)) ∧
        (∀ (T : Over U)
          (D : (properHilbertPresheaf (pullback.fst x y ≫ x)).obj (op T)),
          (IsIso (D.1.subschemeι ≫ graphFirstProjection x y T) ∧
            IsIso (D.1.subschemeι ≫ doubleGraphSecondProjection x y T)) ↔
              ∃! a : T ⟶ J, eH.homEquiv (a ≫ iJ) = D) ∧
        ∃ eJ : ∀ T : Over U, (T ⟶ J) ≃
          (Over.mk (pullback.fst T.hom x) ≅ Over.mk (pullback.fst T.hom y)),
          (∀ (T : Over U) (a : T ⟶ J),
            IsClosedImmersion (doubleGraphMap x y T (eJ T a)) ∧
            (eH.homEquiv (a ≫ iJ)).1 = (doubleGraphMap x y T (eJ T a)).ker ∧
            ∃ (p : (eH.homEquiv (a ≫ iJ)).1.subscheme ≅ pullback T.hom x)
              (q : (eH.homEquiv (a ≫ iJ)).1.subscheme ≅ pullback T.hom y),
              p.hom = (eH.homEquiv (a ≫ iJ)).1.subschemeι ≫
                graphFirstProjection x y T ∧
              q.hom = (eH.homEquiv (a ≫ iJ)).1.subschemeι ≫
                doubleGraphSecondProjection x y T ∧
              p.inv ≫ q.hom = (eJ T a).hom.left) ∧
          (∀ (T' T : Over U) (h : T' ⟶ T) (a : T ⟶ J),
            ((Over.pullback x).map h).left ≫ (eJ T a).hom.left =
              (eJ T' (h ≫ a)).hom.left ≫ ((Over.pullback y).map h).left) ∧
          (∀ (T' T : Over U) (h : T' ⟶ T) (a : T ⟶ J),
            (eH.homEquiv ((h ≫ a) ≫ iJ)).1 =
              (eH.homEquiv (a ≫ iJ)).1.comap
                (baseChangeMap (pullback.fst x y ≫ x) h)) ∧
          (∀ (U' : Scheme.{u}) (g : U' ⟶ U),
            ∃ eb : ((Over.map g).op ⋙
                properHilbertPresheaf (pullback.fst x y ≫ x)).RepresentableBy
                  ((Over.pullback g).obj H),
              (∀ (T : Over U') (a : T ⟶ (Over.pullback g).obj H),
                eb.homEquiv a = eH.homEquiv
                  (((Over.mapPullbackAdj g).homEquiv T H).symm a)) ∧
              (∀ (P : NumericalHilbertPolynomial) (T : Over U')
                (a : T ⟶ (Over.pullback g).obj H),
                HasProjectiveFibreHilbertPolynomial (pullback.fst x y ≫ x) j
                  ((Over.map g).obj T) (eb.homEquiv a).1 P.1 ↔
                    ∃! b : T ⟶ (Over.pullback g).obj (HP P),
                      b ≫ (Over.pullback g).map (ι P) = a) ∧
              ∃ ebJ : ∀ T : Over U', (T ⟶ (Over.pullback g).obj J) ≃
                (Over.mk (pullback.fst (T.hom ≫ g) x) ≅
                  Over.mk (pullback.fst (T.hom ≫ g) y)),
                ∀ (T : Over U') (a : T ⟶ (Over.pullback g).obj J),
                  ebJ T a = eJ ((Over.map g).obj T)
                    (((Over.mapPullbackAdj g).homEquiv T J).symm a)) := by
  sorry

end AlgebraicGeometry
