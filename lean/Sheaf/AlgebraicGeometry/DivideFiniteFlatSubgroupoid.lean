module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient
import Sheaf.AlgebraicGeometry.FppfKernelPairQuotientDescent
import Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent
import Sheaf.AlgebraicGeometry.ClosedFibrePointQuasiFiniteCriterion
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Division by a finite locally free subgroupoid

Source: Stacks Project, bootstrap.tex, Tag 04S4 (lemma-divide-subgroupoid),
Groupoids Tag 03BM, and stacks-morphisms.tex Tag 06N0
(blueprint: lem-sfb-divide-finite-flat-subgroupoid).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Division of a scheme groupoid by a finite locally free monomorphic subrelation.
The coequalizer is the pointwise orbit presheaf; `η` and its bijection on maps to every
fppf sheaf specify its sheafification, including its canonical quotient map.
The two pullback squares specify restriction of arrows and the inverse image of the unit.
Composition compatibility makes these identifications compatible with groupoid operations.

Source: Stacks Project, Tag 04S4 (lemma-divide-subgroupoid), hypotheses (1)-(5) and proof;
Tag 03BM for surjectivity; Tag 06N0 for the unit square
(blueprint: lem-sfb-divide-finite-flat-subgroupoid).

Proof plan:
1. The finite maps from P to affine U make P affine. Its monomorphic endpoint map and
   subgroupoid laws make it an equivalence relation. Apply
   lem-a1-finite-flat-affine-relation-quotient (03BM): its affine quotient has finite locally
   free surjective quotient map q and kernel pair P, preserving endpoints and composition.
2. By lem-a1-fppf-kernel-pair-quotient-descent, q is an fppf cover. Base change and
   composition (lem-trf-fppf-covering-base-change, lem-trf-finite-locally-free-composition)
   make q squared, cubed and to the fourth power finite locally free surjective covers.
   They are fpqc covers by lem-trf-fppf-covering-is-fpqc.
3. Over the kernel pair of U squared to the quotient squared, transport an arrow r by
   (p,p') to inverse(p) composed with r composed with p'. This is an invertible scheme
   map and satisfies the cocycle identity by associativity and the inverse laws.
4. Discrete fibres and local finite type give local quasi-finiteness in the Stacks sense
   by lem-sfb-closed-fibre-point-quasifinite-criterion. Apply
   lem-trf-separated-lqf-fppf-effective-descent to obtain R-bar and the restriction square.
   The projection h is a cover, so lem-weil-pbc-fpqc-representable-descent checks equality
   and descends maps along it.
5. In this restriction square, equal h-images give unique P-arrows between the two pairs
   of endpoints. The transport formula gives exactly r'=p composed with r composed with p'.
   Conversely transport leaves the h-image unchanged. This uses actual test-scheme points.
6. The source and target descend by the structure map to the quotient squared. Inversion
   respects transport, so descends along h by representable fpqc descent.
7. Identities at P-related objects have the same h-image, so descend along q to the unit.
   The transport formula also shows every P-arrow maps to this unit.
8. Pull back q cubed to the space of composable descended arrows. The three lifted objects
   give unique composable original arrows. Their composite has unchanged h-image on overlaps:
   the middle P-arrows cancel. Representable fpqc descent gives descended composition.
9. Check units and inverses after h; check associativity after the cover from q to the fourth
   power. The original groupoid laws imply all these identities and preservation of operations.
10. If h(r) is the unit at u, its endpoints have q-image u. The kernel pair gives the unique
    P-arrow with those endpoints. Its h-image is the same, so the restriction square forces
    it to equal r. This proves the cartesian unit square and agreement of both P-identifications.
-/
theorem divide_finiteFlat_subgroupoid
    {S : Scheme.{u}} {U R P : Over S} [IsAffine U.left]
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s.left t.left ⟶ R.left)
    (hG : IsGroupoidScheme s.left t.left e.left i.left c)
    (ι : P ⟶ R) [Mono ι.left]
    (eP : U ⟶ P) (iP : P ⟶ P)
    (cP : pullback (ι.left ≫ s.left) (ι.left ≫ t.left) ⟶ P.left)
    (hP : IsGroupoidScheme (ι.left ≫ s.left) (ι.left ≫ t.left) eP.left iP.left cP)
    (heP : eP ≫ ι = e) (hiP : iP ≫ ι = ι ≫ i)
    (hcP : ∀ (H : Scheme.{u}) (a b : H ⟶ P.left)
      (hab : a ≫ (ι.left ≫ s.left) = b ≫ (ι.left ≫ t.left))
      (habR : (a ≫ ι.left) ≫ s.left = (b ≫ ι.left) ≫ t.left),
      pullback.lift a b hab ≫ cP ≫ ι.left =
        pullback.lift (a ≫ ι.left) (b ≫ ι.left) habR ≫ c)
    [(ι.left ≫ s.left).IsFiniteLocallyFree]
    [(ι.left ≫ t.left).IsFiniteLocallyFree]
    [Mono (prod.lift (ι ≫ s) (ι ≫ t))]
    [IsSeparated (prod.lift s t).left]
    [LocallyOfFiniteType (prod.lift s t).left]
    (hdiscrete : ∀ x : (U ⨯ U).left,
      DiscreteTopology ((prod.lift s t).left.fiber x)) :
    ∃ (Ū Rbar : Over S) (q : U ⟶ Ū) (h : R ⟶ Rbar)
      (sbar tbar : Rbar ⟶ Ū) (ebar : Ū ⟶ Rbar) (ibar : Rbar ⟶ Rbar)
      (cbar : pullback sbar.left tbar.left ⟶ Rbar.left),
      IsAffine Ū.left ∧ q.left.IsFiniteLocallyFree ∧ Surjective q.left ∧
      IsPullback (ι ≫ s) (ι ≫ t) q q ∧
      IsGroupoidScheme sbar.left tbar.left ebar.left ibar.left cbar ∧
      s ≫ q = h ≫ sbar ∧ t ≫ q = h ≫ tbar ∧
      e ≫ h = q ≫ ebar ∧ i ≫ h = h ≫ ibar ∧
      (∀ (H : Scheme.{u}) (a b : H ⟶ R.left)
        (hab : a ≫ s.left = b ≫ t.left)
        (habbar : (a ≫ h.left) ≫ sbar.left = (b ≫ h.left) ≫ tbar.left),
        pullback.lift a b hab ≫ c ≫ h.left =
          pullback.lift (a ≫ h.left) (b ≫ h.left) habbar ≫ cbar) ∧
      IsPullback (prod.lift s t) h (Limits.prod.map q q) (prod.lift sbar tbar) ∧
      IsPullback ι (ι ≫ s ≫ q) h ebar ∧
      (ι ≫ s ≫ q = ι ≫ t ≫ q) ∧
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) (uliftYoneda.{u + 1}.obj Ū) ∧
      (∃ η : coequalizer (uliftYoneda.{u + 1}.map (ι ≫ s))
          (uliftYoneda.{u + 1}.map (ι ≫ t)) ⟶ uliftYoneda.{u + 1}.obj Ū,
        coequalizer.π (uliftYoneda.{u + 1}.map (ι ≫ s))
          (uliftYoneda.{u + 1}.map (ι ≫ t)) ≫ η = uliftYoneda.{u + 1}.map q ∧
        ∀ F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)),
          Function.Bijective (fun k : uliftYoneda.{u + 1}.obj Ū ⟶ F.obj ↦ η ≫ k)) ∧
      ∀ (T : Scheme.{u}) (r r' : T ⟶ R.left),
        r ≫ h.left = r' ≫ h.left ↔
          ∃ (p p' : T ⟶ P.left)
            (hpr : (p ≫ ι.left) ≫ s.left = r ≫ t.left)
            (hrp : (pullback.lift (p ≫ ι.left) r hpr ≫ c) ≫ s.left =
              (p' ≫ ι.left) ≫ t.left),
            r' = pullback.lift (pullback.lift (p ≫ ι.left) r hpr ≫ c)
              (p' ≫ ι.left) hrp ≫ c := by
  sorry

end AlgebraicGeometry
