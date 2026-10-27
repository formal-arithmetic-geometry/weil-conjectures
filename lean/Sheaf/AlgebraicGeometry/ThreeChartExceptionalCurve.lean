module

public import Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Reciprocal gluing of the exceptional conic and pair of lines

Source: literature/stacks-project/divisors.tex, explicit exceptional-curve calculation
extracted from inherited steps 11--12, following Tag 0804
(blueprint: lem-sfb-three-chart-exceptional-curve).

`Charts` specifies the actual open embeddings and their cartesian overlaps, including the
coordinate substitutions. `ConicData` and `NodalData` retain the identifications as data so
that the final theorem can assert their compatibility with coefficient extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ThreeChartExceptional

/-- The scalar zero or one. Source: the chart calculation following Stacks 0804
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
def epsilonScalar (k : Type u) [Field k] (ε : Fin 2) : k :=
  if ε = 0 then 0 else 1

/-- Specialization of the existing nodal algebra to `rs=ε`.
Source: the chart calculation following Stacks 0804
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
abbrev middleRing (k : Type u) [Field k] (ε : Fin 2) :=
  strictNodalRing (.of k) (epsilonScalar k ε)

/-- The coordinate classes in the existing nodal algebra.
Source: the chart calculation following Stacks 0804
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
def middleCoord (k : Type u) [Field k] (ε : Fin 2) (i : Fin 2) : middleRing k ε :=
  DvrNodal.coordinate (.of k) (epsilonScalar k ε) i

/-- Inclusion of constants in the middle chart.
Source: the chart calculation following Stacks 0804
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
def middleConstants (k : Type u) [Field k] (ε : Fin 2) : k →+* middleRing k ε :=
  (Ideal.Quotient.mk _).comp MvPolynomial.C

/-- A three-chart presentation of the scheme over `k`. Each adjacent intersection is the
specified principal open with its actual coordinate substitutions; the outer intersection is
reciprocal for `ε=1` and empty for `ε=0`. The pullback conditions bind the transitions to the
open embeddings, rather than merely asserting existence of unrelated ring isomorphisms.
Source: the chart calculation following Stacks 0804, node proof step 1
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
structure Charts (k : Type u) [Field k] (ε : Fin 2)
    (E : Scheme.{u}) (p : E ⟶ Spec (.of k)) where
  left : Spec (.of (Polynomial k)) ⟶ E
  middle : Spec (.of (middleRing k ε)) ⟶ E
  right : Spec (.of (Polynomial k)) ⟶ E
  left_open : IsOpenImmersion left
  middle_open : IsOpenImmersion middle
  right_open : IsOpenImmersion right
  cover : Set.range left ∪ Set.range middle ∪ Set.range right = Set.univ
  left_over : left ≫ p = Spec.map (CommRingCat.ofHom Polynomial.C)
  middle_over : middle ≫ p = Spec.map (CommRingCat.ofHom (middleConstants k ε))
  right_over : right ≫ p = Spec.map (CommRingCat.ofHom Polynomial.C)
  left_overlap : ∃ f : middleRing k ε →+*
      Localization.Away (Polynomial.X : Polynomial k),
    f.comp (middleConstants k ε) =
      (algebraMap (Polynomial k) _).comp Polynomial.C ∧
    f (middleCoord k ε 0) = IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) ∧
    f (middleCoord k ε 1) =
      algebraMap (Polynomial k) _ (Polynomial.C (epsilonScalar k ε) * Polynomial.X) ∧
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) _)))
      (Spec.map (CommRingCat.ofHom f)) left middle
  right_overlap : ∃ f : middleRing k ε →+*
      Localization.Away (Polynomial.X : Polynomial k),
    f.comp (middleConstants k ε) =
      (algebraMap (Polynomial k) _).comp Polynomial.C ∧
    f (middleCoord k ε 1) = IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) ∧
    f (middleCoord k ε 0) =
      algebraMap (Polynomial k) _ (Polynomial.C (epsilonScalar k ε) * Polynomial.X) ∧
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) _)))
      (Spec.map (CommRingCat.ofHom f)) right middle
  outer_overlap : ε = 1 → ∃ f : Polynomial k →+*
      Localization.Away (Polynomial.X : Polynomial k),
    f.comp Polynomial.C = (algebraMap (Polynomial k) _).comp Polynomial.C ∧
    f Polynomial.X = IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) ∧
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) _)))
      (Spec.map (CommRingCat.ofHom f)) left right
  outer_disjoint : ε = 0 → Disjoint (Set.range left) (Set.range right)

/-- Global sections representing a homogeneous coordinate vector on an affine spectrum.
Source: the conic parametrizations in node proof steps 3--4, following Stacks 0804
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
def coordinateSections (A : Type u) [CommRing A] (v : Fin 3 → A) :
    ULift.{u} (Fin 3) → Γ(Spec (.of A), ⊤) :=
  fun i => (Scheme.ΓSpecIso (.of A)).inv (v i.down)

/-- The conic identification, including its actual chart parametrizations and two-open cover.
The conic is the existing scheme-theoretic zero locus of `XY-P²`; no radical is taken.
Source: node proof steps 2--5, following Stacks 0804 and 01M4
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
structure ConicData (k : Type u) [Field k] (ε : Fin 2)
    (E : Scheme.{u}) (p : E ⟶ Spec (.of k)) (C : Charts k ε E p) where
  lineIso : E ≅ ProjectiveLine (Spec (.of k))
  line_over : lineIso.hom ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = p
  conicIso : E ≅ (DvrNodal.conicIdeal (Spec (.of k))).subscheme
  conic_over : conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of k))).subschemeι ≫
    ProjectiveSpace (ULift.{u} (Fin 3)) (Spec (.of k)) ↘ Spec (.of k) = p
  smooth : Smooth p
  left_formula : ∃ hs : Ideal.span (Set.range
      (coordinateSections (Polynomial k) ![1, Polynomial.X, Polynomial.X ^ 2])) = ⊤,
    C.left ≫ conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of k))).subschemeι =
      ProjectiveSpace.homOfSections (Spec.map (CommRingCat.ofHom Polynomial.C))
        (coordinateSections (Polynomial k) ![1, Polynomial.X, Polynomial.X ^ 2]) hs
  middle_formula : ∃ hs : Ideal.span (Set.range
      (coordinateSections (middleRing k ε) ![middleCoord k ε 0, 1, middleCoord k ε 1])) = ⊤,
    C.middle ≫ conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of k))).subschemeι =
      ProjectiveSpace.homOfSections
        (Spec.map (CommRingCat.ofHom (middleConstants k ε)))
        (coordinateSections (middleRing k ε) ![middleCoord k ε 0, 1, middleCoord k ε 1]) hs
  right_formula : ∃ hs : Ideal.span (Set.range
      (coordinateSections (Polynomial k) ![Polynomial.X ^ 2, Polynomial.X, 1])) = ⊤,
    C.right ≫ conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of k))).subschemeι =
      ProjectiveSpace.homOfSections (Spec.map (CommRingCat.ofHom Polynomial.C))
        (coordinateSections (Polynomial k) ![Polynomial.X ^ 2, Polynomial.X, 1]) hs
  left_image : Set.range C.left =
    (conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of k))).subschemeι) ⁻¹'
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) (Spec (.of k)) ⟨0⟩ : Set _)
  right_image : Set.range C.right =
    (conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of k))).subschemeι) ⁻¹'
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) (Spec (.of k)) ⟨2⟩ : Set _)
  outer_cover : Set.range C.left ∪ Set.range C.right = Set.univ

/-- The two projective-line components with their actual axis charts, origin, and cartesian
intersection. The origin lies in the specified affine neighbourhood `Spec k[r,s]/(rs)`;
this also fixes the local equation, rather than only the topology of the intersection.
Source: node proof steps 6--9, following Stacks 0804, 01QO and 01I4
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
structure NodalData (k : Type u) [Field k] (ε : Fin 2)
    (E : Scheme.{u}) (p : E ⟶ Spec (.of k)) (C : Charts k ε E p) where
  reduced : IsReduced E
  rLine : ProjectiveLine (Spec (.of k)) ⟶ E
  sLine : ProjectiveLine (Spec (.of k)) ⟶ E
  r_closed : IsClosedImmersion rLine
  s_closed : IsClosedImmersion sLine
  r_over : rLine ≫ p = ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)
  s_over : sLine ≫ p = ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)
  components : irreducibleComponents E = {Set.range rLine, Set.range sLine}
  distinct : Set.range rLine ≠ Set.range sLine
  r_axis : ∃ (f : middleRing k ε →+* Polynomial k)
      (a : Spec (.of (Polynomial k)) ⟶ ProjectiveLine (Spec (.of k))),
    f.comp (middleConstants k ε) = Polynomial.C ∧
    f (middleCoord k ε 0) = Polynomial.X ∧ f (middleCoord k ε 1) = 0 ∧
    IsPullback (Spec.map (CommRingCat.ofHom f)) a C.middle rLine
  s_axis : ∃ (f : middleRing k ε →+* Polynomial k)
      (a : Spec (.of (Polynomial k)) ⟶ ProjectiveLine (Spec (.of k))),
    f.comp (middleConstants k ε) = Polynomial.C ∧
    f (middleCoord k ε 0) = 0 ∧ f (middleCoord k ε 1) = Polynomial.X ∧
    IsPullback (Spec.map (CommRingCat.ofHom f)) a C.middle sLine
  r_completion : Set.range C.left ⊆ Set.range rLine
  s_completion : Set.range C.right ⊆ Set.range sLine
  r_avoids_right : Disjoint (Set.range rLine) (Set.range C.right)
  s_avoids_left : Disjoint (Set.range sLine) (Set.range C.left)
  rOrigin : Spec (.of k) ⟶ ProjectiveLine (Spec (.of k))
  sOrigin : Spec (.of k) ⟶ ProjectiveLine (Spec (.of k))
  rOrigin_over : rOrigin ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _
  sOrigin_over : sOrigin ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _
  intersection : IsPullback rOrigin sOrigin rLine sLine
  origin : ∃ f : middleRing k ε →+* k,
    f.comp (middleConstants k ε) = RingHom.id k ∧
    f (middleCoord k ε 0) = 0 ∧ f (middleCoord k ε 1) = 0 ∧
    rOrigin ≫ rLine = Spec.map (CommRingCat.ofHom f) ≫ C.middle

/-- Both alternatives, retaining witnesses for the coefficient-extension comparison.
Source: node proof steps 2--9 (blueprint: lem-sfb-three-chart-exceptional-curve). -/
structure Description (k : Type u) [Field k] (ε : Fin 2)
    (E : Scheme.{u}) (p : E ⟶ Spec (.of k)) (C : Charts k ε E p) where
  conic : ε = 1 → ConicData k ε E p C
  nodal : ε = 0 → NodalData k ε E p C

/-- Coefficient extension of the chart presentation and of the chosen conic, components and
intersection. The middle ring map is uniquely specified on constants and both coordinates;
the other two maps are `Polynomial.map`. The compatibility equations use the actual
projective-space base-change morphisms, including on the two intersection sections.
Source: node proof step 10, following Stacks 01I4 and 01JY
(blueprint: lem-sfb-three-chart-exceptional-curve). -/
def CompatibleExtension (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ε : Fin 2) (E : Scheme.{u}) (p : E ⟶ Spec (.of k))
    (C : Charts k ε E p) (d : Description k ε E p C)
    (C' : Charts K ε (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (d' : Description K ε _ _ C') : Prop :=
  (C'.left ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K))) ≫ C.left) ∧
  (C'.right ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K))) ≫ C.right) ∧
  (∃ f : middleRing k ε →+* middleRing K ε,
    f.comp (middleConstants k ε) = (middleConstants K ε).comp (algebraMap k K) ∧
    (∀ i : Fin 2, f (middleCoord k ε i) = middleCoord K ε i) ∧
    C'.middle ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom f) ≫ C.middle) ∧
  (∀ h : ε = 1,
    (d'.conic h).lineIso.hom ≫ ProjectiveSpace.map (ULift.{u} (Fin 2))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        (d.conic h).lineIso.hom ∧
    ((d'.conic h).conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of K))).subschemeι) ≫
        ProjectiveSpace.map (ULift.{u} (Fin 3))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        (d.conic h).conicIso.hom ≫ (DvrNodal.conicIdeal (Spec (.of k))).subschemeι) ∧
  (∀ h : ε = 0,
    (d'.nodal h).rLine ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      ProjectiveSpace.map (ULift.{u} (Fin 2))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ (d.nodal h).rLine ∧
    (d'.nodal h).sLine ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      ProjectiveSpace.map (ULift.{u} (Fin 2))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ (d.nodal h).sLine ∧
    (d'.nodal h).rOrigin ≫ ProjectiveSpace.map (ULift.{u} (Fin 2))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ (d.nodal h).rOrigin ∧
    (d'.nodal h).sOrigin ≫ ProjectiveSpace.map (ULift.{u} (Fin 2))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ (d.nodal h).sOrigin)

/-- **Reciprocal gluing of the exceptional conic and pair of lines.**
Source: literature/stacks-project/divisors.tex, explicit exceptional-curve calculation
extracted from inherited steps 11--12, following Tag 0804
(blueprint: lem-sfb-three-chart-exceptional-curve).

Proof, following the ten DAG steps:
1. The principal localizations of `rs=ε` give the displayed substitutions and cartesian
   intersections (lem-weil-pbc-affine-open-section-vanishing-prime and
   lem-weil-pbc-glue-schemes); these are exactly the overlaps in `C`.
2. For `ε=1` the outer charts cover and have the standard reciprocal transition, so their
   identities glue to the projective-line isomorphism (def-sc-p1-standard and
   lem-weil-pbc-scheme-morphism-gluing).
3. On the conic, a homogeneous prime containing `X,Y` contains `P²` and hence `P`, so
   `D₊(X),D₊(Y)` cover even in characteristic two. Their rings are `k[t],k[h]` with
   `Y/X=(P/X)²`, `X/Y=(P/Y)²` (prop-nagata-proj-standard-open and
   def-nagata-homogeneous-localization-degree-zero).
4. Glue these affine identifications to the conic isomorphism. On the middle chart its
   coordinates are `[r:1:s]`; on the outer charts they are `[1:t:t²]`, `[h²:h:1]`
   (lem-weil-pbc-scheme-morphism-gluing).
5. Smoothness follows on the two affine-line charts (sbc-lem-affine-space-smooth and
   lem-weil-pbc-smooth-local-on-source).
6. For `ε=0`, complete each axis with its corresponding outer line. The quotient maps
   `s↦0`, `r↦0` give closed immersions by the affine and target-local criteria
   (lem-weil-pbc-closed-finite-etale-zariski-local).
7. Normal forms `c+rf(r)+sg(s)` embed the middle ring in `k[r]×k[s]`, so it is reduced;
   apply lem-weil-pbc-polynomial-ring-domain, lem-weil-pbc-affine-scheme-reduced-iff
   and lem-trf-reduced-scheme-open-cover.
8. Every prime contains `r` or `s`. The two closed irreducible projective lines cover,
   neither contains the other, hence they are exactly the two irreducible components.
9. Their intersection has ring `A/(s) ⊗[A] A/(r)=A/(r,s)=k`, with its specified origin
   and ambient local equation `rs=0` (lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-spec-domain-stalks-function-field).
10. After any field extension the affine fibre products have the coefficient-extended
    chart rings. All substitutions, conic maps, axis quotients and origin maps commute
    on generators, proving the asserted compatibility (lem-weil-pbc-open-immersion-base-change,
    lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-scheme-morphism-gluing).
-/
theorem reciprocal_gluing_exceptional_curve (k : Type u) [Field k] (ε : Fin 2)
    (E : Scheme.{u}) (p : E ⟶ Spec (.of k)) (C : Charts k ε E p) :
    ∃ d : Description k ε E p C,
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∃ C' : Charts K ε (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
          ∃ d' : Description K ε _ _ C', CompatibleExtension k K ε E p C d C' d' := by
  sorry

end AlgebraicGeometry.ThreeChartExceptional
