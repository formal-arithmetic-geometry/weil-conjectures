/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteRestrictionCoefficientDescentData

/-! # Rational assembly of finite coefficient restrictions

Source: Bhatt--Scholze 6.8.14 and Remark 6.8.15; BBD 1.3.6
(blueprint: lem-zl-finite-restriction-rational-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteRestrictionCoefficient
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage integralTransition transition stageSystem)
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Raw rationalization and exact-heart descent of coherent integral comparisons.

Source: Bhatt--Scholze 6.8.14(1),(2), Remark 6.8.15; BBD 1.3.6;
steps 5, 6, and 8 of finite restriction coefficient descent
(blueprint: lem-zl-finite-restriction-rational-assembly).

Proof:
1. The three actual integral functors are additive and coefficient-linear.
Localize their maps and both actual natural transformations by tensoring with
scalars. The raw rational transport construction has unchanged objects and sends
a tensor g to a tensor the image of g. Localizing the integral comparison maps
and their identity/tower equations gives the scalar comparisons. Their components
are precisely the localized beta components, as required by RationalComparisons.
2. Laws gives the two compatible transformation squares; Coherent gives the
stage-system Morphism coherence. Descend each functor and compatible transformation
by the representative quotient. This keeps the prescribed rational exchange and
restriction components and does not introduce idempotent splittings.
3. Use G.Normalized's rational direct-image comparisons. Take Phi to be
G.rationalImage.rational and beta to be the inverse theta. Its tower equation is
the inverse of the recorded rational theta equation, so it is a Morphism of the
prescribed stage systems. Thus both its Phi and beta normalizations are retained.
4. The integral functors and their rationalizations are exact with their canonical
shift comparisons. Represent distinguished triangles at finite stages and apply
those exact functors there. The endpoint scalar normalization identifies beta with
the canonical geometric comparisons; these commute with the normalized shifts,
so the descended functors are exact. If all stages preserve both standard halves,
represent an object in a half at one stage and apply the inclusion comparison.
This proves t-exactness of the descended functors.
5. Restrict to the intersection of the two halves, with the literal object and
arrow formulas of the full-subcategory lift. It is additive. By the heart
short-exact-triangle criterion, a short exact heart sequence is a distinguished
triangle. Exactness carries it to a distinguished triangle; t-exactness keeps all
terms in the heart, so its image sequence is short exact. Apply this to the three
rationalized functors and the normalized direct image. No t-exactness is assumed
without the conditional hypothesis in HeartExactDescent. -/
theorem finiteRestrictionRationalAssembly
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y)
    (G : Geometry l Ω f y) (I : IntegralComparisons l f y Ω)
    (N : Endpoints l Ω f y G I)
    (hG : G.Normalized) (hI : I.Laws) (hcI : I.Coherent) (hN : N.ScalarNormalized) :
    ∃ R : RationalComparisons l f y Ω I,
      DirectImageDescent l f y Ω G ∧
        ∀ q : Vertex, HeartExactDescent l Ω X (R.diagram q) := by sorry

end WeilConjectures.FiniteRestrictionCoefficient
