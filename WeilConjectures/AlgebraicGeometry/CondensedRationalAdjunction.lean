/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom
public import WeilConjectures.AlgebraicGeometry.TransportIntegralCounitRealization
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.RationalizedSmoothAdjunctionDiagrams
import WeilConjectures.Algebra.Homology.OrdinaryLineDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints

/-! # The native condensed rational purity adjunction

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-rational,
sk-prop-sp-rational-adjunction.md, (1)--(2)
(blueprint: prop-pur-condensed-rational-adjunction).

The integral adjunction is an input, supplied by the integral counit realization.
Every rational functor below acts on the native condensed finite-Tor category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRationalAdjunction

/-- Bundle the actual inclusion of continuous integral coefficients into E.
Source: rational-adjunction (1), scalar extension
(blueprint: prop-pur-condensed-rational-adjunction). -/
def coefficientMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    (Coefficient.integral E).bundled.{u} ell ⟶ (Coefficient.rational E).bundled ell :=
  CommMon.homMk (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E))

/-- Restrict the prescribed total derived scalar extension using only a membership proof.
Source: rational-adjunction (1), Q_T
(blueprint: prop-pur-condensed-rational-adjunction). -/
def extend (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (T : Scheme.{u})
    (h : ∀ K, property ell (.integral E) T K → property ell (.rational E) T
      ((scalarSixChange (coefficientMap ell E) T).obj K)) :
    (Coefficient.integral E).ctf ell T ⥤ (Coefficient.rational E).ctf ell T :=
  (property ell (.rational E) T).lift
    ((property ell (.integral E) T).ι ⋙ scalarSixChange (coefficientMap ell E) T)
    (fun K ↦ h K.obj K.property)

/-- Scalar multiplication is the canonical continuous-coefficient Hom action, restricted
along the full inclusion. Source: rational-localized-hom, pure-tensor formula
(blueprint: prop-pur-condensed-rational-adjunction). -/
def scale (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (T : Scheme.{u}) {K L : (Coefficient.rational E).ctf ell T}
    (e : E.1) (h : K ⟶ L) : K ⟶ L :=
  ObjectProperty.homMk (@SMul.smul E.1 (K.obj ⟶ L.obj)
    (RationalLocalizedHom.rationalHomModule T ell E K.obj L.obj).toSMul e h.hom)

/-- The two endpoint comparisons with the prescribed ambient normalizations.
Their fields contain actual isomorphisms; the normalization fields fix their maps.
Source: rational-adjunction (1), the comparisons a and b
(blueprint: prop-pur-condensed-rational-adjunction). -/
structure Comparisons (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D)
    (A₀ : ExplicitAdjunction ell D (.integral E) s)
    (A : ExplicitAdjunction ell D (.rational E) s)
    (hX : ∀ K, property ell (.integral E) s.X.left K → property ell (.rational E) s.X.left
      ((scalarSixChange (coefficientMap ell E) s.X.left).obj K))
    (hY : ∀ K, property ell (.integral E) s.Y.left K → property ell (.rational E) s.Y.left
      ((scalarSixChange (coefficientMap ell E) s.Y.left).obj K)) where
  coefficient_normalization :
    (Coefficient.integral E).integralMap ell ≫ (coefficientMap ell E).hom.hom =
      (Coefficient.rational E).integralMap ell
  line : ScalarLineCoordinates ell (coefficientMap ell E) coefficient_normalization s.X.left
  b : support ell (.integral E) s.compactification A₀.support_closed ⋙ extend ell E s.Y.left hY ≅
    extend ell E s.X.left hX ⋙ support ell (.rational E) s.compactification A.support_closed
  a : source ell (.integral E) s.map s.dim A₀.source_closed ⋙ extend ell E s.X.left hX ≅
    extend ell E s.Y.left hY ⋙ source ell (.rational E) s.map s.dim A.source_closed
  b_normalized : ∀ M : (Coefficient.integral E).ctf ell s.X.left,
    (b.hom.app M).hom = (scalarSupportMap (coefficientMap ell E) s.compactification).app M.obj
  a_normalized : ∀ K : (Coefficient.integral E).ctf ell s.Y.left,
    (a.hom.app K).hom =
      sourceScalar ell (coefficientMap ell E) s.map s.dim coefficient_normalization line K.obj

/-- All clauses of the rational adjunction, on the actual condensed categories.
The pure-tensor equation holds for every pair of models and every identification.
Together with additivity and E-linearity, it uniquely specifies the displayed tensor
Hom composite and its independence of choices. Source: rational-adjunction (1)--(2)
(blueprint: prop-pur-condensed-rational-adjunction). -/
structure Laws (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D)
    (A₀ : ExplicitAdjunction ell D (.integral E) s)
    (A : ExplicitAdjunction ell D (.rational E) s)
    (hX : ∀ K, property ell (.integral E) s.X.left K → property ell (.rational E) s.X.left
      ((scalarSixChange (coefficientMap ell E) s.X.left).obj K))
    (hY : ∀ K, property ell (.integral E) s.Y.left K → property ell (.rational E) s.Y.left
      ((scalarSixChange (coefficientMap ell E) s.Y.left).obj K))
    (c : Comparisons ell D E s A₀ A hX hY) : Prop where
  modelsX : ∀ M : (Coefficient.rational E).ctf ell s.X.left,
    ∃ M₀ : (Coefficient.integral E).ctf ell s.X.left,
      Nonempty ((extend ell E s.X.left hX).obj M₀ ≅ M)
  modelsY : ∀ K : (Coefficient.rational E).ctf ell s.Y.left,
    ∃ K₀ : (Coefficient.integral E).ctf ell s.Y.left,
      Nonempty ((extend ell E s.Y.left hY).obj K₀ ≅ K)
  hom_add : ∀ (M : (Coefficient.rational E).ctf ell s.X.left)
    (K : (Coefficient.rational E).ctf ell s.Y.left)
    (z z' : (support ell (.rational E) s.compactification A.support_closed).obj M ⟶ K),
    A.adjunction.homEquiv M K (z + z') =
      A.adjunction.homEquiv M K z + A.adjunction.homEquiv M K z'
  hom_smul : ∀ (M : (Coefficient.rational E).ctf ell s.X.left)
    (K : (Coefficient.rational E).ctf ell s.Y.left)
    (z : (support ell (.rational E) s.compactification A.support_closed).obj M ⟶ K)
    (e : E.1),
    A.adjunction.homEquiv M K (scale ell E s.Y.left e z) =
      scale ell E s.X.left e (A.adjunction.homEquiv M K z)
  model_formula : ∀ (M₀ : (Coefficient.integral E).ctf ell s.X.left)
    (K₀ : (Coefficient.integral E).ctf ell s.Y.left)
    (M : (Coefficient.rational E).ctf ell s.X.left)
    (K : (Coefficient.rational E).ctf ell s.Y.left)
    (i : (extend ell E s.X.left hX).obj M₀ ≅ M)
    (j : (extend ell E s.Y.left hY).obj K₀ ≅ K)
    (h : (support ell (.integral E) s.compactification A₀.support_closed).obj M₀ ⟶ K₀)
    (e : E.1),
    A.adjunction.homEquiv M K
      ((support ell (.rational E) s.compactification A.support_closed).map i.inv ≫
        c.b.inv.app M₀ ≫ scale ell E s.Y.left e ((extend ell E s.Y.left hY).map h) ≫ j.hom) =
      i.inv ≫ scale ell E s.X.left e
        ((extend ell E s.X.left hX).map (A₀.adjunction.homEquiv M₀ K₀ h)) ≫
        c.a.hom.app K₀ ≫ (source ell (.rational E) s.map s.dim A.source_closed).map j.hom
  unit : ∀ M₀ : (Coefficient.integral E).ctf ell s.X.left,
    A.adjunction.unit.app ((extend ell E s.X.left hX).obj M₀) =
      (extend ell E s.X.left hX).map (A₀.adjunction.unit.app M₀) ≫
        c.a.hom.app _ ≫ (source ell (.rational E) s.map s.dim A.source_closed).map
          (c.b.hom.app M₀)
  counit : ∀ K₀ : (Coefficient.integral E).ctf ell s.Y.left,
    c.b.hom.app _ ≫ (support ell (.rational E) s.compactification A.support_closed).map
        (c.a.hom.app K₀) ≫ A.adjunction.counit.app ((extend ell E s.Y.left hY).obj K₀) =
      (extend ell E s.Y.left hY).map (A₀.adjunction.counit.app K₀)
  brown : ∀ (G : (Coefficient.rational E).ctf ell s.Y.left ⥤
      (Coefficient.rational E).ctf ell s.X.left)
    (adj : support ell (.rational E) s.compactification A.support_closed ⊣ G),
    ∃! gamma : source ell (.rational E) s.map s.dim A.source_closed ≅ G,
      ∀ K, (support ell (.rational E) s.compactification A.support_closed).map
        (gamma.hom.app K) ≫ adj.counit.app K = A.adjunction.counit.app K

/-- Rationalize the supplied integral purity adjunction with its specified counit.
Source: latest blueprint, rational-adjunction (1)--(2)
(blueprint: prop-pur-condensed-rational-adjunction).

Proof. 1. Integral counit realization supplies A₀; integral linearity is the first
assertion of rationalized-smooth-adjunction-diagrams. Existence identifies the
nonfinite Dctf categories with Dbc and supplies the specified Brown adjunction.
2. Rational-localized-hom gives integral models, the Hom maps h tensor e to e Q(h),
and the actual compact-support and pullback comparisons. Commute scalar extension
past the native Tate line using ordinary-line-derived-scalar-comparison and past
shift 2d using derived-tensor-additive-constraints. These give exactly b and a.
3. On model objects compose rhoY inverse, the integral linear Hom equivalence
tensored with E, and rhoX, followed by a. This proves the pure-tensor formula.
4. Naturality for integral maps follows from the four natural comparisons. Write
every rational map as a finite sum of e Q(h). Write e=c ell^(-n) and use additivity
and invertibility of ell to extend naturality to those actual rational maps.
5. For arbitrary identifications i,j conjugate the model bijection by i inverse
and J(j). For a second choice use u=i inverse i' and v=j' inverse j; rational
naturality cancels these factors. Thus the bijection is independent of all models.
6. Adjunction.mkOfHomEquiv constructs the same adjunction from these natural
bijections. Its Hom equivalence is additive and E-linear.
7. Evaluate the bijection and its inverse at identities to obtain the two stated
unit and counit equations, retaining the realized integral counit normalization.
8. Compare this adjunction with the specified Brown adjunction by rightAdjointUniq.
Its transpose formula yields the unique natural isomorphism gamma with
F(gamma) followed by the Brown counit equal to this same rational counit. -/
theorem condensed_rational_adjunction (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (_hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D)
    (A₀ : ExplicitAdjunction ell D (.integral E) s) :
    ∃ (hX : ∀ K, property ell (.integral E) s.X.left K → property ell (.rational E) s.X.left
        ((scalarSixChange (coefficientMap ell E) s.X.left).obj K))
      (hY : ∀ K, property ell (.integral E) s.Y.left K → property ell (.rational E) s.Y.left
        ((scalarSixChange (coefficientMap ell E) s.Y.left).obj K))
      (A : ExplicitAdjunction ell D (.rational E) s)
      (c : Comparisons ell D E s A₀ A hX hY),
      Laws ell D E s A₀ A hX hY c := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRationalAdjunction
