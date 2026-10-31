/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.Transport
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.SixFunctors.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
import WeilConjectures.AlgebraicGeometry.TateTwistLocallyFree
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteLocalizingExceptionalPreservation

/-! # Purity, counit and smooth trace under change of condensed coefficients

Source: latest blueprint, sk-thm-purity-transport-coefficient-change, clauses (1)--(3)
and its proof, including the uniformizer-reduction sentence.
(blueprint: lem-pur-condensed-purity-coefficient-change).

The family in the conclusion is the normalized family of sk-thm-purity-transport.
Its Brown comparison is computed by rightAdjointUniq; its exceptional scalar map
is the published scalarExceptionalBeta, not a freely chosen isomorphism.
The auxiliary predicates spell out the equations on the full Dctf subcategories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityCoefficientChange
open PurityTransport

/-- The characteristic already determined by the finite-field datum.
Source: standing finite-field setting
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
instance fieldChar (D : WeilConjectures.FiniteFieldDatum.{u}) : CharP D.k D.p := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite _
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  exact charP_of_injective_algebraMap' D.k₀ D.p

/-- The prime-characteristic instance supplied to the existing scalar-six interface.
Source: standing setting (blueprint: lem-pur-condensed-purity-coefficient-change). -/
instance fieldPrime (D : WeilConjectures.FiniteFieldDatum.{u}) : Fact (ringChar D.k).Prime :=
  letI := fieldChar D
  ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩

/-- The distinct-characteristic instance, with no additional field hypothesis.
Source: standing setting (blueprint: lem-pur-condensed-purity-coefficient-change). -/
abbrev fieldDifferent (ell : ℕ) (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) : Fact (ringChar D.k ≠ ell) :=
  letI := fieldChar D
  ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩

variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  (hEll : ell ≠ D.p)

/-- The published scalar functor on Dctf, with its automatic field hypotheses supplied.
Source: scalar-six exceptional comparison
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def change {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : ListedScalarChange ell a) (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    c.ctf ell X.left ⥤ c'.ctf ell X.left :=
  letI := fieldPrime D
  letI := fieldDifferent ell D hEll
  ScalarMaps.scalarExceptionalChange ell D.k a ha X

/-- The canonical exceptional transpose of the proper/open support comparison.
Source: displayed definition of c in the node and det-prop-scalar-six-exceptional
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def exceptionalMap {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (ha : ListedScalarChange ell a)
    (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
    (S : ScalarExceptionalAdjoint (c'.bundled ell) s.compactification) :
    R.upper ⋙ change ell D hEll a ha s.X ⟶
      change ell D hEll a ha s.Y ⋙ S.upper :=
  letI := fieldPrime D
  letI := fieldDifferent ell D hEll
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  ScalarMaps.scalarExceptionalBeta (ell := ell) (k := D.k)
    (hcd := BaseFieldFiniteCD.of_isAlgClosed ell D.k) (a := a) (ha := ha)
    (X := s.X) (Y := s.Y) (f := s.map.asOver (Spec (.of D.k)))
    (c := s.compactification) (R := R) (S := S)

/-- The counit-preserving purity comparison with a specified Brown restriction.
Source: sk-thm-purity-transport and det-sp-unique-right-adjoint
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def gamma (A : AdjunctionFamily ell D) (c : Coefficient ell) (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification) :
    source ell c s.map s.dim (A c s).source_closed ≅ R.upper :=
  (A c s).adjunction.rightAdjointUniq R.restrictedAdjunction

/-- The trace epsilon F(gamma), as an arrow of the ambient derived category.
Source: displayed definition of Tr (blueprint: lem-pur-condensed-purity-coefficient-change). -/
def trace (A : AdjunctionFamily ell D) (c : Coefficient ell) (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
    (K : c.ctf ell s.Y.left) :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).map
    ((gamma ell D A c s R).hom.app K).hom ≫ R.counit K

/-- The coefficient unit isomorphism, derived from the ordinary multiplication map.
Source: identity coefficient changes
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def scalarUnit (c : Coefficient ell) (X : Scheme.{u}) :
    scalarSixChange (𝟙 (c.bundled ell)) X ≅ 𝟭 (c.derived ell X) :=
  scalarChangeUnit (c.bundled ell) X

/-- Normalized Tate coefficient coordinates for every allowed map. The integral
compatibility is an equality of the actual ring morphisms. Every line comparison
is fixed by scalar association and balanced tensor powers in ScalarLineCoordinates.
Source: proof Steps 7--9 (blueprint: lem-pur-condensed-purity-coefficient-change). -/
structure Coordinates where
  integral : ∀ {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell), ListedScalarChange ell a →
    c.integralMap ell ≫ a.hom.hom = c'.integralMap ell
  line : ∀ {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (ha : ListedScalarChange ell a)
    (X : Scheme.{u}), ScalarLineCoordinates ell a (integral a ha) X

/-- The specified pullback, twist and shift comparison s.
Source: definition of s and proof Step 7
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def sourceMap (P : Coordinates.{u} ell) {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (ha : ListedScalarChange ell a)
    (s : SmoothDatum D) (K : c.derived ell s.Y.left) :=
  sourceScalar ell a s.map s.dim (P.integral a ha) (P.line a ha s.X.left) K

/-- All three displayed equations, with the published b and c and the normalized s.
The source comparison is natural on Dctf; the other maps are already natural
transformations by their definitions.
Source: the three displayed equations and naturality sentence
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def Equations (A : AdjunctionFamily ell D) (P : Coordinates.{u} ell) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : ListedScalarChange ell a) (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
    (S : ScalarExceptionalAdjoint (c'.bundled ell) s.compactification),
    (∀ K : c.ctf ell s.Y.left,
      IsIso (sourceMap ell D P a ha s K.obj) ∧
      (scalarSixChange a s.X.left).map ((gamma ell D A c s R).hom.app K).hom ≫
          ((exceptionalMap ell D hEll a ha s R S).app K).hom =
        sourceMap ell D P a ha s K.obj ≫
          ((gamma ell D A c' s S).hom.app ((change ell D hEll a ha s.Y).obj K)).hom ∧
      (scalarSixChange a s.Y.left).map (R.counit K) =
        (scalarCompactSupportMap a s.compactification.i s.compactification.g).app
            (R.upper.obj K).obj ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
              ((exceptionalMap ell D hEll a ha s R S).app K).hom ≫
          S.counit ((change ell D hEll a ha s.Y).obj K) ∧
      (scalarSixChange a s.Y.left).map (trace ell D A c s R K) =
        (scalarCompactSupportMap a s.compactification.i s.compactification.g).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map (sourceMap ell D P a ha s K.obj) ≫
          trace ell D A c' s S ((change ell D hEll a ha s.Y).obj K)) ∧
    ∀ (K L : c.ctf ell s.Y.left) (v : K ⟶ L),
      (scalarSixChange a s.X.left).map ((c.smoothSource ell s.map s.dim).map v.hom) ≫
          sourceMap ell D P a ha s L.obj =
        sourceMap ell D P a ha s K.obj ≫
          (c'.smoothSource ell s.map s.dim).map ((scalarSixChange a s.Y.left).map v.hom)

/-- Multiplication by q^d on the existing Tate line.
Source: canonical Tate scalar normalization
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def powerScalar (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    End (c.line.{u} ell X d) :=
  (D.q ^ d) • (𝟙 (c.line.{u} ell X d))

/-- Multiplication by q^(-d) on the actual Tate line. Ring.inverse of the
q^d-multiplication endomorphism is its canonical unit inverse. Invertibility is
asserted below, rather than supplied as an arbitrary Frobenius parameter.
Source: canonical tau_d normalization, proof Step 8
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def tau (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) : End (c.line.{u} ell X d) :=
  Ring.inverse (powerScalar ell D c X d)

/-- The scalar q^d is a unit on every coefficient Tate line.
Source: proof Step 8 (blueprint: lem-pur-condensed-purity-coefficient-change). -/
def TateUnitInvertible : Prop :=
  ∀ (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ), IsIso (powerScalar ell D c X d)

/-- The actual shifted derived Tate datum used in the source comparison.
Source: proof Step 8 (blueprint: lem-pur-condensed-purity-coefficient-change). -/
def derivedTau (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    End (c.derivedLine ell X d) :=
  (shiftFunctor _ (2 * (d : ℤ))).map
    ((DerivedCategory.singleFunctor _ 0).map (tau ell D c X d))

/-- The specified balanced, shifted Tate comparison intertwines the canonical datum.
Source: proof Steps 7--8 (blueprint: lem-pur-condensed-purity-coefficient-change). -/
def TateScalarFrobenius (P : Coordinates.{u} ell) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : ListedScalarChange ell a) (X : Scheme.{u}) (d : ℕ),
    (scalarSixChange a X).map (derivedTau ell D c X d) ≫
        scalarLineMap ell a X d ((P.line a ha X).power d) =
      scalarLineMap ell a X d ((P.line a ha X).power d) ≫ derivedTau ell D c' X d

/-- Every root-normalized pullback comparison intertwines the same datum.
Source: Tate pullback sentence, proof Steps 7--8
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def TatePullbackFrobenius : Prop :=
  ∀ (c : Coefficient ell) (X Y : Scheme.{u}) (f : X ⟶ Y)
    (p : LinePullCoordinates ell c f) (d : ℕ),
    (CondensedRing.upperStar (c.obj ell) f).map (tau ell D c Y d) ≫ (p.power d).hom =
      (p.power d).hom ≫ tau ell D c X d

/-- The Tate comparison preserves q^(-d), including its pullback identifications,
zero tensor power, integral coefficients and nonflat finite reduction.
Source: Tate Frobenius sentence, proof Steps 7--8
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def FrobeniusCompatible (P : Coordinates.{u} ell) : Prop :=
  TateUnitInvertible ell D ∧ TateScalarFrobenius ell D P ∧ TatePullbackFrobenius ell D

/-- Successive source and support comparisons use the native derived scalar
associators. In particular direct uniformizer reduction and reduction through
any ell-power quotient are the same maps under this associator.
Source: composition and ramified-reduction sentences, proof Step 9
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def CompositionCoherent (P : Coordinates.{u} ell) : Prop :=
  ∀ (c c' c'' : Coefficient ell)
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (b : c'.bundled.{u} ell ⟶ c''.bundled ell)
    (ha : ListedScalarChange ell a) (hb : ListedScalarChange ell b)
    (s : SmoothDatum D),
    (∀ K : c.ctf ell s.Y.left,
      (scalarSixTower a b s.X.left).hom.app ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          sourceMap ell D P (a ≫ b) (.comp a b ha hb) s K.obj =
        (scalarSixChange b s.X.left).map (sourceMap ell D P a ha s K.obj) ≫
          sourceMap ell D P b hb s ((scalarSixChange a s.Y.left).obj K.obj) ≫
          (c''.smoothSource ell s.map s.dim).map
            ((scalarSixTower a b s.Y.left).hom.app K.obj)) ∧
    (∀ M : c.ctf ell s.X.left,
      (scalarSixChange b s.Y.left).map
          ((scalarCompactSupportMap a s.compactification.i s.compactification.g).app M.obj) ≫
        (scalarCompactSupportMap b s.compactification.i s.compactification.g).app
          ((scalarSixChange a s.X.left).obj M.obj) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (c''.obj ell) s.compactification).map
          ((scalarSixTower a b s.X.left).hom.app M.obj) =
      (scalarSixTower a b s.Y.left).hom.app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s.compactification).obj M.obj) ≫
        (scalarCompactSupportMap (a ≫ b) s.compactification.i s.compactification.g).app M.obj) ∧
    ∀ (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
      (S : ScalarExceptionalAdjoint (c'.bundled ell) s.compactification)
      (U : ScalarExceptionalAdjoint (c''.bundled ell) s.compactification)
      (K : c.ctf ell s.Y.left),
      (scalarSixChange b s.X.left).map
          ((exceptionalMap ell D hEll a ha s R S).app K).hom ≫
        ((exceptionalMap ell D hEll b hb s S U).app
          ((change ell D hEll a ha s.Y).obj K)).hom ≫
        (U.upper.map (ObjectProperty.homMk ((scalarSixTower a b s.Y.left).hom.app K.obj))).hom =
      (scalarSixTower a b s.X.left).hom.app (R.upper.obj K).obj ≫
        ((exceptionalMap ell D hEll (a ≫ b) (.comp a b ha hb) s R U).app K).hom

/-- Every existing purity coefficient is an admissible localizing coefficient.
This certificate only supplies the empty coefficient change; its ring and topology
are the existing Coefficient.obj, independently of the site universe.
Source: standing coefficient list
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
abbrev coefficientAdmissible (c : Coefficient ell) :
    IsLocalizingAdmissibleCoefficient ell (c.obj.{u} ell) := by
  cases c with
  | finite A fin n hA =>
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := discreteTopology_bot A
    exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      fin, ⟨n + 1, fun x ↦ by simp only [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul]⟩, ⟨Iso.refl _⟩⟩
  | integers => exact Or.inr (Or.inl ⟨Iso.refl _⟩)
  | rationals => exact Or.inr (Or.inr (Or.inl ⟨Iso.refl _⟩))
  | integral E => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  | rational E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  | closure => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

/-- Identity source, support and exceptional comparisons are the scalar unitors.
Source: identity clause, proof Step 9
(blueprint: lem-pur-condensed-purity-coefficient-change). -/
def IdentityCoherent (P : Coordinates.{u} ell) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D),
    let hc : ListedScalarChange ell (𝟙 (c.bundled.{u} ell)) :=
      .identity _ (coefficientAdmissible ell c)
    (∀ K : c.ctf ell s.Y.left,
      sourceMap ell D P (𝟙 _) hc s K.obj ≫
          (c.smoothSource ell s.map s.dim).map ((scalarUnit ell c s.Y.left).hom.app K.obj) =
        (scalarUnit ell c s.X.left).hom.app ((c.smoothSource ell s.map s.dim).obj K.obj)) ∧
    (∀ M : c.ctf ell s.X.left,
      (scalarCompactSupportMap (𝟙 (c.bundled ell))
          s.compactification.i s.compactification.g).app M.obj ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).map ((scalarUnit ell c s.X.left).hom.app M.obj) =
      (scalarUnit ell c s.Y.left).hom.app
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).obj M.obj)) ∧
    ∀ (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
      (K : c.ctf ell s.Y.left),
      ((exceptionalMap ell D hEll (𝟙 _) hc s R R).app K).hom ≫
          (R.upper.map (ObjectProperty.homMk ((scalarUnit ell c s.Y.left).hom.app K.obj))).hom =
        (scalarUnit ell c s.X.left).hom.app (R.upper.obj K).obj

/-- The canonical purity family has the stated purity, counit and smooth-trace
coefficient equations, Tate Frobenius compatibility, and identity/composition laws.
The first five predicates retain exactly the normalization and geometric
compatibilities of the imported smooth_purity_transport family, so the gamma
appearing in Equations is the specified purity, not a new orientation.

Source: latest blueprint sk-thm-purity-transport-coefficient-change (1)--(3),
including ramified pi-power reduction
(blueprint: lem-pur-condensed-purity-coefficient-change).

Proof, following the accepted DAG split:
1. Transpose T(epsilon) b^(-1) using det-prop-scalar-six-exceptional. Its counit
identity gives the second displayed equation after precomposition by b.
2. The exact finite section-action equivalence transports the diagonal/DNC
adjunction of det-sp-finite-general-ring. Its counit is epsilon F(gamma).
Uniqueness of right adjoints identifies its orientation with the canonical one.
3. Apply det-sp-reduction-compatibilities to every finite ring map, without a
flatness assumption, and identify its b,c,s by their mates and balanced tensors.
4. For integral field extension use lem-pur-transport-integral-counit-realization;
identify the actual tower support and source maps by
lem-pur-native-transition-comparison-identification. Counit transposition then
identifies its exceptional comparison with the published c.
5. Apply prop-pur-condensed-purity-coefficient-change to quotient reduction,
localization, finite field extension and the algebraic closure. The same native
transition identification and counit uniqueness give the specified comparisons.
This includes every positive uniformizer quotient, also when E is ramified.
6. Apply functoriality and naturality of b to epsilon F(gamma), then substitute
the purity and counit equations, obtaining the displayed trace equation.
7. In the common compatible root frame, the Tate coefficient map sends
x tensor y to t(x)y; tensor powers, shifts, localization and common finite stages
preserve this formula. Cartesian pullback preserves the same frames.
8. Since q is a power of p distinct from ell, q is a coefficient unit. The
previous balanced map intertwines multiplication by q^(-d), as does pullback.
9. The native scalar associators identify both evaluations of iterated balanced
tensors; mates give the support and exceptional composition equations. The
identity maps are the scalar unitors. In particular O_E to O_E/ell^m to
O_E/pi_E^n agrees with direct reduction whenever ell^m lies in (pi_E^n).
The listed-map predicate supplies no reduction from E or the algebraic closure
to a finite ring. All equations take place in the ordinary uncompleted derived
categories, on their full bounded constructible finite-Tor subcategories. -/
theorem condensed_purity_coefficient_change :
    ∃ A : AdjunctionFamily ell D,
      BrownComparison ell D A ∧ ScalarCompatible ell D A ∧
      BaseChangeCompatible ell D A ∧ CompositionCompatible ell D hEll A ∧
      AffineNormalized ell D A ∧
      ∃ P : Coordinates.{u} ell,
        Equations ell D hEll A P ∧ FrobeniusCompatible ell D P ∧
        CompositionCoherent ell D hEll P ∧ IdentityCoherent ell D hEll P := by
  sorry

end AlgebraicGeometry.ProEtale.PurityCoefficientChange
