module
public import Sheaf.Paper.SixFunctorOrientationFamily
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.FiniteCoefficientSmoothPurity
public import Sheaf.Paper.AdicSmoothDualizingComplexes
public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.RationalSmoothPurityCanonical
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.Paper.FiniteTateScalarSourceNormalization
public import Sheaf.Paper.ExceptionalCoefficientComparison

/-! # The normalized smooth-purity orientation

Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (6) and the smooth part of (7).
(blueprint: lem-sf-purity-orientation-datum).

The finite normalization is expressed in faithful ordinary-etale coordinates.
Together with the integral reduction and field comparison fields of
`SfOrientationDatum`, it records the finite reduction equation and the canonical
smooth-purity map at each finite coefficient field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The exceptional-image comparison at the coefficient unit. It is the actual
comparison-adjunction unit, followed by the fixed intrinsic equivalence unit and
the published exceptional presentation. No endpoint isomorphism is chosen here.
Source: finite realization in clause (6)
(blueprint: lem-sf-purity-orientation-datum). -/
@[irreducible]
def sfPurityUnitExceptionalPresentation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  let U := Etale.ordinaryFiniteUnit P.Coefficient Y
  let V := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
  let W := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let R := (ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let H := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f
  let K := (sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (P.coefficientUnit Y)
  W.map (H.map
    ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} P.Coefficient) Y).unit.app U ≫
      R.map ((sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.hom.app (V.obj U)))) ≫
    (P.smoothPurityExceptionalComparison f).inv.app K

/-- Finite normalization is equality with smoothPurityMap at the coefficient unit.
The canonical source comparison is finiteUnitSource, the ordered-root comparison
is etalePowerComparison, and the exceptional-image comparison is the actual
comparison-adjunction unit. Quantification over hK only names the proof of the
coefficient unit's finite-Tor constructibility; it supplies no extra geometric data.
Source: clause (6), finite components
(blueprint: lem-sf-purity-orientation-datum). -/
def SfPurityFiniteNormalized (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (m : ℕ) (S : SixFunctorFiniteOperations D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m))) (O : SfFiniteOrientation S) : Prop :=
  ∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left),
    letI := c.hasCompactification
    letI : LocallyOfFiniteType X.obj.hom := X.property.1
    letI : QuasiCompact X.obj.hom := X.property.2
    letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
    letI : QuasiCompact Y.obj.hom := Y.property.2
    let P : PurityFiniteSetting :=
      { field := D, coefficients := C, extension := E,
        level := m + 1, level_pos := Nat.succ_le_succ (Nat.zero_le m) }
    ∀ hK : finiteTorConstructible C.l E (m + 1) (Nat.succ_pos m) Y.obj.left
        (P.coefficientUnit Y.obj.left),
      P.smoothPurityMap f.hom.left d (P.coefficientUnit Y.obj.left) hK =
        (RationalSmoothPurityCanonical.finiteUnitSource P f.hom.left d).hom ≫
          (sfIntrinsicDerivedEquivalence X.obj.left P.Ring).functor.map
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
              X.obj.left).mapDerivedCategory.map
                ((AdicSmoothDualizing.etalePowerComparison P X.obj.left
                    (P.diagonalExponent_isUnit X.obj.hom) d).hom ≫
                  ((O.etale m P.diagonalExponent_annihilates).component f d).hom ≫
                  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
                    f.hom.left).map
                      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient)
                        Y.obj.left).inv) ≫
              sfPurityUnitExceptionalPresentation P f.hom.left)

/-- Canonical finite transport from the small coefficient model back to L.val.
The forward and inverse maps are the quotient maps induced by Shrink.algEquiv
and its inverse on valuation rings. Their composites fix every quotient class.
Uniformizer ideals are transported, so the same index a is retained.
Source: clause (6), finite coefficient-field representatives
(blueprint: lem-sf-purity-orientation-datum). -/
@[irreducible]
def sfPurityCoefficientModelEquiv (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (L : Padic.FiniteCoefficientFields C.l C.Qbar) (a : ℕ) :
    finiteTateCoefficient C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) a ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing C.l L.val (a + 1)) := by
  let M := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L
  let e : M ≃ₐ[Padic C.l] L.val := Shrink.algEquiv (Padic C.l) L.val
  let F := integralScalarQuotientMap C.l M L.val e.toAlgHom a
  let G := integralScalarQuotientMap C.l L.val M e.symm.toAlgHom a
  let q : Padic.coefficientExtensionRing C.l M (a + 1) ≃+*
      Padic.coefficientExtensionRing C.l L.val (a + 1) :=
    { F with
      invFun := G
      left_inv := by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk _
          (integralScalarIntegerInclusion C.l L.val M e.symm.toAlgHom
            (integralScalarIntegerInclusion C.l M L.val e.toAlgHom x)) =
              Ideal.Quotient.mk _ x
        congr 1
        apply Subtype.ext
        exact e.symm_apply_apply x.val
      right_inv := by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk _
          (integralScalarIntegerInclusion C.l M L.val e.toAlgHom
            (integralScalarIntegerInclusion C.l L.val M e.symm.toAlgHom x)) =
              Ideal.Quotient.mk _ x
        congr 1
        apply Subtype.ext
        exact e.apply_symm_apply x.val }
  exact ULift.ringEquiv.trans (q.trans ULift.ringEquiv.symm)

/-- The scalar line comparison selected by its unique pure-root-tensor, unit and
power normalization. This uses the existing uniqueness theorem, rather than
choosing an arbitrary endpoint isomorphism.
Source: clause (6), canonical finite scalar transport
(blueprint: lem-sf-purity-orientation-datum). -/
@[irreducible]
def sfPurityFiniteScalarLine {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x)) :=
  (PurityFiniteSetting.finite_tate_scalar_source_normalization φ N hN hA hB X hX).2.exists.choose

/-- Each small-model finite component is the specified finite smooth-purity arrow.
The coefficient map is fixed by Shrink.algEquiv. The source map is the published
scalar/single/shift map with balancing fixed on every pure root tensor; the target
map is the published compact-support counit mate and its scalar unit. The equation
therefore compares actual arrows and constrains O.coefficientFinite L a. The
line comparison is the uniquely normalized scalar comparison, not a variable.
Source: clause (6), coefficient-field and common-stage components
(blueprint: lem-sf-purity-orientation-datum). -/
def SfPurityCoefficientFiniteNormalized (D : FiniteFieldDatum.{u})
    (C : D.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar)
    [FiniteDimensional (Padic C.l) E]
    (m : ℕ) (S : SixFunctorDatum D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m))) (O : SfOrientationDatum S)
    (L : Padic.FiniteCoefficientFields C.l C.Qbar) (a : ℕ) : Prop :=
  ∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left),
    letI := c.hasCompactification
    letI : LocallyOfFiniteType X.obj.hom := X.property.1
    letI : QuasiCompact X.obj.hom := X.property.2
    letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
    letI : QuasiCompact Y.obj.hom := Y.property.2
    let P : PurityFiniteSetting :=
      { field := D, coefficients := C, extension := L.val,
        level := a + 1, level_pos := Nat.succ_pos a }
    let A := finiteTateCoefficient C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) a
    let N := C.l ^ (a + 1)
    let hB : (N : P.Coefficient) = 0 := P.diagonalExponent_annihilates
    let e : A ≃+* P.Coefficient := sfPurityCoefficientModelEquiv D C L a
    let φ : A →+* P.Coefficient := e.toRingHom
    let hA : (N : A) = 0 :=
      (map_natCast e.symm N).symm.trans
        ((congrArg e.symm hB).trans (map_zero e.symm))
    let hX : ∀ x : X.obj.left, IsUnit (N : X.obj.left.presheaf.stalk x) :=
      fun x ↦ by
        change IsUnit (((C.l ^ (a + 1) : ℕ) : X.obj.left.presheaf.stalk x))
        rw [Nat.cast_pow]
        exact (P.coefficientPrime_isUnit_stalk X.obj.left X.obj.hom x).pow (a + 1)
    let β := sfPurityFiniteScalarLine φ N
      (pow_pos (Fact.out : C.l.Prime).pos _) hA hB X.obj.left hX
    ∀ hK : finiteTorConstructible C.l L.val (a + 1) (Nat.succ_pos a) Y.obj.left
          (P.coefficientUnit Y.obj.left),
        (sfIntrinsicDerivedEquivalence X.obj.left P.Ring).functor.map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
            X.obj.left).mapDerivedCategory.map
              ((Etale.purityScalarExtension φ X.obj.left).map
                  (((O.coefficientFinite L a).etale a hA).component f d).hom ≫
                Etale.ExceptionalCoefficients.dualizingScalarMap φ f.hom.left ≫
                (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
                  f.hom.left).map
                    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient)
                      Y.obj.left).inv) ≫
            sfPurityUnitExceptionalPresentation P f.hom.left) =
          (sfIntrinsicDerivedEquivalence X.obj.left P.Ring).functor.map
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
              X.obj.left).mapDerivedCategory.map
                (PurityFiniteSetting.finiteTateScalarLineMap φ N hA hB X.obj.left d (β d) ≫
                  (AdicSmoothDualizing.etalePowerComparison P X.obj.left
                    (P.diagonalExponent_isUnit X.obj.hom) d).inv)) ≫
            (RationalSmoothPurityCanonical.finiteUnitSource P f.hom.left d).inv ≫
            P.smoothPurityMap f.hom.left d (P.coefficientUnit Y.obj.left) hK


/-- The specified smooth-purity maps, simultaneously at all coefficient stages,
form an orientation datum. The finite normalization fixes every quotient and
finite coefficient field; the datum's actual reduction, rationalization and
common-stage equations fix the integral and field components. At a smooth
structure morphism the inverse of this same component is the dualizing-object
identification, rather than an independently chosen purity isomorphism.
Source: blueprint latest, prop-functor-package.proof.md, clauses (6)--(7)
(blueprint: lem-sf-purity-orientation-datum).

Proof:
1. Evaluate finite smooth purity at the unit; finite-coefficient smooth purity
makes these arrows invertible. Choose the scalar-natural integral family of
lem-pur-adic-purity-scalar-naturality at the completed unit. Its reductions are
these arrows by thm-pur-adic-reconstruction. Rational and common-stage images
are thm-pur-rational-and-qbar-purity's specified components.
2. Smooth trace base change and lem-pur-trace-transpose-base-change give the
base equation for the counit-defined beta. Both beta descriptions are the
transpose of pulled-back counit after inverse compact-support exchange.
3. Apply thm-pur-composition-coherence at the unit. Expand smoothPurityMap as
inverse diagonal orientation followed by theta; theta is the identity at the
unit and natural in its argument. This gives the orientation composition
formula; the even shifts contribute no interchange sign.
4. Finite reduction of purity, normalized integral purity trace and integral
scalar naturality give the coefficient squares as equations of arrows.
5. For a ramified field inclusion first reduce at the cofinal level en, then
at any further quotient. A5 identifies the composites of the comparisons;
canceling their invertible factors gives the finite scalar square, including
identity comparisons, without a field-to-finite reduction.
6. Lift the finite unit arrow and its inverse uniquely through fully faithful
bounded-below etale realization. Vector-integration site comparison fixes the
root-power comparison; the actual comparison unit fixes the exceptional one.
7. The diagonal affine trace site comparison in dimension one identifies the
trace with restricted projective-line integration. Transpose this equality to
obtain finite affine-line normalization at every positive coefficient level.
8. A shifted completed Tate line has its derived endomorphisms identified with
ordinary sheaf endomorphisms by derived-single full faithfulness. Locally these
are multiplication by a section of the inverse-limit coefficient sheaf. If
all finite projections vanish, that section vanishes. Therefore equal finite
reductions detect equality of arrows from this line to the chosen omega.
9. Reduce the integral base and composition equations. A5 preserves pullback,
counit, theta, beta and composition, and normalized integral purity trace
identifies the components. Steps 2--3 and line detection prove the equations.
10. The completed affine-line normalization has the finite integration maps as
reductions. Step 7 and line detection prove equality with the chosen component.
11. Rationalization preserves these equations and A5 identifies their arrows.
For Qbar take a common finite coefficient field for the diagram; scalar
naturality gives independence of enlargement and all common-stage equations.
12. Assemble SfOrientationDatum, including its etale components. The canonical
ordered-power, pulled-unit and exceptional-image comparisons identify the finite
component with smoothPurityMap at coefficientUnit. For each small coefficient
model, transport by the Shrink algebra equivalence on valuation-ring quotients.
The normalized pure-root balancing and the exceptional scalar counit mate give
the same equation at extension L.val. Finite reduction and line detection then
fix each integral component, and rationalization and common-stage equations fix
the field components. On a structure morphism invert this very isomorphism to
obtain omega_X isomorphic to Lambda_X(d)[2d]. -/
theorem purityOrientationDatum (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (m : ℕ) (S : SixFunctorDatum D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m))) :
    ∃ O : SfOrientationDatum S,
      SfPurityFiniteNormalized D C E m S.toSixFunctorFiniteOperations O.primary ∧
      (∀ a : ℕ, SfPurityFiniteNormalized D C E a
        (S.integralNormalization.finiteLevels a) (O.finite a)) ∧
      ∀ (L : Padic.FiniteCoefficientFields C.l C.Qbar) (a : ℕ),
        SfPurityCoefficientFiniteNormalized D C E m S O L a := by
  sorry

end WeilConjectures
