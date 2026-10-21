/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.AdicLocalCharacteristicFactor
public import Sheaf.Paper.CommonStageLocallyFree
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Sheaf.Paper.ZlImmersionWeilLocalBehavior
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.LisseRationalRealization
import Sheaf.Paper.EtaleWeilFundamentalRepresentation
import Sheaf.Paper.EtaleWeilSheafEquivalence
import Sheaf.Paper.WeilPullbackLocalFrobenius
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity
import Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent
import WeilConjectures.DeligneLaumon.Reduction.RealSheaves
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent

/-! # Uniform purity of geometric constituents by two-point curves

Source: main-20261015, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraphs 2--4
(blueprint: lem-zl-two-point-curve-constituent-purity).

The auxiliary records expand the curve and local power clauses. They use the actual
common-stage heart, its canonical pullback, and the normalized constant restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Geometric irreducibility means nonzero and no proper nonzero lisse subobject
in the geometric heart; the Weil action is forgotten in this condition.
Source: paragraphs 1--2, geometrically irreducible quotients
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
def TwoPointGeometricallyIrreducible (F : sfCommonStageWeilSheaf D l hl X₀ Ω) : Prop :=
  (@IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber X₀).left
    (sfWeilPrimeInvertible D l hl X₀) F.obj.carrier) ∧ ¬ IsZero F ∧
    ∀ (A : sfCommonStageHeart l (D.geometricFiber X₀).left Ω)
      (i : A ⟶ ⟨F.obj.carrier, F.property⟩),
      Mono i →
      (@IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber X₀).left
        (sfWeilPrimeInvertible D l hl X₀) A.obj) → IsZero A ∨ IsIso i

/-- A smooth geometrically connected affine closed curve over the actual k_m,
with restriction characterized by the canonical fibre identification and theta^[m].
Source: paragraph 2, finite-field curve and restriction
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
structure TwoPointCurve (m : ℕ) (hm : 1 ≤ m) [IsSeparated X₀.hom] where
  curve : Over (Spec (.of (D.extensionSubfield m hm)))
  [finiteType : LocallyOfFiniteType curve.hom]
  [quasiCompact : QuasiCompact curve.hom]
  immersion : curve ⟶ constantExtensionModel D m hm X₀
  closed : IsClosedImmersion immersion.left
  affine : IsAffine curve.left
  smooth : SmoothOfRelativeDimension 1 curve.hom
  connected : GeometricallyConnected curve.hom
  restriction : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
    sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω
  restriction_spec : ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω restriction

attribute [instance] TwoPointCurve.finiteType TwoPointCurve.quasiCompact
  TwoPointCurve.affine TwoPointCurve.closed TwoPointCurve.smooth TwoPointCurve.connected

/-- The curve restriction is the recorded inverse image after normalized constant restriction.
Source: paragraph 2, exact restriction of the filtration
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
def TwoPointCurve.pull [IsSeparated X₀.hom] {m : ℕ} {hm : 1 ≤ m}
    (C : TwoPointCurve D l hl Ω X₀ m hm) :=
  C.restriction ⋙ zlWeilPull (constantExtensionDatum D m hm) l hl Ω C.immersion

/-- The map of geometric curves to the original geometric scheme is actual base change
followed by the canonical associativity isomorphism.
Source: paragraph 2, containment of the two geometric lifts
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
def TwoPointCurve.geometricMap [IsSeparated X₀.hom] {m : ℕ} {hm : 1 ≤ m}
    (C : TwoPointCurve D l hl Ω X₀ m hm) :=
  zlFiberMap (constantExtensionDatum D m hm) C.immersion ≫
    (constantExtensionFiberIso D m hm X₀).hom

/-- The arithmetic map is the closed immersion followed by the finite constant projection.
Source: paragraphs 3--4, points z over x
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
def TwoPointCurve.arithmeticMap [IsSeparated X₀.hom] {m : ℕ} {hm : 1 ≤ m}
    (C : TwoPointCurve D l hl Ω X₀ m hm) :=
  C.immersion.left ≫ (constantExtensionProjection D m hm X₀).left

/-- The residue extension degree uses the actual residue field homomorphism.
Source: paragraphs 3--4, e and f
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
def TwoPointCurve.residueDegree [IsSeparated X₀.hom] {m : ℕ} {hm : 1 ≤ m}
    (C : TwoPointCurve D l hl Ω X₀ m hm) (z : C.curve.left) : ℕ :=
  letI := ((C.arithmeticMap D l hl Ω X₀).residueFieldMap z).hom.toAlgebra
  Module.finrank (X₀.left.residueField ((C.arithmeticMap D l hl Ω X₀) z))
    (C.curve.left.residueField z)

/-- Local spectra, with multiplicities, are roots of the characteristic polynomial,
obtained by reversing the recorded reverse characteristic factor.
Source: paragraphs 3--4, local eigenvalues
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
def twoPointSpectrum [IsSeparated X₀.hom] (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left}) : Multiset Ω :=
  (sfLocalCharacteristicFactor D l hl Ω X₀ F x).reverse.roots

/-- A curve tests all constituents simultaneously and retains the local power calculation,
including multiplicities, at every closed point of the curve.
Source: paragraphs 2--4, restrictions, reality, and residue degrees
(blueprint: lem-zl-two-point-curve-constituent-purity). -/
def TwoPointCurve.Tests [IsSeparated X₀.hom] {m : ℕ} {hm : 1 ≤ m}
    (C : TwoPointCurve D l hl Ω X₀ m hm)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) {r : ℕ}
    (S : Fin r → sfCommonStageWeilSheaf D l hl X₀ Ω)
    (iota : Ω ≃+* ℂ) (w : Fin r → ℝ) : Prop :=
  SfIsReal (constantExtensionDatum D m hm) l hl Ω C.curve iota
      ((C.pull D l hl Ω X₀).obj F) ∧
    (∀ j : Fin r,
      TwoPointGeometricallyIrreducible (constantExtensionDatum D m hm) l hl Ω C.curve
        ((C.pull D l hl Ω X₀).obj (S j)) ∧
      SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω C.curve iota
        ((C.pull D l hl Ω X₀).obj (S j)) (w j) ∧
      ∀ v : ℝ,
        SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω C.curve iota
          ((C.pull D l hl Ω X₀).obj (S j)) v → v = w j) ∧
    ∀ (H : sfCommonStageWeilSheaf D l hl X₀ Ω), (H = F ∨ ∃ j, H = S j) →
      ∀ (z : {z : C.curve.left // z ∈ closedPoints C.curve.left})
        (x : {x : X₀.left // x ∈ closedPoints X₀.left}),
        (C.arithmeticMap D l hl Ω X₀) z.val = x.val →
        1 ≤ C.residueDegree D l hl Ω X₀ z.val ∧
        Nat.card (C.curve.left.residueField z.val) =
          Nat.card (X₀.left.residueField x.val) ^ C.residueDegree D l hl Ω X₀ z.val ∧
        twoPointSpectrum (constantExtensionDatum D m hm) l hl Ω C.curve
            ((C.pull D l hl Ω X₀).obj H) z =
          (twoPointSpectrum D l hl Ω X₀ H x).map
            (fun a ↦ a ^ C.residueDegree D l hl Ω X₀ z.val)

/-- Every geometrically irreducible quotient in a lisse filtration of a real sheaf is pure,
with simultaneous two-point curves and the fixed-anchor weight formula.
Source: main-20261015 thm-zl-real-mixed-by-curves.proof.md, paragraphs 2--4
(blueprint: lem-zl-two-point-curve-constituent-purity).

Proof:
1. Apply lem-zl-curve-testing-irreducibility to the two chosen lifts (a singleton when
   equal), and to all the quotients together; the family can be empty.
2. Descend the closed curve by lem-zl-bertini-finite-field-descent. Its affine coordinate
   algebra B becomes the smooth geometric curve after faithfully flat extension to k.
   Faithfully-flat surjectivity gives geometric primes above all its primes.
3. Smooth-at-prime descent, dimension invariance under field extension, and geometric
   connectedness tested over the algebraic closure give a smooth connected affine curve
   over k_m, of relative dimension one.
4. Constant extension and immersion pullback are exact on Weil hearts. The classical
   lisse/completed-system and rational-realization comparisons identify their stalks and
   Weil maps, including Frobenius and iterated transports. The local operator at z is
   conjugate to F_x^f and its residue size is q_x^f. Closed-point-field finiteness shows
   that the points under the two lifts are closed.
5. Powering preserves conjugation-stable eigenvalue multisets, even with collisions;
   thus the restricted sheaf remains real, without a semisimplicity assumption.
6. The Weil-sheaf/representation equivalence turns the restricted filtration into a
   composition series: geometric irreducibility implies Weil irreducibility. Apply
   thm-rp-real-lisse-purity-affine to its constituents to obtain curve purity.
7. Nonzero lisse quotients have a nonzero Frobenius eigenvalue alpha at the anchor.
   There |iota(alpha)|^e=(q_anchor^e)^(v/2). Since e>=1 and q_anchor>1, taking logs
   gives v=2 log_(q_anchor)|iota(alpha)|, independent of every curve and eigenvalue.
8. At the other point take the unique positive f-th root of
   |iota(beta)|^f=(q_x^f)^(w/2). This proves global punctual purity. The same argument
   includes x=anchor, length zero, and nonsplit extensions of the filtration. -/
theorem twoPointCurveConstituentPurity
    [IsAffine X₀.left] [IsSeparated X₀.hom] [Nonempty X₀.left]
    [GeometricallyConnected X₀.hom] (d : ℕ) (hd : 1 ≤ d)
    [SmoothOfRelativeDimension d X₀.hom]
    (iota : Ω ≃+* ℂ) (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (hF : @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber X₀).left
      (sfWeilPrimeInvertible D l hl X₀) F.obj.carrier)
    (hreal : SfIsReal D l hl Ω X₀ iota F)
    (r : ℕ) (G : Fin (r + 1) → sfCommonStageWeilSheaf D l hl X₀ Ω)
    (φ : ∀ j : Fin r, G j.castSucc ⟶ G j.succ)
    (hzero : IsZero (G 0)) (hlast : Nonempty (G (Fin.last r) ≅ F))
    (hmono : ∀ j : Fin r, Mono (φ j))
    (hlisse : ∀ j : Fin (r + 1),
      @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber X₀).left
        (sfWeilPrimeInvertible D l hl X₀) (G j).obj.carrier)
    (hirr : ∀ j : Fin r,
      TwoPointGeometricallyIrreducible D l hl Ω X₀ (cokernel (φ j))) :
    ∃ w : Fin r → ℝ,
      (∀ j : Fin r,
        SfIsPunctuallyPureOfWeight D l hl Ω X₀ iota (cokernel (φ j)) (w j)) ∧
      (∀ (anchor : {x : X₀.left // x ∈ closedPoints X₀.left}) (j : Fin r) (α : Ω),
        α ≠ 0 → SfPunctualEigenvalue D l hl Ω X₀ (cokernel (φ j)) anchor α →
          w j = 2 * Real.logb (Nat.card (X₀.left.residueField anchor.val) : ℝ)
            ‖iota α‖) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m) (C : TwoPointCurve D l hl Ω X₀ m hm)
        (anchor : {x : X₀.left // x ∈ closedPoints X₀.left})
        (ιa : X₀.left.residueField anchor.val →+* D.k)
        (ha : ιa.comp (X₀.hom.residueFieldAlgebraMap anchor.val) = algebraMap D.k₀ D.k),
        (∃ a : Spec (.of D.k) ⟶ ((constantExtensionDatum D m hm).geometricFiber
            C.curve).left,
          a ≫ C.geometricMap D l hl Ω X₀ = localClosedPoint D X₀ anchor ιa ha) →
        ∀ (j : Fin r) (v : ℝ),
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω C.curve iota
            ((C.pull D l hl Ω X₀).obj (cokernel (φ j))) v → v = w j) ∧
      ∀ (anchor x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (ιa : X₀.left.residueField anchor.val →+* D.k)
        (ha : ιa.comp (X₀.hom.residueFieldAlgebraMap anchor.val) = algebraMap D.k₀ D.k)
        (ιx : X₀.left.residueField x.val →+* D.k)
        (hx : ιx.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
        ∃ (m : ℕ) (hm : 1 ≤ m) (C : TwoPointCurve D l hl Ω X₀ m hm),
          C.Tests D l hl Ω X₀ F (fun j ↦ cokernel (φ j)) iota w ∧
          (∃ a : Spec (.of D.k) ⟶ ((constantExtensionDatum D m hm).geometricFiber
              C.curve).left,
            a ≫ C.geometricMap D l hl Ω X₀ = localClosedPoint D X₀ anchor ιa ha) ∧
          (∃ b : Spec (.of D.k) ⟶ ((constantExtensionDatum D m hm).geometricFiber
              C.curve).left,
            b ≫ C.geometricMap D l hl Ω X₀ = localClosedPoint D X₀ x ιx hx) := by
  sorry

end WeilConjectures
