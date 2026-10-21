/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.NormalizedClassicalWeilRealization
public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.Paper.LisseAdicAutomorphismPullback
public import Sheaf.Paper.AdicLisseCohomologyCalculus
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.LisseRationalRealization

public import Sheaf.Paper.LisseCompletedSystemData
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Sheaf.Paper.RationalCoefficientCategoryComparison
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.Paper.AdicNormalizedFibreExactness
import Sheaf.Paper.DlConstructibleFibresExact
import Sheaf.Paper.CommonStageCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Classical Weil filtrations in the constructible heart

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 1 and 4;
Bhatt--Scholze, Propositions 6.8.4 and 6.8.14, Remark 6.8.15.
(blueprint: lem-zl-classical-weil-filtration-heart-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Endofunctor (IsoAlgebra)
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

variable [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
  IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- One classical Weil step on actual fibres, before point transport.
Source: Weil II (1.1.10); BS 6.8.15
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def zlClassicalStep (F : ZlClassicalWeil D l Ω Y₀)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω
      (x ≫ (D.geometricFrobenius Y₀).hom) F.carrier ⟶
    lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω x F.carrier :=
  (lisseAlgebraicAutomorphismFiberIso (D.geometricFrobenius Y₀) l Ω x F.carrier).inv ≫
    etaleAlgebraicFiberMap l Ω x F.str.hom

/-- Successive Weil steps, with the endpoint kept as a literal left-associated composite.
Source: Weil II (1.1.10), the defining recurrence for iterated descent
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def zlClassicalOrbitPoint (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    ℕ → (Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
  | 0 => x
  | n + 1 => zlClassicalOrbitPoint x n ≫ (D.geometricFrobenius Y₀).hom

/-- The fibre map of theta^[n], assembled from the actual classical pullback-fibre maps.
Source: Weil II (1.1.10), iterated Weil descent
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def zlClassicalSteps (F : ZlClassicalWeil D l Ω Y₀)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) : (n : ℕ) →
    lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω
        (zlClassicalOrbitPoint D Y₀ x n) F.carrier ⟶
      lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω x F.carrier
  | 0 => 𝟙 _
  | n + 1 => zlClassicalStep D l Ω Y₀ F (zlClassicalOrbitPoint D Y₀ x n) ≫
      zlClassicalSteps F x n

/-- Classical local Frobenius for the normalized return path. The return path is required
in the assertion below to act by precomposition with the n-fold point Frobenius on covers.
Source: Weil II (1.1.8)--(1.1.10)
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def zlClassicalLocal (F : ZlClassicalWeil D l Ω Y₀)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (β : FiniteEtale.fiber x ≅ FiniteEtale.fiber (zlClassicalOrbitPoint D Y₀ x n)) :=
  (etaleAlgebraicPathIso l Ω F.carrier β).hom ≫ zlClassicalSteps D l Ω Y₀ F x n


/-- Finite-stage fibre before extending the coefficient field. This is the recorded
point complex followed by H^0, not an ordinary stalk of a non-torsion etale sheaf.
Source: BS 6.8.14 and the local-operator convention
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def zlFiniteFibre (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E))
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω E) 0).obj
    (localPointComplex l (Coefficient.{u} l Ω E) D hl Y₀ K x)

/-- The displayed finite-stage fibre after the actual inclusion into the closure.
Source: BS 6.8.14, coefficient extension
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def zlExtendedFiniteFibre (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E))
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) : ModuleCat.{u + 1} Ω :=
  (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω E)).obj
    ((ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω E)).obj
      (zlFiniteFibre D l hl Ω Y₀ E K x))

/-- The actual map on the normalized local fibre, including its coefficient extension.
Source: BS 6.8.14; blueprint local-fibre comparison
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def zlFiniteFibreMap (E : Padic.FiniteCoefficientFields l Ω)
    {K M : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E)} (f : K ⟶ M)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    zlExtendedFiniteFibre D l hl Ω Y₀ E K x ⟶ zlExtendedFiniteFibre D l hl Ω Y₀ E M x :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω E)).map
    ((ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω E)).map
      ((DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω E) 0).map
        ((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).map
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) x).map f.hom.f))))

/-- All positive-period local operators of the classical and finite-stage objects agree.
The path on every finite etale cover is explicitly point-Frobenius precomposition;
it is not a freely chosen path. The same identification works for every iterate.
Source: Weil II (1.1.8)--(1.1.10); BS 6.8.15
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
structure ZlClassicalFibreComparison (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E))
    (F : ZlClassicalWeil D l Ω Y₀) where
  fibre : ∀ x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
    zlExtendedFiniteFibre D l hl Ω Y₀ E K x ≅
      lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω x F.carrier
  local_operator : ∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x),
    ∃ β : FiniteEtale.fiber x ≅
        FiniteEtale.fiber (zlClassicalOrbitPoint D Y₀ x (n + 1)),
      (∀ (P : (D.geometricFiber Y₀).left.FiniteEtale) (z : (FiniteEtale.fiber x).obj P),
        (β.hom.app P z).left = localPositivePower (frobeniusPointIso D).hom n ≫ z.left) ∧
      (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω E)).map
          ((ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω E)).map
            (localFrobeniusCohomology l (Coefficient.{u} l Ω E) D hl Y₀ K x n h 0)) ≫
          (fibre x).hom =
        (fibre x).hom ≫ zlClassicalLocal D l Ω Y₀ F x (n + 1) β

/-- A given classical finite filtration, with specified quotients and exactness on
all geometric adic fibres. There are no quotient indices when r=0.
Source: blueprint real-mixed-by-curves proof, paragraph 1
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
structure ZlClassicalFiltration (r : ℕ) where
  terms : Fin (r + 1) → ZlClassicalWeil D l Ω Y₀
  quotients : Fin r → ZlClassicalWeil D l Ω Y₀
  inclusion : ∀ j : Fin r, terms j.castSucc ⟶ terms j.succ
  quotient : ∀ j : Fin r, terms j.succ ⟶ quotients j
  zero : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ (D.geometricFiber Y₀).left),
    Subsingleton ((lisseAlgebraicFiberFunctor l (D.geometricFiber Y₀).left x Ω).obj
      (terms 0).carrier)
  exact : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ (D.geometricFiber Y₀).left) (j : Fin r),
    Function.Injective ((lisseAlgebraicFiberFunctor l (D.geometricFiber Y₀).left x Ω).map
      (inclusion j).hom.f) ∧
    Function.Exact ((lisseAlgebraicFiberFunctor l (D.geometricFiber Y₀).left x Ω).map
      (inclusion j).hom.f)
      ((lisseAlgebraicFiberFunctor l (D.geometricFiber Y₀).left x Ω).map
        (quotient j).hom.f) ∧
    Function.Surjective ((lisseAlgebraicFiberFunctor l (D.geometricFiber Y₀).left x Ω).map
      (quotient j).hom.f)

/-- A finite-stage Weil filtration, with exactness in the underlying raw constructible
heart. Both maps and both directions of every Weil isomorphism belong to this same E.
Source: blueprint finite-stage clause; BS 6.8.14
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
structure ZlFiniteFiltration (r : ℕ) (E : Padic.FiniteCoefficientFields l Ω) where
  terms : Fin (r + 1) → sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E)
  quotients : Fin r → sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E)
  terms_heart : ∀ j, sfRationalHeartProperty l (Coefficient.{u} l Ω E)
    (D.geometricFiber Y₀).left (terms j).carrier
  quotients_heart : ∀ j, sfRationalHeartProperty l (Coefficient.{u} l Ω E)
    (D.geometricFiber Y₀).left (quotients j).carrier
  inclusion : ∀ j : Fin r, terms j.castSucc ⟶ terms j.succ
  quotient : ∀ j : Fin r, terms j.succ ⟶ quotients j
  zero : IsZero (terms 0).carrier
  exact : ∀ j : Fin r, ∃ h :
      (ObjectProperty.homMk (X := ⟨_, terms_heart j.castSucc⟩)
        (Y := ⟨_, terms_heart j.succ⟩) (inclusion j).hom.f) ≫
      (ObjectProperty.homMk (X := ⟨_, terms_heart j.succ⟩)
        (Y := ⟨_, quotients_heart j⟩) (quotient j).hom.f) = 0,
    (ShortComplex.mk _ _ h).ShortExact

/-- Classical punctual purity, using the prescribed finite-cover return path, and
all eigenvalues in the chosen algebraic closure. The zero quotient has no eigenvalues.
Source: Weil II (1.2.6)
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def ZlClassicalPure (iota : Ω →+* ℂ) (F : ZlClassicalWeil D l Ω Y₀) (w : ℝ) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (β : FiniteEtale.fiber (localClosedPoint D Y₀ y ι hι) ≅
      FiniteEtale.fiber (zlClassicalOrbitPoint D Y₀ (localClosedPoint D Y₀ y ι hι)
        (localClosedPointDegree D Y₀ y))),
    (∀ (P : (D.geometricFiber Y₀).left.FiniteEtale)
      (z : (FiniteEtale.fiber (localClosedPoint D Y₀ y ι hι)).obj P),
      (β.hom.app P z).left =
        localPositivePower (frobeniusPointIso D).hom
          (localClosedPointDegree D Y₀ y - 1) ≫ z.left) →
    ∀ α : Ω, Module.End.HasEigenvalue
      (zlClassicalLocal D l Ω Y₀ F (localClosedPoint D Y₀ y ι hι)
        (localClosedPointDegree D Y₀ y) β).hom α →
      ‖iota α‖ = (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)

/-- A simultaneous representative of the prescribed diagram. The comparison is in the
Weil category, so its inverse also intertwines descent. The two map equations retain
the prescribed inclusions and quotient arrows, and exactness is asserted in both hearts.
Source: blueprint real-mixed-by-curves, paragraphs 1 and 4, common-stage clause
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
structure ZlFiltrationTransport (R : ZlClassicalRealization D l hl Ω Y₀)
    (r : ℕ) (F : ZlClassicalFiltration D l Ω Y₀ r)
    (G : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (e : (R.weil D l hl Ω Y₀).obj (F.terms (Fin.last r)) ≅ G)
    (iota : Ω ≃+* ℂ) where
  field : Padic.FiniteCoefficientFields l Ω
  model : ZlFiniteFiltration D l hl Ω Y₀ r field
  terms : ∀ j : Fin (r + 1), sfWeilStageObject D l hl Y₀ Ω field (model.terms j) ≅
    ((R.weil D l hl Ω Y₀).obj (F.terms j)).obj
  quotients : ∀ j : Fin r, sfWeilStageObject D l hl Y₀ Ω field (model.quotients j) ≅
    ((R.weil D l hl Ω Y₀).obj (F.quotients j)).obj
  inclusion : ∀ j : Fin r,
    (GeneralAlgebraicallyClosedCoefficients.inclusion field).map
        (model.inclusion j).hom.f ≫ (terms j.succ).hom.hom.f =
      (terms j.castSucc).hom.hom.f ≫
        ((R.weil D l hl Ω Y₀).map (F.inclusion j)).hom.hom.f
  quotient : ∀ j : Fin r,
    (GeneralAlgebraicallyClosedCoefficients.inclusion field).map
        (model.quotient j).hom.f ≫ (quotients j).hom.hom.f =
      (terms j.succ).hom.hom.f ≫
        ((R.weil D l hl Ω Y₀).map (F.quotient j)).hom.hom.f
  top : sfWeilStageObject D l hl Y₀ Ω field (model.terms (Fin.last r)) ≅ G.obj
  top_identification : top = terms (Fin.last r) ≪≫
    (((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).inverseImage
      (sfCommonStageWeilForget D l hl Y₀ Ω)).ι).mapIso e
  zero : IsZero ((R.weil D l hl Ω Y₀).obj (F.terms 0))
  exact : ∀ j : Fin r, ∃ h :
      (R.weil D l hl Ω Y₀).map (F.inclusion j) ≫
        (R.weil D l hl Ω Y₀).map (F.quotient j) = 0,
    (ShortComplex.mk _ _ h).ShortExact
  terms_fibres : ∀ j : Fin (r + 1),
    ZlClassicalFibreComparison D l hl Ω Y₀ field (model.terms j) (F.terms j)
  quotient_fibres : ∀ j : Fin r,
    ZlClassicalFibreComparison D l hl Ω Y₀ field (model.quotients j) (F.quotients j)
  inclusion_fibres : ∀ (j : Fin r)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    zlFiniteFibreMap D l hl Ω Y₀ field (model.inclusion j) x ≫
        ((terms_fibres j.succ).fibre x).hom =
      ((terms_fibres j.castSucc).fibre x).hom ≫
        etaleAlgebraicFiberMap l Ω x (F.inclusion j).hom.f
  quotient_fibres_natural : ∀ (j : Fin r)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    zlFiniteFibreMap D l hl Ω Y₀ field (model.quotient j) x ≫
        ((quotient_fibres j).fibre x).hom =
      ((terms_fibres j.succ).fibre x).hom ≫
        etaleAlgebraicFiberMap l Ω x (F.quotient j).hom.f
  purity : ∀ (j : Fin r) (w : ℝ),
    SfIsPunctuallyPureOfWeight D l hl Ω Y₀ iota.toRingHom
      ((R.weil D l hl Ω Y₀).obj (F.quotients j)) w ↔
        ZlClassicalPure D l Ω Y₀ iota.toRingHom (F.quotients j) w

omit hUnits in
/-- The proposition specializes only the inherited prime-invertibility instance. No
prime-unit or auxiliary-lattice assumption is added to the geometric hypotheses.
The uniform realization is the inverse-limit realization above; the filtration itself
is arbitrary, and its given top isomorphism is retained in ZlFiltrationTransport.
Source: blueprint real-mixed-by-curves, paragraphs 1 and 4; BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def ZlClassicalFiltrationHeartTransport (iota : Ω ≃+* ℂ) : Prop :=
  letI : Fact (∀ x : (D.geometricFiber Y₀).left,
      IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x)) :=
    ⟨fun x ↦ @isUnit_of_invertible _ _ _ (zlClassicalStalkInvertible D l hl Y₀ x)⟩
  ∀ R : ZlClassicalRealization D l hl Ω Y₀,
    ∀ (r : ℕ) (F : ZlClassicalFiltration D l Ω Y₀ r)
      (G : sfCommonStageWeilSheaf D l hl Y₀ Ω)
      (e : (R.weil D l hl Ω Y₀).obj (F.terms (Fin.last r)) ≅ G),
      Nonempty (ZlFiltrationTransport D l hl Ω Y₀ R r F G e iota)

omit hUnits in
/-- Realize a prescribed classical lisse Weil filtration, including its actual maps,
quotients, normalized local operators, weights and one common finite coefficient stage.
Every return period is allowed: n+1=m*d gives the local operator for an m-fold
constant extension with its iterated Weil structure, without a minimal-period assumption.
Source: blueprint real-mixed-by-curves proof, paragraphs 1 and 4; BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-weil-filtration-heart-transport).

Proof:
1. Finite type over the field makes the geometric fibre noetherian, finite-dimensional,
and a finite union of clopen connected components. Work componentwise, including empty Y.
2. Use the classical Hom colimit to put all terms, quotients, arrows, Weil maps and inverse
Weil maps over one finite coefficient field. Enlarge it for their finitely many equations.
3. Use cor-galois-lisse-representations and lem-pod-profinite-stable-lattice to replace
underlying systems by finite locally free lattices. Do not make Weil maps integral.
4. Complete the systems by inverse limits. Compose the fully faithful comparison of
lem-per-lisse-completed-system-comparison with lem-tw-lisse-rational-realization. Its
fraction rule realizes every a tensor f; lift Weil maps and inverses and their equations.
5. Normalize fibres by completed geometric pullback and point sections. The point clause
of lem-tw identifies sections with the inverse limit of finite-level adic stalks. Compare
also through J of lem-fd-rational-coefficient-category-comparison and the normalized PBC
fibres, using lem-per-continuous-rational-derived-realization.
6. Apply lem-dl-a1-constructible-fibres-exact to the realized short complexes. They are
short exact in the actual heart; conjugate the top identification by the given e.
7. At the finite field, lem-per-adic-normalized-fibre-exactness detects exactness. Exact
faithful extension of fields descends fibre exactness from the coefficient closure.
8. The finite common-stage calculus puts all this data and all its equations at one
larger field; retain the lisse models and the actual inverses there.
9. On finite cover germs, point transport is precomposition by point Frobenius. The
finite-level comparisons, inverse limits and localization preserve it. Induct on n in
the recorded localPointTransportIterate and localWeilIterate. Their return compositor is
the same semilinear scheme-map equality, so the complete local operators intertwine.
10. Conjugacy gives the same eigenvalues and hence exactly the same punctual purity for
each real weight, including zero quotients with vacuous purity.
11. Group m successive transport and Weil factors for a constant extension. The assertion
for every return period includes these grouped operators. For r=0 there are no quotient
sequences; the zero object and its identification are represented at any finite field. -/
theorem zl_classical_weil_filtration_heart_transport (iota : Ω ≃+* ℂ) :
    ZlClassicalFiltrationHeartTransport D l hl Ω Y₀ iota := by
  sorry



end WeilConjectures
