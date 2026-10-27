/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials
public import Sheaf.AlgebraicGeometry.BranchMultiplicityTangentCriterion
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison

/-! # Embedded curve jet flags and Hilbert coefficients

Source: Morrison, arXiv:0810.2340, §3.2, Theorem 8(4)--(6), pp.14--15.
(blueprint: def-sfb-projective-curve-jet-weight-data)

All predicates use the actual component normalizations, projective coordinate germs,
and minimum monomial-basis weights. No restriction map or coefficient is chosen here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite Filter
open scoped AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry AlgebraicGeometry.ProjectiveCurveBranches
open AlgebraicGeometry.BoundedHilbertWeight

namespace AlgebraicGeometry.ProjectiveCurveJets

/-- The canonical reduced induced scheme on the whole support.
Source: Stacks 01IZ (blueprint: def-sfb-projective-curve-jet-weight-data). -/
abbrev Reduction (X : Scheme.{u}) : Scheme.{u} :=
  X.nilradical.subscheme

/-- Its canonical closed immersion, cut out by the nilradical.
Source: Stacks 01IZ (blueprint: def-sfb-projective-curve-jet-weight-data). -/
abbrev reductionMap (X : Scheme.{u}) : Reduction X ⟶ X :=
  X.nilradical.subschemeι

/-- The polynomial restriction arrows, characterized on every standard affine chart.
Source: Morrison §2.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def IsRestriction {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
    (i : X ⟶ Ambient k (n + 2))
    (ρ : ∀ m : ℕ, ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
      sections k n i m) : Prop :=
  ∀ (m : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m)
    (j : HilbertPlucker.Coordinates.{u} n),
    ((Scheme.Modules.tensorPullback i).obj
      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) (m : ℤ))).presheaf.map
        (homOfLE le_top).op ((UniformProjectiveFibreVanishing.zeroSections _).hom (ρ m p)) =
      Scheme.Modules.tensorPullbackSection i
        (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) (m : ℤ))
        (ProjectiveSpace.standardOpen _ (Spec (.of k)) j)
        (ProjectiveSpace.chartRingEquiv _ k j (MvPolynomial.dehomogenizeX k j p.val) •
          ProjectiveSpace.twistGenerator _ (Spec (.of k)) (m : ℤ) j)

/-- The coefficient of m², with the precise O(m) convention of the weight-polynomial node.
Source: Morrison §2.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def HasCoefficient {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
    {i : X ⟶ Ambient k (n + 2)}
    (ρ : ∀ m : ℕ, ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
      sections k n i m)
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) (a : ℚ) : Prop :=
  ∃ A : ℕ, ∀ᶠ m : ℕ in atTop,
    (∃ S, IsMonomialBasis (ρ m) b S) ∧
      |(weight (ρ m) b w : ℚ) - a * (m : ℚ)^2| ≤ (A : ℚ) * m

/-- The coefficient vector of an actual homogeneous linear polynomial.
Source: Morrison §2.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def coefficients {k : Type u} [Field k] {n : ℕ} (f : LinearForms k n) :
    ULift.{u} (Fin (n + 2)) → k :=
  fun j ↦ MvPolynomial.coeff (Finsupp.single j 1) f.val

/-- Vanishing of a linear form at a projective point, independent of the coordinate frame.
Source: Morrison §3.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def VanishesAt {k : Type u} [Field k] {n : ℕ}
    (x : Ambient k (n + 2)) (f : LinearForms k n) : Prop :=
  ∀ (j : ULift.{u} (Fin (n + 2)))
    (hx : x ∈ ProjectiveSpace.standardOpen _ (Spec (.of k)) j),
    linearGerm k (n + 2) x j hx (coefficients f) ∈
      IsLocalRing.maximalIdeal ((Ambient k (n + 2)).presheaf.stalk x)

/-- Order at least h on the specified normalized branch; zero germs satisfy every order.
Source: Morrison §3.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def HasBranchOrder {k : Type u} [Field k] {n : ℕ} {D : Scheme.{u}}
    (i : D ⟶ Ambient k (n + 2)) (p : D) (q : Branch D p) (h : ℕ)
    (f : LinearForms k n) : Prop :=
  ∀ (j : ULift.{u} (Fin (n + 2)))
    (hp : i p ∈ ProjectiveSpace.standardOpen _ (Spec (.of k)) j),
    localMap D p q ((i.stalkMap p)
      (linearGerm k (n + 2) (i p) j hp (coefficients f))) ∈
        IsLocalRing.maximalIdeal ((Component D q.1).presheaf.stalk q.2.1) ^ h

/-- Restriction of coefficient vectors to genuine global sections of the pulled-back O(1).
Source: Morrison §3.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def linearSection {k : Type u} [Field k] {r : ℕ} {Y : Scheme.{u}}
    (j : Y ⟶ Ambient k r) (a : ULift.{u} (Fin r) → k) :
    Γ((Scheme.Modules.tensorPullback j).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) 1), ⊤) :=
  ∑ t : ULift.{u} (Fin r),
    (j ≫ (Ambient k r ↘ Spec (.of k))).appTop.hom
      ((Scheme.ΓSpecIso (.of k)).inv (a t)) •
      (Scheme.Modules.tensorPullbackTopSection j
        (ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of k)) 1)
        (ProjectiveSpace.twistOneSection (ULift.{u} (Fin r)) (Spec (.of k)) t))

/-- A rational normal embedded component: it is P¹ over k, and the ambient linear forms
surject onto its hyperplane sections. Since the morphism is a closed immersion, this is
exactly the complete linear system embedding in its own linear span; its degree is the
recorded hyperplane degree on normalization.
Source: Morrison §3.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def IsRationalNormal {k : Type u} [Field k] {r : ℕ} {Y : Scheme.{u}}
    (j : Y ⟶ Ambient k r) : Prop :=
  (∃ e : Y ≅ ProjectiveLine (Spec (.of k)),
    e.hom ≫ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) =
      j ≫ (Ambient k r ↘ Spec (.of k))) ∧ Function.Surjective (linearSection j)

/-- The multiplicity flag, with weight zero on forms vanishing at p and weight one outside.
Source: Morrison §3.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def IsPointFlag {k : Type u} [Field k] {n : ℕ}
    (x : Ambient k (n + 2))
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) : Prop :=
  (∀ j, w j ≤ 1) ∧ ∀ f : LinearForms k n, f ∈ flag b w 0 ↔ VanishesAt x f

/-- The ramified branch flag. The equal thresholds at 2 and 3 exclude weight 3;
empty graded pieces impose no artificial nonemptiness requirement.
Source: Morrison §3.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def IsRamifiedFlag {k : Type u} [Field k] {n : ℕ} {D : Scheme.{u}}
    (i : D ⟶ Ambient k (n + 2)) (p : D) (q : Branch D p)
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) : Prop :=
  (∀ j, w j ≤ 4) ∧
    (∀ f : LinearForms k n, f ∈ flag b w 0 ↔ HasBranchOrder i p q 4 f) ∧
    (∀ f : LinearForms k n, f ∈ flag b w 1 ↔ HasBranchOrder i p q 3 f) ∧
    (∀ f : LinearForms k n, f ∈ flag b w 2 ↔ HasBranchOrder i p q 2 f) ∧
    flag b w 3 = flag b w 2

/-- The common-tangent flag: weights 0 on its equations, 1 on the additional point
ideal and 2 on the remaining forms.
Source: Morrison §3.2 (blueprint: def-sfb-projective-curve-jet-weight-data). -/
def IsTangentFlag {k : Type u} [Field k] {n : ℕ} {D : Scheme.{u}}
    (i : D ⟶ Ambient k (n + 2)) (p : D) (q : Branch D p)
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) : Prop :=
  (∀ j, w j ≤ 2) ∧
    (∀ f : LinearForms k n, f ∈ flag b w 0 ↔
      coefficients f ∈ lineEquations k (n + 2) D i p q) ∧
    (∀ f : LinearForms k n, f ∈ flag b w 1 ↔ VanishesAt (i p) f)

end AlgebraicGeometry.ProjectiveCurveJets
