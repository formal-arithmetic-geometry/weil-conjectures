/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.SequentialDerivedInverseLimit
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Finite-projective tensor and countable derived products

Source: blueprint, proper base change, finite-reduction-reconstruction proof,
final sentence on tensor and the two Roos products
(blueprint: lem-weil-pbc-finite-projective-tensor-products).

A bounded finite-free retract complex P represents E. Tensor in the first variable
with P in the second already preserves quasi-isomorphisms, so localization gives
precisely C ↦ C tensor-derived E, without resolving C or choosing representatives
of derived objects. The localization comparison fixes this functor on every complex.
The product comparison is Mathlib's canonical map induced by the projections.

## Main definitions

* `finiteProjectiveTensorComplexRight`: total tensor with the chosen representative.
* `finiteProjectiveTensorRight`: its canonical localization lift.
* `finiteProjectiveTensorRightComparison`: the comparison on all complexes.
* `finiteProjectiveTensorRightMap`: the unique roof-normalized coefficient action.

## Main statements

* `finiteProjectiveTensorComplexRight_inverts`: bounded finite-free retracts are K-flat.
* `finiteProjectiveTensorRightMap_exists`: existence and uniqueness of the coefficient action.
* `finiteProjectiveTensorProducts`: preservation of products and naturality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Total tensor with P, followed by the standard localization in D(Mod(A_T)).
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorComplexRight (P : CochainComplex (adicDatumModules T d) ℤ) :
    CochainComplex (adicDatumModules T d) ℤ ⥤ adicDatumDerived T d :=
  (completedConstantTensor T (adicDatumRing T d)).flip.obj P ⋙ completedConstantQ _

/-- Bounded finite-free retract terms make tensor with P preserve quasi-isomorphisms.
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products).
Proof: each finite free term is flat because its tensor is a finite sum of the input.
Retracts preserve exactness, so every term of P is flat. Finite totalization of the
acyclic test tensor is acyclic, starting with the end term of the bounded complex
and inducting through its finite filtration. Thus P is K-flat. The cone of a
quasi-isomorphism is acyclic, and tensor with P commutes with this cone, including
its differential signs. It is therefore again a quasi-isomorphism. Localization
makes its image an isomorphism. This is step 1 of the node's proof, using
 def-weil-derived-tensor and def-pc-tensor-complex-sheaves. -/
theorem finiteProjectiveTensorComplexRight_inverts
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    (HomologicalComplex.quasiIso (adicDatumModules T d) (ComplexShape.up ℤ)).IsInvertedBy
      (finiteProjectiveTensorComplexRight T d P) := by
  sorry

/-- The canonical derived functor C ↦ C tensor-derived E, for E represented by P.
The value is defined by localization, with its universal representative comparison;
no arbitrary endofunctor or isomorphism is chosen.
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorRight (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    adicDatumDerived T d ⥤ adicDatumDerived T d :=
  Localization.lift (finiteProjectiveTensorComplexRight T d P)
    (finiteProjectiveTensorComplexRight_inverts T d P hb p) (completedConstantQ _)

/-- On every complex, this is exactly total tensor with the chosen bounded representative.
It identifies the functor with derived tensor by E = Q(P), naturally in the input.
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorRightComparison (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    completedConstantQ _ ⋙ finiteProjectiveTensorRight T d P hb p ≅
      finiteProjectiveTensorComplexRight T d P :=
  Localization.fac (finiteProjectiveTensorComplexRight T d P)
    (finiteProjectiveTensorComplexRight_inverts T d P hb p) (completedConstantQ _)

/-- A derived coefficient map induces a unique tensor transformation, fixed on every
K-flat test complex and every roof representing that coefficient map.
Source: blueprint, finite-reduction-reconstruction proof, functoriality in step 4
(blueprint: lem-weil-pbc-finite-projective-tensor-products).
Proof: represent a derived map by a roof P ← S → P'. For a K-flat test complex C,
tensoring the left denominator with C is a quasi-isomorphism. Invert its localized
image and follow by the numerator; conjugate by the two localization comparisons.
Common refinements of roofs show independence, because tensor is a functor and
inverts every denominator on this K-flat test class. The resulting maps commute
with test-complex chain maps and inverse quasi-isomorphisms. K-flat resolutions
of arbitrary test complexes extend this to a natural transformation on D(Mod(A_T)).
The same resolutions prove uniqueness: its components on all K-flat test objects
are prescribed, and every derived object is isomorphic to one of them. -/
theorem finiteProjectiveTensorRightMap_exists
    (P P' : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (hb' : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P'.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (p' : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P')
    (e : (completedConstantQ _).obj P ⟶ (completedConstantQ _).obj P') :
    ∃! η : finiteProjectiveTensorRight T d P hb p ⟶
        finiteProjectiveTensorRight T d P' hb' p',
      ∀ (C : CochainComplex (adicDatumModules T d) ℤ),
        CochainComplex.IsAcyclicTensorKFlat (R := adicDatumRing T d) C →
        ∀ (S : CochainComplex (adicDatumModules T d) ℤ) (s : S ⟶ P) [QuasiIso s]
          (g : S ⟶ P'),
          e = inv ((completedConstantQ _).map s) ≫ (completedConstantQ _).map g →
          (completedConstantQ _).map
              (((completedConstantTensor T (adicDatumRing T d)).obj C).map s) ≫
            (finiteProjectiveTensorRightComparison T d P hb p).inv.app C ≫
              η.app ((completedConstantQ _).obj C) =
          (completedConstantQ _).map
              (((completedConstantTensor T (adicDatumRing T d)).obj C).map g) ≫
            (finiteProjectiveTensorRightComparison T d P' hb' p').inv.app C := by
  sorry

/-- Tensoring an arbitrary derived coefficient map, defined by its unique roof formula.
Source: blueprint, finite-reduction-reconstruction proof, functoriality in step 4
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorRightMap
    (P P' : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (hb' : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P'.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (p' : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P')
    (e : (completedConstantQ _).obj P ⟶ (completedConstantQ _).obj P') :
    finiteProjectiveTensorRight T d P hb p ⟶ finiteProjectiveTensorRight T d P' hb' p' :=
  (finiteProjectiveTensorRightMap_exists T d P P' hb hb' p p' e).exists.choose

/-- Tensor by a globally strict-perfect coefficient complex preserves countable products.
The comparison is induced by the actual derived-product projections. The second clause
records naturality for every derived coefficient map e : E → E', using the unique
roof-normalized tensor transformation, and every componentwise map f of families.
Thus the assertion is independent of the bounded representative and is functorial
in E and in the family.

Source: blueprint, finite-reduction-reconstruction proof, final tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products).
Proof:
1. By finiteProjectiveTensorComplexRight_inverts, P is K-flat; the localization
comparison computes derived tensor using the ordinary total tensor with P.
2. Tensor with a finite free term is a finite power, which commutes with products.
For a retract, use its same splitting idempotent on both sides; the comparison
intertwines the idempotents and hence restricts to an isomorphism on their images.
3. Boundedness makes every total diagonal a finite sum. Apply step 2 to its terms;
the comparisons respect the signed differential since all use the same projections.
By lem-weil-proetale-countable-products-exact and def-pc-tensor-complex-sheaves,
localization of termwise products computes the derived product.
4. By def-weil-pbc-derived-inverse-limit this is precisely the product in the stated
ambient category, so the resulting canonical map is invertible. Composing either
naturality route with its nth projection gives the same map, by functoriality and
naturality of the roof-normalized transformation. Product uniqueness gives the
displayed equality, also for arbitrary derived maps and inverse quasi-isomorphisms. -/
theorem finiteProjectiveTensorProducts
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (C : ℕ → adicDatumDerived T d) :
    IsIso (piComparison (finiteProjectiveTensorRight T d P hb p) C) ∧
    ∀ (P' : CochainComplex (adicDatumModules T d) ℤ)
      (hb' : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P'.X j))
      (p' : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((adicLisseForget T).obj (adicDatumRing T d)) P')
      (e : (completedConstantQ _).obj P ⟶ (completedConstantQ _).obj P')
      (C' : ℕ → adicDatumDerived T d) (f : ∀ n : ℕ, C n ⟶ C' n),
      (finiteProjectiveTensorRight T d P hb p).map (Limits.Pi.map f) ≫
          (finiteProjectiveTensorRightMap T d P P' hb hb' p p' e).app (∏ᶜ C') ≫
          piComparison (finiteProjectiveTensorRight T d P' hb' p') C' =
        piComparison (finiteProjectiveTensorRight T d P hb p) C ≫
          Limits.Pi.map (fun n ↦ (finiteProjectiveTensorRight T d P hb p).map (f n) ≫
            (finiteProjectiveTensorRightMap T d P P' hb hb' p p' e).app (C' n)) := by
  sorry

end AlgebraicGeometry.Scheme
