/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.NormalizedDVRTower
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.FiniteTensorConstructibleCohomology
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.Paper.FiniteCoefficientFlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.IntegralDerivedOperationsOnSlices

/-!
# Integral pullback and completed tensor preserve constructibility

Source: Bhatt--Scholze, Lemmas 6.5.3--6.5.5 and 6.5.9(5); Stacks Project,
Tags 099M, 099N, 09BQ and 054I
(blueprint: lem-pur-integral-operations-preserve-constructible).

Finite reductions use index `n` for the positive exponent `n + 1`. The reduction
comparisons below are the adjoints of the actual Roos projections, transported
through the defining representative comparisons of the integral operations.
Their targets compute the finite pullback and finite derived tensor on K-flat
representatives. All good representatives and all identifications with the input
objects are allowed; no resolutions or comparison morphisms are extra hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical projection of the strict Roos complex to its nth tower term.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-preserve-constructible).
It is the first mapping-cocone projection followed by the nth product projection. -/
def integralOperationRoosProjection (W : AlgebraicGeometry.Scheme.{u})
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (integralOperationsRoos T) ⟶ DerivedCategory.Q.obj (T.obj (op n)) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
        (integralOperationsTowerStep T)) ≫ Pi.π (fun m ↦ T.obj (op m)) n)

/-- The finite pullback of the nth reduction of a good integral representative.
The coefficient pullback is the canonical pro-etale inverse image with its
constant-ring action; exactness makes this compute `f⁻¹(K tensor^L A_(n+1))`.
Source: Bhatt--Scholze, Lemma 6.5.9(5); Stacks Tag 099N(5)
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralPullbackFiniteComplex {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :=
  ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((unrestrictedIntegralFiniteComplex l E Y n).obj P)

/-- The finite derived tensor on the two reduced K-flat representatives.
This is the recorded total tensor, before restricting its scalar action to the completion.
Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Tag 09BQ
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralTensorFiniteComplex (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :=
  (Functor.uncurry.obj
    ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).map₂CochainComplex)).obj
        (((unrestrictedIntegralFiniteComplex l E W n).obj P),
          ((unrestrictedIntegralFiniteComplex l E W n).obj Q))

/-- The canonical reduction comparison for integral pullback. Its adjoint is the
Roos projection, after the defining representative comparison and exact-restriction
factorization. Thus this map is fixed, rather than an arbitrary isomorphism.
Source: Stacks Tag 099N(5); Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralPullbackFiniteComparison {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (K : DerivedCategory (integralTowerModules l E Y))
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj ((integralDerivedPullback l E f).obj K) ⟶
      DerivedCategory.Q.obj (integralPullbackFiniteComplex l E f P.obj n) :=
  (((derivedScalarExtensionRestrictionAdjunction l E X n).choose).homEquiv _ _).symm
    ((integralDerivedPullback l E f).map e.inv ≫
      (integralDerivedPullbackComparison l E f).hom.app P ≫
        integralOperationRoosProjection l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
          (integralPullbackFiniteComplex l E f P.obj n))

/-- The canonical reduction comparison for the completed integral tensor.
Its adjoint is the actual projection to `Res_n(P_n tensor Q_n)` of the defining Roos
complex. The finite tensor is computed on reduced K-flat representatives.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks Tags 099M and 09BQ
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralTensorFiniteComparison (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ M) (d : DerivedCategory.Q.obj Q.obj ≅ N) (n : ℕ) :
    (scalarReductionDerivedExtension l E W n).obj
        ((integralCompletedTensor l E W).obj (M, N)) ⟶
      DerivedCategory.Q.obj (integralTensorFiniteComplex l E W P.obj Q.obj n) :=
  (((derivedScalarExtensionRestrictionAdjunction l E W n).choose).homEquiv _ _).symm
    ((integralCompletedTensor l E W).map (e.inv, d.inv) ≫
      (integralCompletedTensorComparison l E W).hom.app (P, Q) ≫
        integralOperationRoosProjection l E W
          ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) n ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app
          (integralTensorFiniteComplex l E W P.obj Q.obj n))

/-- Integral pullback and completed tensor preserve the bounded constructible
 derived-complete category, and their canonical finite-reduction maps are isomorphisms.

Source: Bhatt--Scholze, Lemmas 6.5.3--6.5.5 and 6.5.9(5); Stacks Tags 099M, 099N,
09BQ and 054I (blueprint: lem-pur-integral-operations-preserve-constructible).

Proof:
1. Choose K-flat resolutions with flat terms. Their finite reductions remain
K-flat with flat terms by lem-pur-kflat-change-of-rings. Repeated scalar extension
identifies with direct reduction by multiplying coefficient factors; this also
proves the quotient cocycle.
2. Finite pullback is exact by prop-weil-pbc-proetale-constant-exact. It commutes
with tensor and constant coefficients by lem-weil-pbc-ringed-topoi-module-pullback-tensor,
and preserves K-flatness by lem-weil-pbc-ringed-pullback-preserves-kflat. Finite total
tensors are K-flat; their terms are flat using lem-weil-pbc-flat-coproduct. The
pure-tensor coefficient formulas give normalized towers (def-coef-normalized-dvr-tower).
3. Apply lem-coef-normalized-dvr-effectivity to both towers. Their Roos limits
are the defining integral operations. Effectivity gives completeness and makes
the adjoints of the actual projections, precisely the displayed comparisons, isomorphisms.
4. Pull back a finite constructible stratification. Its subsets remain constructible
by lem-pur-scheme-constructible-preimage, locally closed by continuity, and their
scheme structures are the base changes of the original immersions
(def-weil-closed-immersion). They are disjoint and cover X.
5. Pull back the trivializing covers of every stratum using def-weil-proetale-inverse-image.
Inverse image preserves finite constant modules, their operations and scalar action;
prop-weil-pbc-proetale-constant-exact identifies the action with the specified one.
Empty strata may be removed; on the empty scheme retain one empty stratum.
6. Exact finite pullback commutes with cohomology and preserves zero. Thus the
constructibility and common cohomological interval of all input reductions give
the same conditions for the pullback reductions
(def-weil-finite-torsion-constructibility, def-weil-derived-complete-integral-detailed).
7. Apply lem-coef-integral-residue-tor to the two residue cohomology intervals.
All reductions have those Tor bounds. Bounded flat models (lem-sf-flat-model)
then put every total tensor in their summed interval, uniformly in n. These
models establish the bound; the strict towers of step 2 remain the chosen towers.
8. By lem-pur-finite-tensor-constructible-cohomology all finite tensor cohomology
sheaves are constructible. The uniform bound and completeness of step 3 verify
all clauses of def-weil-derived-complete-integral-detailed for the completed tensor.
The reduction isomorphisms are already the canonical maps from step 3. -/
theorem integralOperations_preserve_constructible
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (∀ K : DerivedCategory (integralTowerModules l E Y),
      sfIntegralConstructible l E Y K →
      sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K) ∧
        ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
          (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ),
          IsIso (integralPullbackFiniteComparison l E f K P e n)) ∧
    (∀ (W : AlgebraicGeometry.Scheme.{u}), W = X ∨ W = Y →
      ∀ M N : DerivedCategory (integralTowerModules l E W),
      sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
      sfIntegralConstructible l E W ((integralCompletedTensor l E W).obj (M, N)) ∧
        ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
          (e : DerivedCategory.Q.obj P.obj ≅ M) (d : DerivedCategory.Q.obj Q.obj ≅ N)
          (n : ℕ), IsIso (integralTensorFiniteComparison l E W M N P Q e d n)) := by
  sorry

end WeilConjectures
