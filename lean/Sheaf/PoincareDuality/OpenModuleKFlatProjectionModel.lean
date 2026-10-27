/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.PoincareDuality.OpenModuleBalancedProjection
public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Algebra.Homology.KFlatModuleObject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric

/-!
# The canonical unbounded open module projection model

Source: blueprint `sec-six-functors-basics/sk-lem-int-tensor/`
`det-lem-int-tensor-projection.proof.md`, Derived version
(blueprint: lem-pd-open-module-kflat-projection-model).

The endpoints below use the existing signed direct-sum total tensor. The localization
comparisons use the specified exact-functor factorizations and lax localization tensorator.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The source E Tot(P tensor RQ), using the existing signed direct-sum total.
Source: blueprint Derived version, termwise formula
(blueprint: lem-pd-open-module-kflat-projection-model). -/
def openModuleProjectionSource {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (P : CochainComplex (supportModules Λ U) ℤ)
    (Q : CochainComplex (supportModules Λ Z) ℤ) :
    CochainComplex (supportModules Λ Z) ℤ :=
  ((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).obj
    (HomologicalComplex.tensorObj P (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj Q))

/-- The target Tot(EP tensor Q), using the existing signed direct-sum total.
Source: blueprint Derived version, termwise formula
(blueprint: lem-pd-open-module-kflat-projection-model). -/
def openModuleProjectionTarget {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (P : CochainComplex (supportModules Λ U) ℤ)
    (Q : CochainComplex (supportModules Λ Z) ℤ) :
    CochainComplex (supportModules Λ Z) ℤ :=
  HomologicalComplex.tensorObj
    (((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).obj P) Q

/-- The canonical source comparison from e(K tensor rL) to localization of E Tot(P tensor RQ).
It is built from the exact pullback factor, localization tensorator, and exact extension factor.
Source: blueprint Derived version, K-flat identifications, proof Step 6
(blueprint: lem-pd-open-module-kflat-projection-model). -/
def openModuleProjectionSourceComparison {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (P : CochainComplex (supportModules Λ U) ℤ)
    (Q : CochainComplex (supportModules Λ Z) ℤ) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P ⊗
          (moduleObjectDerivedPullback Λ j).obj (DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj (openModuleProjectionSource Λ j P Q) :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory.map
      ((𝟙 (DerivedCategory.Q.obj P) ⊗ₘ
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app (DerivedCategory.Q.obj Q) ≫
            (upperStar Λ j).mapDerivedCategoryFactors.hom.app Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P
          (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
    (openImmersionLowerShriek Λ j).mapDerivedCategoryFactors.hom.app
      (HomologicalComplex.tensorObj P (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj Q))

/-- The canonical target comparison from eK tensor L to localization of Tot(EP tensor Q).
Source: blueprint Derived version, K-flat identifications, proof Step 6
(blueprint: lem-pd-open-module-kflat-projection-model). -/
def openModuleProjectionTargetComparison {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (P : CochainComplex (supportModules Λ U) ℤ)
    (Q : CochainComplex (supportModules Λ Z) ℤ) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⊗
        DerivedCategory.Q.obj Q ⟶
      DerivedCategory.Q.obj (openModuleProjectionTarget Λ j P Q) :=
  ((openImmersionLowerShriek Λ j).mapDerivedCategoryFactors.hom.app P ⊗ₘ
      𝟙 (DerivedCategory.Q.obj Q)) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      (((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).obj P) Q

/-- Canonical chain projection, flat/K-flat preservation, and equality with the specified mate.
Source: blueprint `det-lem-int-tensor-projection.proof.md`, Derived version
(blueprint: lem-pd-open-module-kflat-projection-model).

Proof (the nine steps of the node).
1. Use lem-pd-open-module-balanced-projection for exactness and the invertible ordinary
unit. The specified adjunction makes E preserve the small coproducts, by
lem-weil-pbc-left-adjoint-preserves-colimits. Exactness preserves acyclicity by
lem-weil-pbc-exact-functor-complex-cohomology.
2. On each insertion define Phi by theta. Naturality of theta with the first and second
differentials gives the chain equation, including (-1)^p since E is additive. The inverse
bidegree maps give the inverse chain map. Check both identities on all coproduct insertions;
the same calculation with arbitrary chain maps proves two-variable naturality.
3. Apply R, tensor with a flat module on U, and apply E to prove E preserves flatness,
using theta to identify the resulting short exact sequence. For a flat module on Z,
apply E to a short exact sequence on U, tensor, apply theta inverse, then R and the
invertible unit to prove its restriction is flat.
4. If P is K-flat and A acyclic on Z, then RA is acyclic. The defining acyclic tensor
test pur713-def-kflat-module and exactness of E show E Tot(P tensor RA) is acyclic.
Phi identifies it with Tot(EP tensor A); thus EP is K-flat, without flat-term assumptions.
5. For Q K-flat on Z and C acyclic on U, EC is acyclic. Signed symmetry (-1)^(pq)
identifies Tot(EC tensor Q) with Tot(Q tensor EC), which is acyclic. Apply R to Phi and
precompose with the invertible unit to identify Tot(C tensor RQ) with its acyclic image.
Signed symmetry gives the defining K-flat test for RQ. Step 3 gives flat terms.
6. For flat-term K-flat P,Q, use sk-def-sfb-derived-tensor-hom and the preservation just
proved. The exact factorizations of lem-weil-pbc-exact-functor-derived-factorization
and the localization tensorators give precisely the source and target comparisons below;
both are invertible. lem-pd-module-ringed-topos-derived-comparison identifies these
with the fixed section-module comparisons, preserving total tensor and K-flatness.
7. Derive the specified ordinary adjunction by lem-sfb-adjunction-localization. Its unit
and counit formulas identify the displayed eta and epsilon with localization of u and v.
The cited internal/section comparison identifies precisely these adjunctions.
8. On the double complex EP,Q the inverse of the normalized ordinary comparison of
def-sfb-condensed-pullback-tensor-comparison totals to the actual lax tensorator mu:
its inverse is the actual oplax comparison, the same one used in the internal/section
comparison. Its representative has components nu and the canonical coproduct maps.
9. The composite e(eta tensor 1), e(mu), epsilon therefore has bidegree representative
v composed with E(nu) and E(u tensor 1), exactly theta by
lem-pd-open-module-balanced-projection. Naturality of v moves each insertion past v.
Equality on insertions proves equality of chain maps; localization gives the displayed
commuting square. No boundedness, finite Tor dimension or constructibility is used. -/
theorem openModuleKFlatProjectionModel
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U Z : Scheme.{u}} [U.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (j : U ⟶ Z) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] :
    (∀ M : supportModules Λ U, ObjectProperty.flat M →
      ObjectProperty.flat ((openImmersionLowerShriek Λ j).obj M)) ∧
    (∀ P : CochainComplex (supportModules Λ U) ℤ,
      IsKFlatModuleObject U (CommMon.mk (condensedRingObj Λ U)) P →
        IsKFlatModuleObject Z (CommMon.mk (condensedRingObj Λ Z))
          (((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ Q : CochainComplex (supportModules Λ Z) ℤ,
      IsKFlatModuleObject Z (CommMon.mk (condensedRingObj Λ Z)) Q →
      (∀ n : ℤ, ObjectProperty.flat (Q.X n)) →
      IsKFlatModuleObject U (CommMon.mk (condensedRingObj Λ U))
          (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj Q) ∧
        ∀ n : ℤ, ObjectProperty.flat
          ((((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj Q).X n)) ∧
    ∃ Φ : ∀ (P : CochainComplex (supportModules Λ U) ℤ)
        (Q : CochainComplex (supportModules Λ Z) ℤ),
        openModuleProjectionSource Λ j P Q ≅ openModuleProjectionTarget Λ j P Q,
      (∀ (P : CochainComplex (supportModules Λ U) ℤ)
          (Q : CochainComplex (supportModules Λ Z) ℤ) (p q n : ℤ) (h : p + q = n),
        ∃ b : (openImmersionLowerShriek Λ j).obj
              (P.X p ⊗ (upperStar Λ j).obj (Q.X q)) ≅
            (openImmersionLowerShriek Λ j).obj (P.X p) ⊗ Q.X q,
          b.hom = openModuleBalancedProjectionMap Λ j (P.X p) (Q.X q) ∧
          (openImmersionLowerShriek Λ j).map
              (HomologicalComplex.ιTensorObj P
                (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj Q) p q n h) ≫
              (Φ P Q).hom.f n =
            b.hom ≫ HomologicalComplex.ιTensorObj
              (((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).obj P) Q p q n h ∧
          HomologicalComplex.ιTensorObj
              (((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).obj P) Q p q n h ≫
              (Φ P Q).inv.f n =
            b.inv ≫ (openImmersionLowerShriek Λ j).map
              (HomologicalComplex.ιTensorObj P
                (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj Q) p q n h)) ∧
      (∀ (P P' : CochainComplex (supportModules Λ U) ℤ)
          (Q Q' : CochainComplex (supportModules Λ Z) ℤ) (a : P ⟶ P') (b : Q ⟶ Q'),
        ((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.tensorHom a
              (((upperStar Λ j).mapHomologicalComplex (.up ℤ)).map b)) ≫ (Φ P' Q').hom =
          (Φ P Q).hom ≫ HomologicalComplex.tensorHom
            (((openImmersionLowerShriek Λ j).mapHomologicalComplex (.up ℤ)).map a) b) ∧
      ∀ (P : CochainComplex (supportModules Λ U) ℤ)
          (Q : CochainComplex (supportModules Λ Z) ℤ),
        IsKFlatModuleObject U (CommMon.mk (condensedRingObj Λ U)) P →
        (∀ n : ℤ, ObjectProperty.flat (P.X n)) →
        IsKFlatModuleObject Z (CommMon.mk (condensedRingObj Λ Z)) Q →
        (∀ n : ℤ, ObjectProperty.flat (Q.X n)) →
        IsIso (openModuleProjectionSourceComparison Λ j P Q) ∧
        IsIso (openModuleProjectionTargetComparison Λ j P Q) ∧
        openModuleProjectionSourceComparison Λ j P Q ≫ DerivedCategory.Q.map (Φ P Q).hom =
          (openImmersionLowerShriek Λ j).mapDerivedCategory.map
              ((ModuleRingedComparison.internalOpenAdjunction Λ j).unit.app
                  (DerivedCategory.Q.obj P) ▷
                (moduleObjectDerivedPullback Λ j).obj (DerivedCategory.Q.obj Q)) ≫
            (openImmersionLowerShriek Λ j).mapDerivedCategory.map
              (inv (((upperStar Λ j).leftDerivedTensorComparison.app
                ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj P))).app (DerivedCategory.Q.obj Q))) ≫
            (ModuleRingedComparison.internalOpenAdjunction Λ j).counit.app
              ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj
                (DerivedCategory.Q.obj P) ⊗ DerivedCategory.Q.obj Q) ≫
            openModuleProjectionTargetComparison Λ j P Q := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
