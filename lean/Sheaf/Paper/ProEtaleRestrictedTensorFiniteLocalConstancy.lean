/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.Paper.ProEtaleConstantModulePullbackHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.LocallyConstantTensor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Finite local constancy of a restricted derived tensor

Source: Stacks Project, Cohomology on Sites, Tags 094H and 07A4.
(blueprint: lem-pur-proetale-restricted-tensor-finite-local-constancy).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A bounded-above tensor is finite locally constant after restriction whenever
its input cohomology sheaves are finite locally constant there. Zero input cohomology
sheaves need no local-model hypothesis. The coefficient ring is any finite commutative
ring, and the restricting morphism is arbitrary.

Source: Stacks Project, Cohomology on Sites, Tag 094H,
lemma-locally-constant-tensor-product, and Tag 07A4, lemma-pullback-tensor-product.
(blueprint: lem-pur-proetale-restricted-tensor-finite-local-constancy).

Proof: use proEtaleConstantModulePullbackHomologyIso to identify the cohomology
of the exact termwise pullback with the restriction of input cohomology. The
canonical coefficient comparison and exactness are proved in its imported module.
In degree j with zero input cohomology its restriction
is zero, which is the constant zero module; in the other degrees use the given
finite locally constant models. A local model on a nonempty covering member has
finite underlying module: choose a geometric point of that member and identify
the stalk with the model value. On empty covering members replace the model by
zero. Finite modules are finitely generated. Thus every restricted input cohomology
is locally constant of finite type. The termwise pulled-back complexes
have the given upper bounds.
A finite ring is Noetherian. Apply the locally constant tensor theorem, Tag 094H,
on the small model of the pro-etale site, with the lifted coefficient ring ULift A.
For representatives choose K-flat flat-term resolutions; the canonical tensor
pullback comparison, Tag 07A4, identifies their tensor with the restriction of the
original derived tensor. K-flatness makes this independent of the given resolution
P and permits using the original second factor L. Transport the resulting
cohomology isomorphism back to the pro-etale site. A finitely generated module over
a finite ring is finite. Its constant sheaf has those module values as geometric
stalks, so the local models give both local constancy and finite stalks of the
restricted tensor cohomology. No lower bound on the tensor is used. -/
theorem proEtale_restrictedTensor_finiteLocalConstancy
    {T X : Scheme.{u}} (a : X ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (K L P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := proEtaleConstantRing T A) P)
    (hKb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      (((proEtaleConstantModulePullbackFunctor a A).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj K).homology j))
    (hLb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      (((proEtaleConstantModulePullbackFunctor a A).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj L).homology j))
    (hK : ∀ j : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
          (DerivedCategory.Q.obj K)) →
      IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback a A
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T A)) j).obj (DerivedCategory.Q.obj K))) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback a A ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
              (DerivedCategory.Q.obj K)))))
    (hL : ∀ j : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
          (DerivedCategory.Q.obj L)) →
      IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback a A
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T A)) j).obj (DerivedCategory.Q.obj L))) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback a A ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
              (DerivedCategory.Q.obj L)))))
    (i : ℤ) :
    IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback a A
      ((DerivedCategory.homologyFunctor (proEtaleRingModules T
        (proEtaleConstantRing T A)) i).obj (derivedTensor T A K L P f hf hP))) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
        (proEtaleConstantModulePullback a A ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj
            (derivedTensor T A K L P f hf hP)))) := by
  sorry

end AlgebraicGeometry.Scheme
