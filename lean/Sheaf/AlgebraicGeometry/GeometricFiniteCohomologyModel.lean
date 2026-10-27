/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Finite representation cohomology of a constructible field complex

Source: blueprint six-functors direct-images proof, paragraph (3);
Bhatt--Scholze, Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-geometric-finite-cohomology-model).

The continuous-function model is the existing `LisseTransport`: its `sections`, `scalar`,
`action` and `restriction` fields specify precisely the equivariant condensation of a
norm-continuous representation. No separate construction of that model is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FieldActionTransport

open CondensedGalois

/-- Bounded constructible field complexes have lisse cohomology and bounded
finite-dimensional continuous representation cohomology. Here `e` is the normalized
field equivalence and `L` its lisse realization from
`lem-sfb-field-action-derived-section-transport`. In the displayed isomorphism the
right-hand side has sections `C(P, (W q).obj.V)` by `L.sections`; `L.scalar`, `L.action`
and `L.restriction` identify all operations with pointwise operations and precomposition.
`Subsingleton (W q).obj.V` says that the vector space is zero outside the finite interval.
Source: blueprint direct-images paragraph (3); Bhatt--Scholze Example 4.1.10,
Definition 6.8.3 and Proposition 6.8.4; Hemo--Richarz--Scholbach Example 3.1
(blueprint: lem-sfb-geometric-finite-cohomology-model).

Proof plan:
1. By sk-def-sfb-bounded-constructible every H^q(M) is constructible. Spec k has one
   point, so the unique nonempty stratum of def-sfb-constructible-module is Spec k:
   a nonempty immersion into Spec k is an isomorphism. Thus
   def-sfb-locally-finitely-presented and def-sfb-finitely-presented-module give local
   finite presentations over the original pulled-back continuous-function ring.
2. The equivalence def-weil-pbc-internal-abelian-sheaf-module-equivalence preserves
   the section modules, finite sums and cokernels. Apply
   lem-weil-pbc-condensed-lfp-local-triviality to these presentations on Spec k,
   whose topology is Noetherian. Translate back to obtain
   def-sfb-lisse-coefficient-module, allowing rank zero.
3. The exact normalized field equivalence commutes with kernels, images and cokernels.
   Apply lem-weil-pbc-exact-functor-complex-cohomology on representatives. Naturality
   descends to the ordinary derived localization, identifying H^q(D(e)M) with e(H^q M).
4. Apply the lisse realization of lem-sfb-field-action-derived-section-transport.
   The explicit reconstruction of lem-sfb-field-free-orbit-norm-lisse-reconstruction
   gives finite norm-continuous W_q and the pointwise scalar and variable-action
   formulas and precomposition restrictions. Compose with the comparison in step 3.
5. Choose ordered finite bounds for M. Exactness preserves zero cohomology, so the
   same bounds work after D(e). Choose W_q to be zero outside that interval and use
   step 4 in the remaining degrees. For M=0 take a=b=0 and all W_q=0. Trivial G and
   empty profinite tests satisfy the same formulas. No invariants or arithmetic
   cohomological-dimension bound is used.
-/
theorem geometric_finite_cohomology_model
    (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    [CategoryTheory.CondensedBar.ActionAbelian (normCoefficients E) (ks ≃ₐ[k] ks)]
    (e : FieldData k ks (normCoefficients E)) (L : LisseTransport k ks E e)
    (M : DerivedCategory.{u + 2} (Modules (normCoefficients E).toMon (Spec (.of k))))
    (hM : boundedConstructible (condensedRingObj (normCoefficients E).X (Spec (.of k))) M) :
    (∀ q : ℤ, IsLisseCoefficientModule (normCoefficients E).X
      ((DerivedCategory.homologyFunctor _ q).obj M)) ∧
    DerivedCategory.TStructure.t.bounded ((fieldFunctor k ks e).mapDerivedCategory.obj M) ∧
    ∃ (a b : ℤ) (W : ℤ → NormContinuousRepresentations E (ks ≃ₐ[k] ks)),
      a ≤ b ∧
      (∀ q : ℤ, Nonempty
        ((DerivedCategory.homologyFunctor _ q).obj
            ((fieldFunctor k ks e).mapDerivedCategory.obj M) ≅
          (fieldFunctor k ks e).obj (L.equivalence.inverse.obj (W q)).obj)) ∧
      ∀ q : ℤ, q < a ∨ b < q → Subsingleton (W q).obj.V := by
  sorry

end AlgebraicGeometry.ProEtale.FieldActionTransport
