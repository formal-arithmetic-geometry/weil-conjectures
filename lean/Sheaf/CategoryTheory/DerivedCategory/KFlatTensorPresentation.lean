/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # A chosen derived tensor computed by K-flat resolutions

Source: the finite Tor amplitude paragraph in the blueprint proof of
`det-proper-image-localizing-open` (blueprint: def-sf-kflat-tensor-presentation).
The binary total tensor is the existing signed direct-sum total tensor. K-flatness
uses its existing two-sided quasi-isomorphism test, equivalently the acyclic test.
-/

@[expose] public section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- A presentation of the specified derived tensor by signed total tensors of K-flat
resolutions. Its comparison is natural on all complexes and invertible on K-flat pairs;
the resolution clause makes it compute the tensor on every unbounded derived object.
Source: blueprint finite Tor amplitude paragraph of `det-proper-image-localizing-open`
(blueprint: def-sf-kflat-tensor-presentation). -/
structure KFlatTensorPresentation
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [MonoidalCategory (DerivedCategory A)] where
  /-- Every unbounded complex admits a K-flat quasi-isomorphism onto it. -/
  resolution : ∀ X : CochainComplex A ℤ,
    ∃ (P : CochainComplex A ℤ) (s : P ⟶ X), P.IsKFlatForTotalTensor ∧ QuasiIso s
  /-- The derived tensor comparison on complexes. -/
  comparison :
    (((Functor.whiskeringLeft₂ _).obj (Q (C := A))).obj Q).obj
        (curriedTensor (DerivedCategory A)) ⟶
      (Functor.postcompose₂.obj (Q (C := A))).obj
        ((curriedTensor A).map₂CochainComplex)
  /-- K-flat pairs compute the chosen tensor. -/
  isIso : ∀ (P T : CochainComplex A ℤ), P.IsKFlatForTotalTensor →
    T.IsKFlatForTotalTensor → IsIso ((comparison.app P).app T)

end DerivedCategory
