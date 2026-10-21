/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.PointFdComplexes
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Finite cohomology of finite-dimensional complexes

Source: coefficient-point matrix realization, bounded finite-dimensional models,
Weil blueprint rationality proof, first sentence
(blueprint: lem-zl-point-finite-dimensional-complex-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A complex with finite-dimensional terms and finite term support has bounded
finite-dimensional derived cohomology. The zero complex and empty support are included.

Source: coefficient-point comparison, steps 3 and 5; homology as a kernel quotient
(blueprint: lem-zl-point-finite-dimensional-complex-cohomology).

Proof: outside the term support the middle term of the homology short complex is zero,
so its homology is zero. In every degree its homology is the quotient of the kernel of
its outgoing differential by the incoming image. Subspaces and quotients of a
finite-dimensional space are finite-dimensional. The localization comparison transports
these facts to derived cohomology.
-/
theorem pointFiniteDimensional_Q_of_finite_terms
    (E : Type u) [Field E] (K : CochainComplex (ModuleCat.{u} E) ℤ)
    (s : Finset ℤ) (hs : ∀ i : ℤ, i ∉ s → IsZero (K.X i))
    (hfinite : ∀ i : ℤ, FiniteDimensional E (K.X i)) :
    pointFiniteDimensional E (Q.obj K) := by
  constructor
  · refine ⟨s, fun i hi ↦ ?_⟩
    exact ((K.sc i).isZero_homology_of_isZero_X₂ (hs i hi)).of_iso
      ((homologyFunctorFactors (ModuleCat.{u} E) i).app K)
  · intro i
    let : FiniteDimensional E (K.X i) := hfinite i
    have : FiniteDimensional E ((K.sc i).X₂) := hfinite i
    have : FiniteDimensional E (K.sc i).homology := inferInstance
    let e : (homologyFunctor (ModuleCat.{u} E) i).obj (Q.obj K) ≅ (K.sc i).homology :=
      (homologyFunctorFactors (ModuleCat.{u} E) i).app K
    exact e.toLinearEquiv.symm.finiteDimensional

end DerivedCategory
