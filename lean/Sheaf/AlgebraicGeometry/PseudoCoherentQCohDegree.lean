/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex

/-! A single-degree reduction of quasi-coherent cohomology for pseudo-coherent complexes.

This is the degreewise local-model argument from Stacks Project, Tag 08E5.
(blueprint: lem-sc-pseudo-coherent-qcoh-degree)
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A fixed cohomology sheaf of a pseudo-coherent derived object is quasi-coherent.

Source: Stacks Project, Derived Categories of Schemes, Tag 08E5, proof of
Lemma 36.13.5.  Around each point, pseudo-coherence supplies a bounded-above complex
of finite free modules representing the restriction.  Its terms are quasi-coherent,
and the kernel of each differential and the quotient by the preceding image are
quasi-coherent by the kernel and cokernel closure results.  The local identifications
of cohomology sheaves then glue, since quasi-coherence is local on a scheme.  This
degreewise statement is the strictly smaller component from which the all-degrees
property is obtained.
(blueprint: lem-sc-pseudo-coherent-qcoh-degree)
-/
theorem schemeDerivedQCohProperty_of_isPseudoCoherent_degree
    (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory Y) (hE : IsPseudoCoherent Y E) (n : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme
