/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Filtered.Basic

/-! # Directed colimit by finite-presentation modules

Source: Stacks Project, Properties, Lemma 01PK (blueprint:
lem-weil-pbc-module-directed-colimit-finite-presentation).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module on a qcqs scheme is a directed colimit of modules of finite
presentation. Source: Stacks Project, Properties, Lemma 01PK (blueprint:
lem-weil-pbc-module-directed-colimit-finite-presentation).
(blueprint: lem-weil-pbc-module-directed-colimit-finite-presentation)

The proof proceeds by applying the filtered-category version (01PJ), dualizing its colimit
cone, and reindexing the resulting cofiltered limit by a directed set using Categories,
Lemma 0032; the cocone axioms and colimit property are then transported back along the
opposite-category equivalence.
-/
theorem exists_directedColimit_finitePresentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·)),
      ∃ (D : I ⥤ X.Modules),
        (∀ i : I, (D.obj i).IsFinitePresentation) ∧
        ∃ (φ : D ⟶ (Functor.const I).obj F),
          Nonempty (IsColimit (Cocone.mk F φ)) := by sorry

end AlgebraicGeometry.Scheme.Modules
