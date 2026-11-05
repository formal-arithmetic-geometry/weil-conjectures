/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Acyclic tensor tests along tensor-compatible equivalences

Let `F : C ⥤ D` be an additive equivalence of abelian monoidal categories together with a
natural isomorphism `F (X ⊗ Y) ≅ F X ⊗ F Y`. Applied termwise, `F` carries total tensor
complexes to total tensor complexes, and it preserves and reflects the acyclic tensor test
for K-flatness: `Tot(Z ⊗ P)` is acyclic for every acyclic `Z`.

No monoidal coherence of the comparison isomorphism is needed.

Source: Stacks Project, Cohomology on Sites, Tag 06YN
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

end CochainComplex
