/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Morphisms out of bounded above complexes of projectives in the derived category

Let `P` be a bounded above cochain complex whose terms are projective. Then `P` is K-projective
(`CochainComplex.isKProjective_of_projective`), so that:

* every morphism `Q.obj P ⟶ Q.obj L` in the derived category is the image of a chain map
  (`DerivedCategory.Q_map_surjective_of_projective`);
* two chain maps `f g : P ⟶ L` have the same image in the derived category if and only if
  they are homotopic (`DerivedCategory.Q_map_eq_Q_map_iff_of_projective`).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

end DerivedCategory
