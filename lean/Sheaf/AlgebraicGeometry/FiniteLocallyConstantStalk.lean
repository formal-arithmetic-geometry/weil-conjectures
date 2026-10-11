/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite geometric stalks of finite locally constant sheaves of sets

Source: Stacks Project, Etale Cohomology, Definition 03RU (4), Lemma 03Q1 (3),
and Remark 03P5 (blueprint: lem-galois-flc-set-stalk-finite).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-galois-flc-set-stalk-finite) Stacks Project, Etale Cohomology,
Definition 03RU (4), Lemma 03Q1 (3), and Remark 03P5. Lift the geometric point to
one member of the etale cover. The stalk of the restricted sheaf surjects onto
the original stalk by reindexing pointed etale neighbourhoods using a fibre
product. The local sheaf isomorphism gives an isomorphism on stalks. The stalk
of a constant sheaf is a quotient of its constant value: sheafification
preserves stalks, and every germ of the constant presheaf comes from the
terminal pointed neighbourhood. Thus a finite local value, including the
empty set, gives a finite geometric stalk. -/
theorem finite_stalk_of_finite_locally_constant_sets {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y,
      ∀ i, ∃ S : Type (u + 1), Finite S ∧
        Nonempty ((F.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (Type (u + 1))).obj S)) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite ((pointSmallEtale s).sheafFiber.obj F) := by
  sorry

end AlgebraicGeometry.Scheme
