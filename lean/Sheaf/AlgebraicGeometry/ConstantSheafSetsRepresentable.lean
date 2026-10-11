/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H1
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Constant sheaves of sets represented by disjoint unions

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), Groupoid Schemes,
Example 39.5.6 (Tag 03YW), and Lemma 59.15.8 (Tag 03O3)
(blueprint: lem-galois-constant-sheaf-sets-representable).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The presheaf represented by the disjoint union of `E` copies of `U`, restricted to
the small etale site and lifted to the universe of set-valued sheaves.
Source: Stacks Project, Tags 03YW and 03P5
(blueprint: lem-galois-constant-sheaf-sets-representable). -/
noncomputable abbrev constantSetCoproductPresheaf (U : Scheme.{u}) (E : Type u) :
    U.Etaleᵒᵖ ⥤ Type (max u (u + 1)) :=
  (Etale.forget U).op ⋙
    yoneda.obj (Over.mk (Sigma.desc (fun _ : E => 𝟙 U) : (∐ fun _ : E => U) ⟶ U)) ⋙
    uliftFunctor.{u + 1, u}

/-- (blueprint: lem-galois-constant-sheaf-sets-representable) For any scheme `U` and set `E`,
the presheaf on the small etale site of `U` represented by the disjoint union of `E` copies of
`U` is a sheaf and is canonically isomorphic to the constant sheaf of value `E`.

The coproduct codiagonal makes `∐ (_ : E), U` a `U`-scheme. A section of its representable
presheaf is a morphism over `U`; the canonical map from the constant presheaf sends `e` to
the composite of the structure map with the `e`-th coprojection.

For the proof, representable presheaves are etale sheaves by Stacks Tag 03O3. Every section
of the representable presheaf gives an `E`-indexed clopen decomposition of its domain, on
whose pieces it is the image of the respective constant element (Tag 03YW). These pieces
form an etale cover; distinct overlaps are empty, and a sheaf has one section on an empty
object. Gluing the images of these constants shows that the representable sheaf has the
universal property of sheafification of the constant presheaf (Tag 03P5). Applying that
property in both directions produces inverse morphisms and establishes the unique
factorization. For `E` empty, the coproduct is the empty scheme and the same argument
uses the empty covering. -/
theorem constantSheaf_sets_representable (U : Scheme.{u}) (E : Type u) :
    ∃ (hH : Presheaf.IsSheaf (smallEtaleTopology U)
        (constantSetCoproductPresheaf U E))
      (c : (Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E) ⟶
        constantSetCoproductPresheaf U E),
      (∀ (W : U.Etale) (e : E), ((c.app (Opposite.op W)) ⟨e⟩).down.left =
        W.hom ≫ Sigma.ι (fun _ : E => U) e) ∧
      ∃ φ : (constantSheaf (smallEtaleTopology U) (Type (max u (u + 1)))).obj
          (ULift.{u + 1, u} E) ⟶ ⟨constantSetCoproductPresheaf U E, hH⟩,
        (toSheafify (smallEtaleTopology U)
          ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))) ≫ φ.hom = c ∧
        IsIso φ ∧
        ∀ ψ : (constantSheaf (smallEtaleTopology U) (Type (max u (u + 1)))).obj
            (ULift.{u + 1, u} E) ⟶ ⟨constantSetCoproductPresheaf U E, hH⟩,
          (toSheafify (smallEtaleTopology U)
            ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))) ≫ ψ.hom = c →
            ψ = φ := sorry

end AlgebraicGeometry.Scheme
