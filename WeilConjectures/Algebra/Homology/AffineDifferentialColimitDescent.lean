/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.FinitePresentationColimit

/-! # Descent of differentials on fixed bounded graded module models

Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1), descent of maps and relations.
(blueprint: lem-pc-affine-differential-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- On fixed bounded finitely presented term models, the differentials and their zero-composite
relations descend after extending those models to a later stage.
Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1), via Algebra, Tag 05N7.
(blueprint: lem-pc-affine-differential-colimit-descent).

Proof: Transport each differential of P across the given term isomorphisms. Only adjacent
pairs with both degrees in [a,b] can have a nonzero differential. Descend this finite list
by the map clause of finite-presentation colimit descent, and choose one common later stage.
Use the canonical iterated extension-of-scalars isomorphisms to keep all the descended maps
compatible with one common family of term isomorphisms. Each consecutive composite becomes
zero after extension to the colimit, because it is conjugate to a composite in P. Apply the
equality clause of finite-presentation colimit descent to these finitely many composites
and the zero maps, and pass to a common later stage. Put zero in nonadjacent degrees and
where either term is outside the interval; scalar extension preserves zero objects, so
compatibility there is automatic. Composition of the retained adjacent maps is zero by
the imposed relations; all other composites contain a zero map. Return the maps and the
compatible term isomorphisms. No complex is constructed here. For a preorder, pass to its
antisymmetrization as an indexing category to use the partial-order finite-presentation
lemma and lift the later index back (equivalence preserves and reflects the order relation).
For an empty interval all models are zero, so all returned maps are zero. -/
theorem exists_differentials_on_graded_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (P : CochainComplex (ModuleCat.{u} (colimit F : CommRingCat.{u})) ℤ)
    (i : I) (M : ℤ → ModuleCat.{u} (F.obj i)) (a b : ℤ)
    (hzero : ∀ n : ℤ, n < a ∨ b < n → IsZero (M n))
    (hfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i) (M n))
    (e : ∀ n : ℤ, (ModuleCat.extendScalars (colimit.ι F i).hom).obj (M n) ≅ P.X n) :
    ∃ (j : I) (hij : i ≤ j),
      let G := ModuleCat.extendScalars (F.map (homOfLE hij)).hom
      let E := ModuleCat.extendScalars (colimit.ι F j).hom
      ∃ (d : ∀ m n : ℤ, G.obj (M m) ⟶ G.obj (M n))
        (e' : ∀ n : ℤ, E.obj (G.obj (M n)) ≅ P.X n),
        (∀ m n : ℤ, ¬ (ComplexShape.up ℤ).Rel m n → d m n = 0) ∧
        (∀ m n k : ℤ, d m n ≫ d n k = 0) ∧
        (∀ m n : ℤ, (e' m).hom ≫ P.d m n = E.map (d m n) ≫ (e' n).hom) := by
  sorry

end CochainComplex
