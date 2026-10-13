/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.Algebra.FinitePresentationColimit

/-! # Descent of a retraction between fixed finitely presented models

Source: Stacks Project, More on Algebra, Tag 0BC7, first proof paragraph,
using Algebra, Tag 05N7, map and equality clauses.
(blueprint: lem-pc-fp-colimit-retraction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

/-- A retraction between two fixed finitely presented models descends to a later stage.
Source: Stacks Project, More on Algebra, Tag 0BC7, label lemma-colimit-perfect,
first proof paragraph, using Algebra, Tag 05N7, (2) and (3).
(blueprint: lem-pc-fp-colimit-retraction).

Proof: Replace the directed preorder by its antisymmetrization and transport the ring
colimit and the fixed models along the equivalence of indexing categories. Apply the
map clause of finitePresentation_descent_directedColimit separately to s and r.
Directedness supplies a common stage above both stages; extend both maps to that
stage. Use extendScalarsComp and cocone naturality to identify their further scalar
extensions with s and r. The comparison isomorphisms in the map clause agree with
these canonical ones because they agree on all tensors 1 tensor m, which generate
the base changes. Thus the composite of the two descended maps becomes the identity
after extending to the colimit. Finite presentation is preserved by scalar extension.
Apply the equality clause to this composite and the identity, then extend both maps
to the resulting later stage. Functoriality makes their composite the identity there.
The canonical iterated scalar-extension isomorphism for M gives eM. Lift this stage
and these maps back to the original preorder. For zero models the maps are zero and
the identity of the zero module is zero; for a singleton diagram this is ordinary
transport of a retraction along a ring isomorphism. -/
theorem exists_retraction_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (i : I) (M N : ModuleCat.{u} (F.obj i))
    (hM : Module.FinitePresentation (F.obj i) M)
    (hN : Module.FinitePresentation (F.obj i) N)
    (s : (extendScalars (colimit.ι F i).hom).obj M ⟶
      (extendScalars (colimit.ι F i).hom).obj N)
    (r : (extendScalars (colimit.ι F i).hom).obj N ⟶
      (extendScalars (colimit.ι F i).hom).obj M)
    (hsr : s ≫ r = 𝟙 _) :
    ∃ (j : I) (hij : i ≤ j),
      let E := extendScalars (F.map (homOfLE hij)).hom
      ∃ (s' : E.obj M ⟶ E.obj N) (r' : E.obj N ⟶ E.obj M),
        s' ≫ r' = 𝟙 _ ∧
        Nonempty ((extendScalars (colimit.ι F j).hom).obj (E.obj M) ≅
          (extendScalars (colimit.ι F i).hom).obj M) := by sorry

end ModuleCat
