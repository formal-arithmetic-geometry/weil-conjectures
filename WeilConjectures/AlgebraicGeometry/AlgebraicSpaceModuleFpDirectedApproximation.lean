/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Finite-presentation approximation of modules on qcqs algebraic spaces

Source: Stacks Project, Limits of Algebraic Spaces, Tag 07V9,
lemma-colimit-finitely-presented
(blueprint: lem-sfb-space-module-fp-directed-approximation).

The diagram and its colimit cocone live in all module sheaves on the small etale
site. Mathlib's finite-presentation predicate implies quasi-coherence of every term.
Quasi-separatedness is absolute, using the existing affine-test definition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every quasi-coherent module on a qcqs algebraic space is a small filtered colimit
of modules of finite presentation, hence of quasi-coherent modules. The natural
transformation gives the compatible maps to the specified module, and its cocone
has the universal property in all module sheaves.
Source: Stacks Project, Limits of Algebraic Spaces, Tag 07V9,
lemma-colimit-finitely-presented
(blueprint: lem-sfb-space-module-fp-directed-approximation).

Proof:
1. Apply lem-sfb-space-change-base-to-integers to view X over Spec Z. Its small etale
   site and structure sheaf are identified with the original ones, so modules,
   quasi-coherence, finite presentations and colimit cocones are unchanged.
   The same atlas and maps give the same point topology by
   def-a1-space-point-topology. Quasi-compactness is therefore unchanged, and the
   diagonal hypothesis was already absolute.
2. By lem-sfb-space-absolute-noetherian-approximation, write X as the limit of a
   small nonempty directed system with affine transitions and Noetherian stages.
   By lem-sfb-space-affine-limits-schematic-stages, every limit projection is affine.
   Choosing one index gives an affine morphism to a Noetherian algebraic space;
   no Noetherian property of X is inferred.
3. Apply lem-sfb-space-affine-noetherian-module-approximation to this projection
   and the given module M. It supplies the filtered diagram, its finitely presented
   quasi-coherent terms and its colimit cocone in all module sheaves. The ringed-site
   identification of step 1 returns the required diagram on the original X. -/
theorem exists_finitePresentation_filtered_colimit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [CompactSpace (Point X.obj.obj)] (hqs : IsAbsolutelyQuasiSeparated X)
    (M : X.Modules) [M.IsQuasicoherent] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ X.Modules),
      (∀ j : J, (D.obj j).IsFinitePresentation) ∧
        ∃ ι : D ⟶ (Functor.const J).obj M,
          Nonempty (IsColimit (Cocone.mk M ι)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
