/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.ModuleFilteredColimitFinitePresentation

/-! # Directed colimit by finite-presentation modules

Source: Stacks Project, Properties, Lemma 01PK (blueprint:
lem-weil-pbc-module-directed-colimit-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module on a qcqs scheme is a directed colimit of modules of finite
presentation. Source: Stacks Project, Properties, Lemma 01PK (blueprint:
lem-weil-pbc-module-directed-colimit-finite-presentation).
(blueprint: lem-weil-pbc-module-directed-colimit-finite-presentation)

Apply the filtered-category version (01PJ), then Categories, Lemma 0032, to obtain a final
functor from a nonempty directed partial order to the filtered index category. Precompose
the diagram with this functor and whisker its cocone. Finite presentation holds termwise,
and finality preserves the colimit property with the same vertex and selected cocone legs.
-/
theorem exists_directedColimit_finitePresentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·)),
      ∃ (D : I ⥤ X.Modules),
        (∀ i : I, (D.obj i).IsFinitePresentation) ∧
        ∃ (φ : D ⟶ (Functor.const I).obj F),
          Nonempty (IsColimit (Cocone.mk F φ)) := by
  obtain ⟨J, hJ, hfiltered, M, hfp, φ, ⟨hc⟩⟩ :=
    exists_filteredColimit_of_isQuasicoherent X F
  obtain ⟨I, horder, hdir, hne, G, hfinal⟩ := IsFiltered.exists_directed J
  refine ⟨I, horder.toPreorder, hne, hdir, G ⋙ M, fun i ↦ hfp (G.obj i),
    (Cocone.mk F φ).whisker G |>.ι, ?_⟩
  exact ⟨(Functor.Final.isColimitWhiskerEquiv G (Cocone.mk F φ)).symm hc⟩

end AlgebraicGeometry.Scheme.Modules
