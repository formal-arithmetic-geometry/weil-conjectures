/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective

import WeilConjectures.AlgebraicGeometry.EtaleClosedSectionShrink
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageSectionDescription

/-! # Local representatives around a closed subscheme

## References

* Stacks Project, Tag 09ZF
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Local sections whose unit equations hold on the entire closed base changes.
(Stacks, Tag 09ZF) -/
theorem etale_closed_section_local_family
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X))))) :
    ∃ (J : Type u) (U : J → X.Etale) (s : ∀ j, F.obj.obj (op (U j))),
      Set.range i ⊆ ⋃ j, Set.range (U j).hom ∧
      ∀ j, etaleSetDescentUnit i F (U j) (s j) =
        ((Scheme.etaleSetPullback i).obj F).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ i).map
            (MorphismProperty.Over.homMk (U j).hom (Category.comp_id _) :
              U j ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
  classical
  let B := MorphismProperty.Over.pullback @Etale ⊤ i
  let H := (Scheme.etaleSetPullback i).obj F
  let e : Scheme.Etale.mk (𝟙 Z) ≅ B.obj (Scheme.Etale.mk (𝟙 X)) :=
    (MorphismProperty.Over.mkIdTerminal @Etale Z).uniqueUpToIso
      ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _)
  obtain ⟨J, V, π, hπ, hrep⟩ := etaleInverseImageSectionDescription X Z i F
    (H.obj.map e.hom.op t)
  have hlocal : ∀ j, ∃ (U : X.Etale) (s : F.obj.obj (op U)),
      Set.range ((V j).hom ≫ i) ⊆ Set.range U.hom ∧
      etaleSetDescentUnit i F U s = H.obj.map
        (B.map (MorphismProperty.Over.homMk U.hom (Category.comp_id _) :
          U ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
    intro j
    obtain ⟨U, a, s, hs⟩ := hrep j
    have ht : H.obj.map
        (((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).from (V j)).op t =
        H.obj.map a.op (etaleSetDescentUnit i F U s) := by
      rw [← Functor.map_comp_apply, ← op_comp] at hs
      have he : π j ≫ e.hom =
          ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).from (V j) :=
        ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).hom_ext _ _
      rw [he] at hs
      exact hs
    exact etale_closed_section_shrink i F t (V j) U a s ht
  choose U s hr he using hlocal
  refine ⟨J, U, s, ?_, he⟩
  rintro x ⟨z, rfl⟩
  have hc := (Scheme.ofArrows_mem_smallEtaleTopology_iff π).mp hπ
  have hz : z ∈ ⋃ j, Set.range (π j).left := by rw [hc]; trivial
  obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hz
  have hπhom : (π j).left = (V j).hom := by
    have h := MorphismProperty.Over.w (π j)
    change (π j).left ≫ 𝟙 Z = (V j).hom at h
    exact (Category.comp_id ((π j).left)).symm.trans h
  apply Set.mem_iUnion.mpr
  refine ⟨j, hr j ?_⟩
  refine ⟨y, ?_⟩
  change i ((V j).hom y) = i z
  rw [← hπhom]
  exact congrArg i hy

end AlgebraicGeometry
