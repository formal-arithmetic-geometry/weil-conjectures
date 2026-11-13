/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiSectionUnitEquation

/-! # The top-open comparison unit equation

## References

* [Stacks, Tag 09ZF], [Stacks, Tags 03CB, 03CC]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The explicit section comparison carries the topological unit to the etale unit. -/
theorem gabber_h0_zariski_top_unit_equation
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (beta : (gabberZariskiPull (pullback.snd i h)).obj (gabberZariskiG h F) ⟶
      gabberZariskiH i h F)
    (hbeta : GabberZariskiUnitCompatible i h F beta) :
    ∀ s : (gabberZariskiG h F).obj.obj (op (⊤ : X'.Opens)),
    (gabberZariskiCompare i h F ∘ beta.hom.app (op (⊤ : (pullback i h).Opens)))
      (gabberZariskiUnit (pullback.snd i h) (gabberZariskiG h F) ⊤ s) =
    eqToHom (congrArg
      (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
          (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
      (etaleSetDescentComparison h (pullback.snd i h) F
        (Scheme.Etale.mk (𝟙 X)) (gabberZariskiLift h F s)) := by
  have hb : beta.hom.app (op (⊤ : (pullback i h).Opens)) ∘
      gabberZariskiUnit (pullback.snd i h) (gabberZariskiG h F) ⊤ =
    (((Scheme.etaleSetPullback (pullback.snd i h)).obj
      ((Scheme.etaleSetPullback h).obj F)).obj.map
        (gabberPreimageEtaleIso (pullback.snd i h) ⊤).hom.op) ∘
    (etaleSetDescentUnit (pullback.snd i h)
      ((Scheme.etaleSetPullback h).obj F) (Scheme.Etale.mk (⊤ : X'.Opens).ι)) :=
    funext (hbeta ⊤)
  have ht := congrArg (fun f ↦ gabberZariskiCompare i h F ∘ f) hb
  have hc := gabber_h0_zariski_section_unit_equation i h F
  intro s
  exact congrFun (ht.trans hc) s

end AlgebraicGeometry
