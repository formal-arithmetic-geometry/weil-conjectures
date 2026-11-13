/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTrace
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDegreeSplitAt
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitComponent

/-!
# Trace after restriction for a finite étale morphism of fixed degree

## References

* Stacks Project, Section 03SH, the paragraph following Definition 03SE; local splitting is
  Lemma 04HN.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Restriction followed by trace is multiplication by the prescribed finite locally free
degree. (Stacks, Section 03SH, paragraph following Definition 03SE.) -/
theorem finiteEtaleTrace_comp_restriction
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (d : ℕ) [f.IsFiniteLocallyFreeOfDegree d] :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      finiteEtaleRestriction f F ≫ finiteEtaleTrace f F = d • 𝟙 F := by
  classical
  intro F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  obtain ⟨W⟩ := W
  let C := finiteEtaleRestriction f F ≫ finiteEtaleTrace f F
  have hlocal (w : W.left) := exists_finiteEtale_degree_split_at f d W w
  choose V a v hv D i hc hi hp using hlocal
  have hcover : Sieve.ofArrows V a ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
    apply Set.eq_univ_of_forall
    intro w
    exact Set.mem_iUnion.mpr ⟨w, v w, hv w⟩
  apply F.property.hom_ext_ofArrows a hcover
  intro w
  have hs := finiteEtaleTrace_comp_restriction_app_of_split f F (V w)
    (ULift.{u} (Fin d)) (D w) (i w) (hc w) (hi w) (hp w)
  change C.hom.app (Opposite.op W) ≫ F.obj.map (a w).op =
    (d • 𝟙 F).hom.app (Opposite.op W) ≫ F.obj.map (a w).op
  rw [← C.hom.naturality]
  simp only [Fintype.card_ulift, Fintype.card_fin] at hs
  rw [show C.hom.app (Opposite.op (V w)) = d • 𝟙 (F.obj.obj (Opposite.op (V w))) from hs]
  change F.obj.map (a w).op ≫ (d • 𝟙 (F.obj.obj (Opposite.op (V w)))) =
    (d • (𝟙 F.obj)).app (Opposite.op W) ≫ F.obj.map (a w).op
  simp

end AlgebraicGeometry.Etale
