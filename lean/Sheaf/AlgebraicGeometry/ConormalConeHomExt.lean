/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.PurityNormalCone
import Sheaf.AlgebraicGeometry.ConormalGradedAlgebraHomExt

/-! # Morphism uniqueness for relative conormal spectra
Source: Stacks 0630, 0632; sk-thm-dnc, Local construction.
(blueprint: lem-pur-conormal-cone-hom-ext).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private def structureAlgebraMap {S T Y : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (f : T ⟶ Y) (hf : f ≫ p = t) :
    (Under.mk (⟨p.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj Y.sheaf) :
        S.CommAlgebraSheaf) ⟶
    Under.mk (⟨t.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} t.base).obj T.sheaf) := by
  refine Under.homMk ⟨{
    app := fun W ↦ f.appLE (p ⁻¹ᵁ W.unop) (t ⁻¹ᵁ W.unop)
      (by rw [← Scheme.Hom.comp_preimage, hf])
    naturality := ?_ }⟩ ?_
  · intro U W i
    change Y.presheaf.map _ ≫ _ = _ ≫ T.presheaf.map _
    simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    change p.app W.unop ≫ f.appLE _ _ _ = t.app W.unop
    rw [← Scheme.Hom.comp_appLE]
    subst t
    exact Scheme.Hom.appLE_eq_app (f ≫ p)

/-- Maps to an affine realization of the conormal algebra are determined by their base
map and pullback of degree-one ideal classes.
Source: Stacks 0632 and 01LX (blueprint: lem-pur-conormal-cone-hom-ext).

Proof: Compose the structure-algebra isomorphism with the two pullback maps to the
pushforward of O_T. Their degree-one components agree by the hypothesis, so
ConormalGradedAlgebra.hom_ext_degree_one makes the algebra maps equal. On each affine
open of S the inverse image in Y is affine. The Gamma--Spec adjunction identifies
its maps with the corresponding section-ring homomorphisms; hence the restrictions
of f and g agree. The inverse images of affine opens cover T, so scheme-morphism
uniqueness gives f=g. This includes empty bases and arbitrary, possibly nonaffine T. -/
theorem conormalCone_hom_ext {V S T Y : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s]
    (p : Y ⟶ S) [IsAffineHom p]
    (e : (ConormalGradedAlgebra.presentation s).algebra ≅
      Under.mk (⟨p.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj Y.sheaf))
    (t : T ⟶ S) (f g : T ⟶ Y) (hf : f ≫ p = t) (hg : g ≫ p = t)
    (h : ∀ (U : V.affineOpens)
      (b : (ConormalGradedAlgebra.power s 1).val.obj (Opposite.op U.1)),
      (f.appLE (p ⁻¹ᵁ (s ⁻¹ᵁ U.1)) (t ⁻¹ᵁ (s ⁻¹ᵁ U.1))
        (by rw [← Scheme.Hom.comp_preimage f p, hf]))
          (e.hom.right.hom.app (Opposite.op (s ⁻¹ᵁ U.1))
            (ConormalGradedAlgebra.homogeneousClass s
              (ConormalGradedAlgebra.presentation s).algebra
              (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 b)) =
      (g.appLE (p ⁻¹ᵁ (s ⁻¹ᵁ U.1)) (t ⁻¹ᵁ (s ⁻¹ᵁ U.1))
        (by rw [← Scheme.Hom.comp_preimage g p, hg]))
          (e.hom.right.hom.app (Opposite.op (s ⁻¹ᵁ U.1))
            (ConormalGradedAlgebra.homogeneousClass s
              (ConormalGradedAlgebra.presentation s).algebra
              (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 b))) :
    f = g := by
  have heq : e.hom ≫ structureAlgebraMap p t f hf =
      e.hom ≫ structureAlgebraMap p t g hg := by
    apply ConormalGradedAlgebra.hom_ext_degree_one s
    intro U b
    exact h U b
  have hfg : structureAlgebraMap p t f hf = structureAlgebraMap p t g hg :=
    (cancel_epi e.hom).mp heq
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show t x ∈ (⊤ : S.Opens) from trivial) isOpen_univ
  refine ⟨t ⁻¹ᵁ U, hxU, ?_⟩
  have : IsAffine (p ⁻¹ᵁ U).toScheme := hU.preimage p
  have hh : f.resLE (p ⁻¹ᵁ U) (t ⁻¹ᵁ U)
      (by rw [← Scheme.Hom.comp_preimage, hf]) =
    g.resLE (p ⁻¹ᵁ U) (t ⁻¹ᵁ U)
      (by rw [← Scheme.Hom.comp_preimage, hg]) := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    exact congrArg (fun a ↦ (p ⁻¹ᵁ U).topIso.hom ≫
      a.right.hom.app (Opposite.op U) ≫ (t ⁻¹ᵁ U).topIso.inv) hfg
  simpa only [Scheme.Hom.resLE_comp_ι] using congrArg (· ≫ (p ⁻¹ᵁ U).ι) hh

end AlgebraicGeometry.Etale.FiniteSmoothPurity
