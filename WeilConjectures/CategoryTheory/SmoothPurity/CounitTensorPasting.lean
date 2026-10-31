/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction

/-! # Pasting coefficient-linear counit squares -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory

/-- Counit squares for two successive tensor actions paste without changing their maps.
Source: Mathlib adjunction composition, applied in the ordered affine trace argument
(blueprint: lem-pur-counit-tensor-pasting).

Proof: expand the composite counit. Naturality of the inner counit commutes the
mapped outer right comparison across it. Apply the inner counit square and then
the outer counit square. Functoriality combines the two counit factors. -/
theorem counitTensor_pasting
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : D ⥤ C} {R : C ⥤ D} {J : E ⥤ D} {U : D ⥤ E}
    (a : L ⊣ R) (j : J ⊣ U)
    (B : C ⥤ C) (B1 : D ⥤ D) (B2 : E ⥤ E)
    (s : ∀ M, B2.obj (U.obj M) ≅ U.obj (B1.obj M)) (K : C)
    (c : B1.obj (R.obj K) ≅ R.obj (B.obj K))
    (p : L ⋙ B ⟶ B1 ⋙ L)
    (e : ∀ M : E, B1.obj (J.obj M) ⟶ J.obj (B2.obj M))
    (ho : ∀ M : D, e (U.obj M) ≫ J.map ((s M).hom) ≫
      j.counit.app (B1.obj M) = B1.map (j.counit.app M))
    (hp : B.map (a.counit.app K) =
      p.app (R.obj K) ≫ L.map c.hom ≫ a.counit.app (B.obj K)) :
    p.app (J.obj (U.obj (R.obj K))) ≫ L.map (e (U.obj (R.obj K))) ≫
      (J ⋙ L).map ((s (R.obj K)).hom ≫ U.map c.hom) ≫
      (AlgebraicGeometry.Etale.affineTraceComposeAdjunction j a).counit.app (B.obj K) =
        B.map ((AlgebraicGeometry.Etale.affineTraceComposeAdjunction j a).counit.app K) := by
  have hn := congrArg (fun f ↦ L.map f) (j.counit.naturality c.hom)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hn
  rw [AlgebraicGeometry.Etale.affineTraceComposeAdjunction_counit,
    AlgebraicGeometry.Etale.affineTraceComposeAdjunction_counit]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  have hoK := congrArg (fun f ↦ L.map f) (ho (R.obj K))
  simp only [Functor.map_comp] at hoK
  rw [reassoc_of% hoK]
  have hpn := p.naturality (j.counit.app (R.obj K))
  simp only [Functor.comp_map] at hpn
  rw [← reassoc_of% hpn, ← hp, ← B.map_comp]

end CategoryTheory
