/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits

import WeilConjectures.AlgebraicGeometry.AffineChartRingColimitGeometric
import WeilConjectures.AlgebraicGeometry.ModuleSectionsPullbackIsoTransport

/-! # Colimit and sections comparisons for a fixed affine chart

Source: Stacks Project, Limits Tag 01ZR, affine case; Modules on Schemes Tag 01I6.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The rings of the stage charts have the fixed limit chart ring as their colimit,
and changing from the fixed limit chart to an iterated chart transports sections.
There is no finite-presentation assumption and no assertion of a stage module model.
Source: Stacks Project, Limits Tag 01ZR, first proof, affine case, and Modules on
Schemes Tag 01I6, together with pullback pasting. -/
theorem exists_affine_chart_sections_colimit_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (M : (pullback f (c.π.app (op i))).Modules)
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    let W := V.pullback₁ (pullback.fst f (c.π.app (op i)))
    let Z := W.X a
    let N := ModuleCat.of Γ(Z, ⊤) Γ((Scheme.Modules.pullback (W.f a)).obj M, ⊤)
    ∃ F : {j : I // i ≤ j} ⥤ CommRingCat.{u},
      ∃ q : colimit F ≅ Γ(Z, ⊤),
      ∀ j : {j : I // i ≤ j},
        let U : (pullback f (Spec.map (R.map (homOfLE j.property)))).OpenCover.{u} :=
          V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE j.property))))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j.val)) (c.w (homOfLE j.property).op))
        let Y := (U.pullback₁ p).X a
        let P := (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M
        ∃ (e : F.obj j ≅ Γ(U.X a, ⊤)) (s : Γ(Z, ⊤) ≅ Γ(Y, ⊤)),
          colimit.ι F j ≫ q.hom ≫ s.hom = e.hom ≫ (U.pullbackHom p a).appTop ∧
          Nonempty ((ModuleCat.extendScalars s.hom.hom).obj N ≅
            ModuleCat.of Γ(Y, ⊤) Γ(P, ⊤)) := by
  classical
  dsimp
  obtain ⟨F, q, hcompare⟩ := exists_affine_chart_ring_colimit_geometric R c hc i f V a ha
  refine ⟨F, q, ?_⟩
  intro j
  obtain ⟨e, h, hg, hmap⟩ := hcompare j
  refine ⟨e, Scheme.Γ.mapIso h.op, hmap, ?_⟩
  exact nonempty_module_sections_pullback_iso_transport h _ _ hg M


end AlgebraicGeometry
