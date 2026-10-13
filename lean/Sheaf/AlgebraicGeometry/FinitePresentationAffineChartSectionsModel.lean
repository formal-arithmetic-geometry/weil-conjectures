/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation

/-! # Algebraic models for affine chart sections
Source: Stacks Project, Tags 01ZR and 05N7. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The finite presentation of the restricted module descends as algebraic sections.
Source: Stacks Project, Algebra Tag 05N7 and Limits Tag 01ZR, affine object clause.
(blueprint: lem-pc-fp-affine-chart-sections-model).

Proof: On the upper tail above i the stage chart rings are base changes of the fixed
chart ring. Affine pullback identifies these with tensor products, which commute
with directed colimits. Uniqueness of the affine limit identifies the limit chart
ring with that colimit. The restriction of M has finitely presented sections since
it is finitely presented and the chart is affine. Apply the object clause of module
descent over a directed preorder: lift a finite relation matrix and form its range
quotient at a stage. Its scalar extension is the original sections module. The
pullback pasting isomorphism identifies the limit chart with the iterated chart
in the conclusion, and transports the section comparison. Zero rings and modules
are treated by the same relation quotient; no choice of unspecified sheaf data
is made. -/
theorem exists_finitePresentation_affine_chart_sections_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent)
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    ∃ (j : I) (hij : i ≤ j),
      let U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u} :=
        V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE hij))))
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      let Y := (U.pullback₁ p).X a
      let P := (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M
      ∃ Q : ModuleCat.{u} Γ(U.X a, ⊤),
        Module.FinitePresentation Γ(U.X a, ⊤) Q ∧
        Nonempty ((ModuleCat.extendScalars (U.pullbackHom p a).appTop.hom).obj Q ≅
          ModuleCat.of Γ(Y, ⊤) Γ(P, ⊤)) := by sorry

end AlgebraicGeometry
