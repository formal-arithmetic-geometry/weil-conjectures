/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjectionFormulaMaps
import WeilConjectures.SixFunctors.ProjectionSystemCoherence
import WeilConjectures.SixFunctors.SystemProperOpenSupport

/-! # Projection compatibility with graph refinements

Source: Stacks 0F7B, 0F7J and 0B56; the strict-system projection calculation.
(blueprint: lem-pur-system-projection-change-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.SystemProjectionFormula

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverseOnDomain_eq {C : Type*} [Category C] [HasZeroMorphisms C]
    {K M : C} (b : K ⟶ M) [IsIso b] : inverseOnDomain b = inv b := by
  simp only [inverseOnDomain, dif_pos (inferInstance : IsIso b)]

private theorem refinement_isIso (D : FiniteFieldDatum.{u})
    (o : Operations l E) (z : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {d e : Compactification f} (r : d.Refinement e) :
    IsIso (refinement l E o z.compositors z.openComparisons z.canonicalBridge
      z.properOpen r) := by
  have := d.quasiCompact_openImmersion inferInstance
  have := e.quasiCompact_openImmersion inferInstance
  have := systemProperOpenGammaIsIso l E o D z d.i (𝟙 X) r.hom e.i
    (r.i_hom.trans (Category.id_comp _).symm)
  unfold refinement
  infer_instance

private theorem refinement_inverse (D : FiniteFieldDatum.{u})
    (o : Operations l E) (z : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {d e : Compactification f} (r : d.Refinement e) (M : System l E X)
    [QuasiCompact d.i] [QuasiCompact e.i]
    (hM : IsIso ((z.properOpen.gamma d.i (𝟙 X) r.hom e.i
      (r.i_hom.trans (Category.id_comp _).symm)).app M)) :
    projectionSystemRefinement l E o z.compositors z.openComparisons z.canonicalBridge
      z.properOpen d e r (r.i_hom.trans (Category.id_comp _).symm) M hM =
    inverseOnDomain
      ((refinement l E o z.compositors z.openComparisons z.canonicalBridge
        z.properOpen r).app M) := by
  have := refinement_isIso l E D o z r
  rw [inverseOnDomain, dif_pos (inferInstance : IsIso
    ((refinement l E o z.compositors z.openComparisons z.canonicalBridge
      z.properOpen r).app M))]
  apply IsIso.eq_inv_of_hom_inv_id
  simp [projectionSystemRefinement, refinement, projectionSystemPushIdentity,
    ← Functor.map_comp, Category.assoc]

private theorem projection_inverse_refinement (D : FiniteFieldDatum.{u})
    (o : Operations l E) (z : Realizations l E D o)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))] [QuasiCompact f]
    {d e : Compactification f} (r : d.Refinement e)
    (M : System l E X) (N : System l E Y) :
    projection l E o z.compositors z.openComparisons d M N ≫
      inverseOnDomain
        ((refinement l E o z.compositors z.openComparisons z.canonicalBridge
          z.properOpen r).app
            ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N))) =
    (calculus l E Y).systemClosed.tensor.map
      (Prod.mkHom
        (inverseOnDomain
          ((refinement l E o z.compositors z.openComparisons z.canonicalBridge
            z.properOpen r).app M)) (𝟙 N)) ≫
      projection l E o z.compositors z.openComparisons e M N := by
  have := d.quasiCompact_openImmersion inferInstance
  have := e.quasiCompact_openImmersion inferInstance
  have := systemProperOpenGammaIsIso l E o D z d.i (𝟙 X) r.hom e.i
    (r.i_hom.trans (Category.id_comp _).symm)
  have hM := NatIso.isIso_app_of_isIso
    (z.properOpen.gamma d.i (𝟙 X) r.hom e.i
      (r.i_hom.trans (Category.id_comp _).symm)) M
  have hT := NatIso.isIso_app_of_isIso
    (z.properOpen.gamma d.i (𝟙 X) r.hom e.i
      (r.i_hom.trans (Category.id_comp _).symm))
    ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N))
  have h := (projectionSystemGeneratingEquations l E D o z).2.2.1
    (f.asOver (Spec (.of D.k))) d e r
    (r.i_hom.trans (Category.id_comp _).symm) M N hM hT
  have hiM := refinement_inverse l E D o z r M hM
  have hiT := refinement_inverse l E D o z r
    ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N)) hT
  erw [hiM, hiT] at h
  exact h

section Geometry
variable (D : FiniteFieldDatum.{u})
  (o : Operations l E) (z : Realizations l E D o)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [QuasiCompact g]

-- Keep the original geometric interface, although the proof works more generally.
set_option linter.unusedSectionVars false in
include D overX overY sepX sepY ftX qcX ftY qcY overF sepF ftF in
/-- The specified graph-refinement transport intertwines the two projection maps.
Source: Stacks 0F7B and 0F7J, refinement substitution in 0B56's counit projection.
(blueprint: lem-pur-system-projection-change-compatibility).

Proof: apply the intrinsic proper/open projection-mate identity to the refinement
square (d.i, id, r.hom, e.i). Insert the canonical identity direct-image comparison.
The proper-composition counit equation identifies the projection for the composite
proper morphism with the two successive proper projection maps. Naturality moves
the open tensor comparison through this word, yielding projection compatibility
with the reverse refinement transformation. Its factors are invertible by proper/open
support and the compositors. Inverting that square gives compatibility with inverse
refinement. Apply the two squares to infFst d e and infSnd d e and paste them.
Their common-refinement factors cancel, leaving exactly change d e. All maps are
formed on the ringed sequence site before evaluation. The argument works for arbitrary
system inputs; it does not invert a projection or use finite-Tor closure. -/
theorem projection_change (d e : Compactification f)
    (M : System l E X) (N : System l E Y) :
    projection l E o z.compositors z.openComparisons d M N ≫
      change l E o z.compositors z.openComparisons z.canonicalBridge z.properOpen d e
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N)) =
    (calculus l E Y).systemClosed.tensor.map
      (Prod.mkHom
        (change l E o z.compositors z.openComparisons z.canonicalBridge z.properOpen
          d e M) (𝟙 N)) ≫
      projection l E o z.compositors z.openComparisons e M N := by
  have := refinement_isIso l E D o z (Compactification.infFst d e)
  have := refinement_isIso l E D o z (Compactification.infSnd d e)
  have h₁ := projection_inverse_refinement l E D o z (Compactification.infFst d e) M N
  have h₂ := projection_inverse_refinement l E D o z (Compactification.infSnd d e) M N
  simp only [inverseOnDomain_eq] at h₁ h₂
  unfold change
  simp only [inverseOnDomain_eq]
  have : IsIso (Prod.mkHom
      (inv ((refinement l E o z.compositors z.openComparisons
        z.canonicalBridge z.properOpen (Compactification.infFst d e)).app M)) (𝟙 N)) :=
    by
      refine ⟨⟨Prod.mkHom
        ((refinement l E o z.compositors z.openComparisons z.canonicalBridge
          z.properOpen (Compactification.infFst d e)).app M) (𝟙 N), ?_, ?_⟩⟩
      · ext <;> simp
      · ext <;> simp
  apply (cancel_epi ((calculus l E Y).systemClosed.tensor.map
    (Prod.mkHom (inv ((refinement l E o z.compositors z.openComparisons
      z.canonicalBridge z.properOpen (Compactification.infFst d e)).app M)) (𝟙 N)))).mp
  simp only [← Category.assoc, ← Functor.map_comp] at h₁ h₂ ⊢
  rw [← h₁]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [h₂]
  simp


end Geometry
end WeilConjectures.SystemProjectionFormula
