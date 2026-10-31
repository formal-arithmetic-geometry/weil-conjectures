/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels

/-!
# Projection formula and finite coefficient reduction

Source: current blueprint latest, sec-six-functors,
sk-prop-sf-pf-coherence/prop-sf-pf-reduction (blueprint: prop-sf-pf-reduction).
The proposition uses ordinary unbounded etale categories and reduction retained
as an endofunctor of the original coefficient category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option relaxedAutoImplicit false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicGeometry.Etale CategoryTheory.Limits MonoidalCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The three clauses of compatibility with finite reduction, for any finite ring
and any ideal, on the ordinary unbounded etale derived categories.
The square uses the proper-counit/open-unit projection and its specified reduction
comparison. No boundedness, constructibility or Tor-amplitude condition is imposed.
Source: current blueprint latest, prop-sf-pf-reduction (1)-(3)
(blueprint: prop-sf-pf-reduction).
The first conjunct is the full morphism equality stated by
`projectionMapOfCompactification_constantSingle`, with M = Λ/J; `type_of%`
preserves its derived monoidal instance exactly.
Proof: specialize the constant-coefficient associativity square to the quotient
module. The finite proper projection theorem and the open tensor isomorphism make
both projection maps invertible. Cancellation of the three vertical isomorphisms
identifies invertibility of the reduced map with that of the lower projection. -/
theorem projectionFiniteReduction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (J : Ideal Λ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let A := ModuleCat.{u + 1} Λ
    (type_of% (projectionMapOfCompactification_constantSingle A c
      (ModuleCat.of Λ (Λ ⧸ J)) K L)) ∧
    (IsIso ((reductionModIdeal Λ Y J).map
        (((AlgebraicGeometry.Etale.projectionMapOfCompactification A c).app K).app L)) ↔
      IsIso (((AlgebraicGeometry.Etale.projectionMapOfCompactification A c).app K).app
        ((reductionModIdeal Λ Y J).obj L))) ∧
    (IsIso (((AlgebraicGeometry.Etale.projectionMapOfCompactification A c).app K).app L) ↔
      IsIso (((AlgebraicGeometry.Etale.projectionMapOfCompactification A c).app K).app
        ((reductionModIdeal Λ Y J).obj L))) ∧
    IsIso (((AlgebraicGeometry.Etale.projectionMapOfCompactification A c).app K).app L) ∧
    IsIso (((AlgebraicGeometry.Etale.projectionMapOfCompactification A c).app K).app
      ((reductionModIdeal Λ Y J).obj L)) := by
  dsimp only
  let : HasCompactification f := c.hasCompactification
  have hK := (hasProjectionFormulaOfCompactification_iff Λ c K L).mpr
    (by simpa only using (hasProjectionFormula_of_finite Λ f K L))
  have hL := (hasProjectionFormulaOfCompactification_iff Λ c K
    ((reductionModIdeal Λ Y J).obj L)).mpr
      (by simpa only using (hasProjectionFormula_of_finite Λ f K
        ((reductionModIdeal Λ Y J).obj L)))
  exact ⟨projectionMapOfCompactification_constantSingle (ModuleCat.{u + 1} Λ) c
      (ModuleCat.of Λ (Λ ⧸ J)) K L,
    isIso_reductionModIdeal_map_projectionMapOfCompactification_iff Λ J c K L,
    ⟨fun _ ↦ hL, fun _ ↦ hK⟩, hK, hL⟩

end WeilConjectures
