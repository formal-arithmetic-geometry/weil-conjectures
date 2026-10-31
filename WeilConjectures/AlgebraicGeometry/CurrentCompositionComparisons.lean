/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionComparisons
public import WeilConjectures.AlgebraicGeometry.CurrentIntegralData
import WeilConjectures.AlgebraicGeometry.CurrentIntegralEdge
import WeilConjectures.AlgebraicGeometry.CurrentReductionFaithful
import WeilConjectures.AlgebraicGeometry.CurrentIntegralCompositionLaws

/-! # Composition comparisons with the current integral coefficient model

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
sk-prop-sp-composition-comparisons.md, clauses (1)--(3)
(blueprint: det-sp-composition-comparisons).

The finite and strict-tower clauses are the publicly imported
`compositionComparisons_finite` and `compositionComparisons_towers`.
The integral clause below uses bounded constructible internal modules over the
pulled-back completed ring, over the same arbitrary positive-characteristic field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompositionComparisons
open IntegralDirectImageTower NormalizedIntegralAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Total derived inverse limit realizes the given tower compositors on the completed
Z_l coefficient Dbc categories, over the full standing field setting. Tower functors,
adjunctions and their counit-compatible compositors are the data fixed in clause (3),
not extra properties of an input complex. An index n in the imported tower model
means exponent n+1, so every positive level, including equal reduction indices, occurs.
Source: latest blueprint comparisons (3), integral realization
(blueprint: det-sp-composition-comparisons).

Proof, following the four DAG steps:
1. The finite comparisons are compositionComparisons_finite: finite-type schemes
are Noetherian, finite constructible etale origin and Tor reflection allow the
proper/open site-coherence and coefficient-composition identities to apply. The
counit transpose gives the unique right compositor and its coefficient equation.
2. compositionComparisons_towers constructs the actual strict-tower compositors;
its Laws give finite evaluations, counits, reduction squares, and preservation of
normalization with uniform bounds, without faithfulness of evaluation.
3. sk-lem-sp-tower identifies normalized towers with bounded constructible integral
objects. det-sp-integral-direct-image-tower identifies the separately derived
support with its normalized total-limit model. Restrict the tower adjunction along
reduction. This gives the three IntegralEdge realizations, including the actual
proper/open left comparison and the reduction/limit counit on the right.
4. Insert the middle reduction/limit counit between the two support functors and
apply total limit to alphaTower. Apply total limit to thetaTower and insert the
inverse middle counit between the two right functors. Naturality gives the two
reduction equations in SpCompositionIntegralLaws. Reduce the counit identity and
use the tower identity; full faithfulness of reduction proves the integral identity.
Uniqueness of right adjoints gives the unique normalized theta. The middle counit
is applied only to normalized towers. No arbitrary-limit interchange is used.
-/
theorem integral
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (s : Presentation l (ULift.{u} (Padic l)))
    (hFf : ∀ M : Towers l (ULift.{u} (Padic l)) s X,
      spConstructibleTorTowers l (ULift.{u} (Padic l)) Y (s.towers Y)
        ((towerShriek l (ULift.{u} (Padic l)) s cf).obj M.obj))
    (hFg : ∀ M : Towers l (ULift.{u} (Padic l)) s Y,
      spConstructibleTorTowers l (ULift.{u} (Padic l)) Z (s.towers Z)
        ((towerShriek l (ULift.{u} (Padic l)) s cg).obj M.obj))
    (hFh : ∀ M : Towers l (ULift.{u} (Padic l)) s X,
      spConstructibleTorTowers l (ULift.{u} (Padic l)) Z (s.towers Z)
        ((towerShriek l (ULift.{u} (Padic l)) s ch).obj M.obj))
    (Gf : Towers l (ULift.{u} (Padic l)) s Y ⥤ Towers l (ULift.{u} (Padic l)) s X)
    (Gg : Towers l (ULift.{u} (Padic l)) s Z ⥤ Towers l (ULift.{u} (Padic l)) s Y)
    (Gh : Towers l (ULift.{u} (Padic l)) s Z ⥤ Towers l (ULift.{u} (Padic l)) s X)
    (af : towerSupport l (ULift.{u} (Padic l)) s cf hFf ⊣ Gf)
    (ag : towerSupport l (ULift.{u} (Padic l)) s cg hFg ⊣ Gg)
    (ah : towerSupport l (ULift.{u} (Padic l)) s ch hFh ⊣ Gh)
    (alphaTower : towerSupport l (ULift.{u} (Padic l)) s cf hFf ⋙
        towerSupport l (ULift.{u} (Padic l)) s cg hFg ≅
      towerSupport l (ULift.{u} (Padic l)) s ch hFh)
    (thetaTower : Gh ≅ Gg ⋙ Gf)
    (_ht : ∀ K,
      (towerSupport l (ULift.{u} (Padic l)) s cf hFf ⋙
          towerSupport l (ULift.{u} (Padic l)) s cg hFg).map (thetaTower.hom.app K) ≫
        (af.comp ag).counit.app K = alphaTower.hom.app (Gh.obj K) ≫ ah.counit.app K) :
    IntegralResult l (ULift.{u} (Padic l)) s cf cg ch hFf hFg hFh Gf Gg Gh af ag ah
      alphaTower thetaTower := by
  obtain ⟨If⟩ := integralEdge l (ULift.{u} (Padic l)) k p _hpl f d s cf hFf Gf af
  obtain ⟨Ig⟩ := integralEdge l (ULift.{u} (Padic l)) k p _hpl g e s cg hFg Gg ag
  obtain ⟨Ih⟩ := integralEdge l (ULift.{u} (Padic l)) k p _hpl (f ≫ g) (d + e)
    s ch hFh Gh ah
  obtain ⟨full⟩ := reductionFullyFaithful l (ULift.{u} (Padic l)) k p _hpl s Z Ih.reductionY
  obtain ⟨alpha, theta, laws⟩ := integralLaws l s cf cg ch hFf hFg hFh
    Gf Gg Gh af ag ah If Ig Ih full alphaTower thetaTower _ht
  exact ⟨If, Ig, Ih, alpha, theta, laws⟩

end AlgebraicGeometry.ProEtale.CompositionComparisons
