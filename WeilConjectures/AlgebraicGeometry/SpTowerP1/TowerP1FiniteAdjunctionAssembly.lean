/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1EtaleOriginComparisons

/-! # Assembly of the finite projective-line adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md
(blueprint: lem-sp-tower-p1-finite-adjunction-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- The finite adjunction and its precise evaluation equations, conditional only on
both actual tower triangles. This conclusion contains no tower adjunction.
Source: Levels, det-sp-tower-p1-adjunction steps 10--11
(blueprint: lem-sp-tower-p1-finite-adjunction-assembly).

Proof: apply towerP1SingleLevelTriangles at n and feed it the assumed identities.
Its singleton realizes every bounded-below ordinary etale input, so its conclusion
gives both finite etale triangles. Use the canonical finite projection, exchange,
composition and formula comparisons retained in h.levels to transport the diagonal
unit and splitting-trace counit through the fully faithful bounded-below comparison.
This gives natural transformations on the full finite etale-origin domains; their
functors preserve these domains by exact pullback, the rank-one twist and bounded-below
proper direct image. The pullback/tensor evaluation isomorphism is the composite of
the recorded pullEvaluation and tensorEvaluation, so comparison_eq is its defining
component formula. The transported triangles hold for any retained antecedent, and
fullness identifies every ambient morphism with its antecedent morphism. Construct
the finite adjunction from these two natural transformations and triangles. The whole
eta/epsilon word comparisons imply the two displayed equations for all tower inputs,
including the specified pushEvaluation arrows. Naturality makes these independent
of the chosen antecedent. The argument holds at every positive level, including
n=0 (exponent one); it does not use faithfulness of general tower evaluation. -/
theorem towerP1_finite_adjunction_assembly (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisons l E p d)
    (ht : (∀ M : C l E p.classes.base (ProjectiveLine S),
      (p.F l E).map (eta l E d M) ≫ epsilon l E d ((left l E d).obj M) =
        𝟙 ((p.F l E).obj M.obj)) ∧
      (∀ K : C l E p.classes.base S,
        eta l E d ((rightRestricted l E d).obj K) ≫ (p.G l E).map (epsilon l E d K) =
          𝟙 ((p.G l E).obj K.obj))) (n : ℕ) :
    ∃ (fm : FiniteMaps l E p n) (adj : finiteLeft l E fm ⊣ finiteRight l E fm),
      (∀ M : C l E p.classes.base (ProjectiveLine S),
        (SpTowerShriek.Ev l E (ProjectiveLine S) n).map (eta l E d M) ≫
          fm.comparison.hom.app ((p.F l E).obj M.obj) ≫
            (finiteG l E p n).map
              (((p.operations.geometry (ProjectiveLine S ↘ S)).pushEvaluation n).hom.app M.obj) =
          (finiteDomain l E (ProjectiveLine S) n).ι.map
            (adj.unit.app ((evaluation l E p.classes.base (ProjectiveLine S) n).obj M))) ∧
      (∀ K : C l E p.classes.base S,
        (finiteF l E S n).map (fm.comparison.inv.app K.obj) ≫
          ((p.operations.geometry (ProjectiveLine S ↘ S)).pushEvaluation n).inv.app
            ((p.G l E).obj K.obj) ≫ (SpTowerShriek.Ev l E S n).map (epsilon l E d K) =
          (finiteDomain l E S n).ι.map
            (adj.counit.app ((evaluation l E p.classes.base S n).obj K))) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
