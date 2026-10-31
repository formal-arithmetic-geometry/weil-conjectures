/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Changing the presentation of a normalized tower purity record

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md,
Uniqueness and functoriality, and Levels; tower-geometric-gamma.proof.md, (1)--(3).
(blueprint: lem-pur-tower-purity-adjoint-transport).

This is transport of a given normalized record, not uniqueness of orientations.
Neither a ground-field automorphism nor an equality of finite orientations is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerGamma

/-- A normalized purity record can be expressed using any other counit-preserving
presentation of the same exceptional adjoint and its finite levels.
Source: tower-geometric-gluing.proof.md, Uniqueness and functoriality and Levels;
tower-geometric-gamma.proof.md, (1)--(3)
(blueprint: lem-pur-tower-purity-adjoint-transport).

Proof:
1. Put rho = adj'.rightAdjointUniq adj and keep the input coefficient-unit witness,
   root lines, coefficient coordinates, tensors, geometry and all invertibility
   witnesses of a'. Define the new orientation as a'.orientation followed by
   realization.mapIso (rho.app unit). Its hom is the displayed composite.
2. The adjunction identity F(rho_K) >> epsilon_K = epsilon'_K and projection
   naturality show that gamma' followed by realization(rho_K) is the new gamma.
   Indeed, before transposing, tensor naturality moves rho_unit through inverse
   projection; the counit identity removes it. Injectivity of adj.homEquiv gives
   the equality after transposing. Thus purity invertibility and naturality
   transfer. The tensor domains and projection invertibility transfer along rho;
   the uniform constructible domains are closed under isomorphism. Compact-support
   normalization is unchanged and exceptional normalization transfers along rho.
3. At level n, compare the two retained ordinary origins by the unique isomorphism
   whose image under nu* is the composite of their originIso maps. These origins
   are bounded below. Compare their ordinary right adjoints by rightAdjointUniq.
   The normalization of support_evaluation makes its comparison independent of lv.
   The counit equations in lv' and lv then identify the right comparisons with
   evaluation of rho: both have the same adjunction transpose. For each n, retain
   exactly the old dg and alpha. Compose the old ui with the origin comparison;
   naturality and the unit equations give its required coefficient-unit equation.
   Thus the proposition OrientationNormalized is literally unchanged.
4. Substitute these equalities in both WordComparison equations of a'.finite_levels.
   Naturality of the section-preserving levelComparison and rightIso cancels the
   intermediate comparisons. This gives precisely the two finite_levels equations
   in lv, with the new orientation and gamma from steps 1--2. The coefficient-mate
   reduction equations of both Levels records identify their quotient transitions;
   no faithfulness assertion for evaluation on derived morphisms is used.
5. Assemble these data and properties into the required Purity record. Its orientation
   was defined in step 1, so the final displayed equality is by functoriality. This
   argument includes the empty scheme, d=0, rho the identity, and arbitrary choices
   of the two finite-level presentations. -/
theorem purity_rightAdjoint_transport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G' G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj' : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G')
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv' : SpTowerGluing.Levels l E b o q (factorization j p) hF G' adj')
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj)
    (a' : Purity l E b o q j p d w hF G' adj' lv') :
    ∃ a : Purity l E b o q j p d w hF G adj lv,
      a.orientation.hom = a'.orientation.hom ≫
        (realization l E b q X).map
          ((adj'.rightAdjointUniq adj).hom.app ⟨originalUnit l E b q Y, a'.unit_mem⟩) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerGamma
