/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.FiniteAdjointCompositorTransposes

/-! # Finite normalization of the given tower left compositor

This is the finite evaluation step of the actual tower compositor argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g]
  {cf : Compactification f} {cg : Compactification g} {ch : Compactification (f ≫ g)}

/-- The supplied proper/open tower compositor evaluates to any finite compositor
with the specified etale counit normalization. Only the left comparison is asserted.
Source: blueprint, smooth-purity composition comparisons proof (3), and the parent
node lem-sp-tower-adjoint-compositor-realization, steps 2--3
(blueprint: lem-sp-tower-compositor-finite-evaluation).

Proof: The coherence.composition_finite field of cal gives the evaluation formula
in fixed module coordinates, using cal.finite.evaluation. Each Evaluation has the
same comparison: its normalization field writes that comparison as the same word
of the realization counits and Fcomparison. Thus replace all three evaluations by
vf, vg, vh. At level n, cal.finite.finite_origin realizes the evaluated input by a
bounded constructible etale complex. The normalization of (A n).alpha identifies
its value on that witness with the etale proper/open compositor transported through
finiteAdjointSiteSupportIso. Finite compact-site coherence identifies this with
finiteCanonicalComposition in the fixed-coordinate formula. Naturality transports
that equality along the witness isomorphism. Finally the intrinsic/fixed derived
comparison is fully faithful, so cancel it to obtain the displayed equality. This
uses faithfulness of the site equivalence at one finite level, never faithfulness
of evaluation out of the derived tower category. -/
theorem towerCompositorFiniteEvaluation
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l) (k : Type u) [Field k] [CharP k p]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (hP : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z hP)
    (vf : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q cf n)
    (vg : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q cg n)
    (vh : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q ch n)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (n : ℕ) (M : SpTowerCalculus.C l E b q X) :
    (spDerivedCoefficientEvaluation l E Z (q.abelian Z) n).map
        ((cal.composition.composition f g (f ≫ g) rfl cf cg ch).hom.app M) ≫
      (vh n).comparison.hom.app M.obj =
    (vg n).comparison.hom.app ((SpTowerCalculus.F l E b o q cf).obj M.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E n) cg.i cg.g).map
        ((vf n).comparison.hom.app M.obj) ≫
      ((A n).alpha.hom.app ((SpTowerGluing.level l E b q X n).obj M)).hom := by sorry

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
