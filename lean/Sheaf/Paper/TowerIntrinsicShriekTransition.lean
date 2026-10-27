/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.CoefficientTowerShriekInterfaces
import Sheaf.Paper.ShriekNormalizedTransitionComparison

/-! # Actual compact-support transitions in intrinsic tower coordinates

Source: blueprint latest, smooth tower gluing proof, Levels paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.SpTowerCalculus

namespace AlgebraicGeometry.ProEtale

/-- Transport the actual compact-support transition equation to the original tower
category and the specified intrinsic finite evaluations.

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gluing.proof.md, Levels, final sentence
(blueprint: lem-sp-intrinsic-shriek-transition).

Proof: exact level evaluations identify the cohomology of the tower with its
levelwise cohomology. The uniform lower bound on G therefore makes its
section-normalized realization bounded below. The finite ctf levels give the
GoodLevel hypotheses after the quotient congruence b.ideals. Apply
lem-sp-shriek-normalized-transition-comparison to that realized object. The
sequence quotientMap equals the factor quotient by induction on the interval
length, or by surjectivity of O_E onto its quotient. The ordinary section equations
in q identify its evaluations and strict transitions with those of the realization.
Localizing those equations and using uniqueness of a left-adjoint comparison
preserving its specified unit identifies its rho with reduction. Expand the
normalization equation of each v: the realization counit cancels by naturality,
and its inverse cancels by the equivalence triangle identities. The resulting
actual = word equation is precisely the displayed formula. This calculation
uses equality on the derived strict-system model, never faithfulness of derived
level evaluations. Equal indices use the same argument with the tensor unitor;
no normalization or coefficient flatness is assumed. -/
theorem tower_intrinsic_shriek_transition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b)
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))]
    [c.Z.Over (Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (v : ∀ n : ℕ, Evaluation l E b o q c n) (G : C l E b q X)
    {m n : ℕ} (h : m ≤ n) :
    (scalarExtensionFunctor (quotient l E h) Y).map
        ((v n).comparison.hom.app G.obj) ≫
      (reductionDirectImageComparison (quotient l E h) c.i c.g).app
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj G.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (reduction l E X (q.abelian X) h (q.scalar X h) G.obj) =
    reduction l E Y (q.abelian Y) h (q.scalar Y h) ((F l E b o q c).obj G.obj) ≫
      (v m).comparison.hom.app G.obj := by sorry

end AlgebraicGeometry.ProEtale
