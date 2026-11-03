/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.QuasiFiniteCondensed.QuasiFiniteCondensedData

/-! Strict subclaim of the quasi-finite condensed direct-image theorem. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.QuasiFiniteCondensed
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Source: latest blueprint, lem-zl-quasi-finite.proof.md, clauses (3)--(5).

Proof:
A mixed sheaf $\mathcal F$ of weights $\le w$, placed in degree zero, lies in $D_{\le w}$. By (2)
its image lies there too; by (1) it is $g_!\mathcal F[0]$. The degree-zero condition is precisely
(3).

For (4)--(5), the canonical finite-fibre comparison for $p_*j_!\mathcal F$ is normalized by the
adjunction-counit projections. Summands off $Z$ vanish. Frobenius permutes the others; over a
closed $z$ above $y$ its cycle length is $e=[\kappa(z):\kappa(y)]\ge1$, its return is conjugate to
$F_z$, and $q_z=q_y^e$. Projecting a nonzero $\beta$-eigenvector to a nonzero summand gives a
source eigenvalue $\alpha=\beta^e$. Thus $|\iota\beta|^e=|\iota\alpha|\le q_y^{ew/2}$, and the
positive $e$th root proves (4); equality proves (5). Empty fibres have no eigenvalues. For finite
$g$, take $j=\mathrm{id}$ and $g_!=g_*$.
(blueprint: lem-zl-quasi-finite-purity-finite). -/
theorem _root_.WeilConjectures.QuasiFiniteCondensed.purityAndFinite
    (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    [IsSeparated Y₀.hom] (g₀ : X₀ ⟶ Y₀) [IsSeparated g₀.left]
    [LocallyQuasiFinite g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (c₀ : Compactification g₀.left) (F : AffineLineConventions.WeilSheaf D l X₀) :
    (∃ hF' : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber Y₀).left)
        (RelativeCurve.higherShriek D l g₀ c₀ F.obj 0).carrier,
      let F' : AffineLineConventions.WeilSheaf D l Y₀ :=
        ⟨RelativeCurve.higherShriek D l g₀ c₀ F.obj 0, hF'⟩
      (NativeL2.Mixed D l X₀ F.obj iota w → NativeL2.Mixed D l Y₀ F'.obj iota w) ∧
      (AffineLineConventions.HasPunctualWeightsAtMost F iota w →
        AffineLineConventions.HasPunctualWeightsAtMost F' iota w) ∧
      (NativeL2.Pure D l X₀ F.obj iota w → NativeL2.Pure D l Y₀ F'.obj iota w)) ∧
    (∀ (_hfinite : IsFinite g₀.left), NativeL2.Pure D l X₀ F.obj iota w →
      NativeL2.Pure D l Y₀ (NativeL2.middleWeilImage D l g₀ F.obj) iota w) := by
  sorry
end WeilConjectures.QuasiFiniteCondensed
