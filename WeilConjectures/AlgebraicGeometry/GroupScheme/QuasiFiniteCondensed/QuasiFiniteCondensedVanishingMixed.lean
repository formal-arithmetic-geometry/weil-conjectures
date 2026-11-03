/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.QuasiFiniteCondensed.QuasiFiniteCondensedData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProetaleSiteProperties
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import WeilConjectures.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian

/-! Strict subclaim (clauses (1)--(2)) of the quasi-finite condensed direct-image theorem,
with its proved finite-compactification case. -/

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

/-- Source: latest blueprint, lem-zl-quasi-finite.proof.md, clauses (1)--(2).

Proof:
The standing separated finite-type setting applies. $Y_0$ is Noetherian, hence qcqs. Zariski's
main theorem gives $g=p_0j_0$ with $j_0:Z_0\hookrightarrow T_0$ quasi-compact open and $p_0$
finite. Finite maps are proper; composition of separated and finite-type maps makes $T_0/k_0$
separated finite type, as is $Z_0$. Base change gives $g=pj$. The canonical composition and
properness comparisons give $Rg_!\simeq Rp_!Rj_!\simeq Rp_*D(j_!)$, equivariantly for Weil
structures. Use the specified proper/open interchange map, normalized by restriction to the
identity on the open.

Since $Y$ is Noetherian, $p$ is finitely presented. Thus $p_*$ is exact and $Rp_*$ is computed
termwise. Exact $j_!$ and six-operation stability make $T=p_*j_!$ exact on constructible hearts.
Consequently $Rg_!\mathcal F=T(\mathcal F)[0]$, proving (1), and $\mathcal H^r(Rg_!K)\simeq
T\mathcal H^r(K)$.

For $K\in D_{\le w}(Z_0)$, each $\mathcal H^rK$ has a finite mixed filtration with pure quotients
of weights $\le w+r$. Exact $j_!$ sends this to a filtration with quotients $j_!$ of those
quotients. Their fibres and Frobenius are unchanged on $Z_0$, and zero off it, so their purity
weights are unchanged. Hence $Rj_!K\in D_{\le w}(T_0)$. The finite pushforward bound gives
$Rp_*Rj_!K\in D_{\le w}(Y_0)$, proving (2).
(blueprint: lem-zl-quasi-finite-vanishing-mixed). -/
theorem _root_.WeilConjectures.QuasiFiniteCondensed.vanishingAndMixed
    (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    [IsSeparated Y₀.hom] (g₀ : X₀ ⟶ Y₀) [IsSeparated g₀.left]
    [LocallyQuasiFinite g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (c₀ : Compactification g₀.left) (F : AffineLineConventions.WeilSheaf D l X₀) :
    (∀ i : ℕ, 0 < i → IsZero (RelativeCurve.higherShriek D l g₀ c₀ F.obj i)) ∧
    (∀ K : AmbientPair D l X₀, boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left) K.carrier →
      (∀ b : ℤ, NativeL2.Mixed D l X₀ (cohomology D l X₀ K b) iota (w + b)) →
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).left) (image D l g₀ c₀ K).carrier ∧
      ∀ b : ℤ, NativeL2.Mixed D l Y₀
        (cohomology D l Y₀ (image D l g₀ c₀ K) b) iota (w + b)) := by
  sorry

end WeilConjectures.QuasiFiniteCondensed
