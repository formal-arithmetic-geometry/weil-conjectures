/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearGeometryOps
public import Sheaf.Paper.SemilinearDerivedCalculus
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Existence of operations on ordinary semilinear systems

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-operations-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The geometric, coefficient-extension, and open-localization operations,
for a previously constructed ordinary system calculus.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-operations-existence).
Proof: apply the actual inverse-image, direct-image, tensor, and extension-by-zero
constructions on the ringed sequence site. Their normalized evaluation formulas
are obtained on K-flat and K-injective representatives and then localized. -/
structure SemilinearOperationsData (systems : Data.{c, v, r} J B τ) where
  geometric : ∀ {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv],
    {G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet //
      G.PullTransitionFormula J B τ systems J' uInv uPush adjSet}
  coefficientExtension : ∀ (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n),
    ScalarSystems.{c, v, r} J B τ F σ α hα
  localization : ∀ U : C, OpenSystems.{c, v, r} J B τ U

/-- Geometric and coefficient operations on a fixed semilinear system calculus.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-operations-existence).
Proof:
1. Apply $u^{-1}$ and $u_*$ termwise on the underlying sequence topoi. Their adjunction follows by
applying the original adjunction at every index: the naturality equations for a family of maps
correspond under transposition. The inverse image preserves finite limits and colimits, so is
exact on module systems, with coefficient ring $C_\bullet=u^{-1}B_\bullet$. This is a morphism of
the two ringed sequence topoi. Apply [lem-weil-pbc-ringed-projection-mate-exact] and
[prop-pur-kinjective-resolutions-exist] there. They give $V\dashv G=Ru_{*,\bullet}$, with $G$
computed by a K-injective system resolution and $V$ termwise exact. The unit and counit here are
maps in the ordinary derived categories of systems.

2. Write $L_n^B,L_n^C$ for the finite left extensions on the two sites. On a flat-term K-flat
representative $P$, inverse image and coefficient tensor give $VE_n^BP\cong E_n^Cu^{-1}P$, with
the same zero components above $n$. The isomorphism is $u^{-1}(P\otimes_{B_n}B_q)\cong
u^{-1}P\otimes_{C_n}C_q$. K-flat pullback and derived tensor/pullback identify it as $VL_n^B\cong
L_n^Cu^{-1}$ on the ordinary derived categories. For $P\in D(B_n)$ and $N\in D(\mathscr S(C))$,
the natural bijections
$$\operatorname{Hom}(P,e_nGN)\cong\operatorname{Hom}(L_n^BP,GN)\cong\operatorname{Hom}(VL_n^BP,N)\
cong\operatorname{Hom}(L_n^Cu^{-1}P,N)\cong\operatorname{Hom}(u^{-1}P,N_n)\cong\operatorname{Hom}(
P,Ru_{*,n}N_n)$$
therefore give $e_nG\cong Ru_{*,n}e_n$ by Yoneda. This proves the formula without any preservation
of K-injectives by evaluation.

3. Use the canonical adjunctions in the preceding Hom bijections. The derived adjunction formula
on a resolving representative is the ordinary tensor-adjoint formula: its unit sends $x$ to
$x\otimes1$, and its transpose sends $x\otimes a$ to $a h(x)$. This follows from the canonical
pre-derived adjunction formula of [lem-pc-pre-derived-adjoint-functors-general], with the identity
resolving leg, and then naturality in a K-flat resolution. Consequently the Hom bijections
defining $e_nG$ carry the evaluated unit and counit to the level unit and counit: applying the
bijection to an identity gives its unit, and applying its inverse to an identity gives its counit.
The comparison $VL_n^B\cong L_n^Cu^{-1}$ commutes with $\sigma_{mn}$, since its two composites are
the same inverse-image tensor reassociation on $q\leq n$ and zero above. Transpose this square.
The reduction transition of $GN$ becomes $G_n(t^N_{m,n})b_{m,n}$, where $b$ is the transpose of
$$u^{-1}T_{m,n}G_m\xrightarrow{q^{-1}}S_{m,n}u^{-1}G_m\xrightarrow{S_{m,n}\varepsilon_m}S_{m,n}.$$
Ordinary mate pasting gives the composition law. This proves compatibility of evaluations with the
adjunction maps and coefficient transitions, not merely the evaluated objects.

4. For an open localization apply $j_!,j^*$ at each level. Their exactness and adjunction follow
from [lem-pur-site-restriction-module-adjunction-exact], by transposing the transition equations.
Both exact functors are their own total derived functors
[lem-weil-pbc-exact-functor-derived-functor], so they descend termwise and retain their adjunction
by [lem-pc-derived-adjoint-functors]. To compute coefficient change, use the slice projection
identity [lem-weil-pbc-ringed-slice-extension-tensor]. It also proves $j_!$ preserves flatness:
tensoring an exact sequence with $j_!F$ is exact $j_!$ applied to its exact restriction tensored
with flat $F$. For K-flat $P$ and acyclic $A$, $(j_!P)\otimes A\cong j_!(P\otimes j^*A)$ is
acyclic, proving K-flatness. Thus the same identity on K-flat resolutions gives the derived
coefficient comparison. On an extension summand it sends $x\otimes b$ to $x\otimes j^*b$; iterated
coefficient changes agree as balanced tensors. All these are transformations on systems before
localization and so have the stated ordinary derived system models.

5. A compatible ring-system map $B_\bullet\to D_\bullet$ is a map of ring sheaves on the sequence
site. Apply derived ringed-topos pullback for the identity topos
[lem-weil-pbc-ringed-topoi-derived-pullback], resolving by flat-term K-flat complexes on that
site. Their evaluations are flat-term K-flat by step 3, so evaluation of extension is exactly
$M_n\otimes^L_{B_n}D_n$. Tensor and coefficient composition are obtained from total tensor
rebracketing. The monoidal and composition comparisons of
[lem-sfb-ringed-derived-monoidal-comparisons] apply both to the sequence topos and to each
evaluation morphism. They prove compatibility with tensor associativity, units, symmetry and
iterated pullback. Thus these comparisons are actual natural transformations on ordinary derived
systems, with the indicated evaluation formulas, for arbitrary coefficient maps.

6. Form each specified exchange by its unit/composition/counit word [def-weil-pbc-adjunction-mate]
for the derived functors on the ringed sequence topoi; for an open map use $j_!\dashv j^*$
instead. Pullback composition and direct-image composition use the normalized ordinary comparisons
[lem-sfb-ringed-derived-monoidal-comparisons,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. Every letter is already a system
functor or transformation. Evaluation of those letters is the level letter, including the unit and
counit by step 9 and the exact open adjunction by step 10. Hence evaluation of the word is the
corresponding level word. The same applies to any specified composite with open extension or
proper direct image. Ordinary mate pasting proves compatibility with composition on the system
category itself. No properness was needed to construct a direct-image composition, and no
invertibility of a mate is inferred.

For geometric tensor pullback use the inverse-image pure-tensor comparison on each total-complex
summand, with the inverse ordinary comparison as its recorded inverse. The differential signs make
these chain maps. Resolving on the system site by K-flat complexes with flat terms gives the
normalized derived comparison; hence its specification is checked before evaluation, without
assuming derived evaluation is faithful. -/
theorem semilinearOperationsData (systems : Data.{c, v, r} J B τ) :
    Nonempty (SemilinearOperationsData.{c, v, r} J B τ systems) := by
  sorry

end WeilConjectures.SemilinearSections
