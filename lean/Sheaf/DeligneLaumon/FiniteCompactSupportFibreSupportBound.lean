/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Perverse.Basic
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSupport
import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.FiniteRingCompactSupportFiniteness
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.GeometricStalkCohomology
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.DeligneLaumon.ConstructibleSubsetClosureDimension
import Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Constructible
import Mathlib.Topology.NoetherianSpace

/-! # Fibre support bounds at finite coefficients

Source: BBD, Faisceaux pervers, section 4.2.4, the finite-coefficient sheaf support
estimate used in its compact-support amplitude bound
(blueprint: lem-per-finite-compact-support-fibre-support-bound).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The closed support of `R^q f_! F` has dimension at most `a + d - q`.
The bound is expressed on nonempty support, where the integer bound must be nonnegative;
empty support has dimension bottom. The second clause states both vanishing ranges.
Natural numbers `a` and `d` encode precisely the nonnegative integer parameters.
Source: BBD, Faisceaux pervers, 4.2.4, finite-coefficient sheaf support estimate
(blueprint: lem-per-finite-compact-support-fibre-support-bound).

Proof plan (the DAG proof, with its cited inputs):

1. Choose a compactification $X\xrightarrow{j}\overline X\xrightarrow{r}Y$ by
[thm-nagata-compactification]. Here $Y$ is qcqs, $f$ is separated of finite type, and $\overline
X$ is finite type over $k$ since $r$ is proper. Use $Rf_!=Rr_*Dj_!$ as defined in
[def-amb-etale-compact-support]. Apply [lem-fd-finite-ring-compact-support-finiteness] to $F[0]$
and this compactification. It gives constructibility of every $G_q=R^qf_!F$ and $G_q=0$ for $q<0$
(its amplitude clause with $[a,b]=[0,0]$). The sheaf $F[0]$ is bounded constructible by
[def-weil-pbc-constructible-complexes].

2. For each $q$, [lem-weil-pbc-constructible-module-support-constructible] makes the nonzero-stalk
set $S_q$ constructible and makes its definition independent of the geometric point over a fixed
point. Its closure is the closed support $C_q$: an open set misses $S_q$ exactly when the
restricted sheaf is zero by [lemma-weil-pbc-geometric-stalk-conservative]. The schemes here are
Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since a field is Noetherian. In
particular [lem-sc-noetherian-closed-subset-finite-components] gives finitely many irreducible
components of $C_q$.

3. The generic point $t$ of every irreducible component $T$ of $C_q$ belongs to $S_q$. Indeed,
remove the other finitely many components and work on the resulting nonempty open subset of $T$.
It meets $S_q$ densely. Express $S_q$ as a finite union of locally closed sets by
[def-weil-constructible-subset]. Some one of their closures is all of $T$: a finite closed cover
of an irreducible space has a member equal to the space. This locally closed set therefore
contains a nonempty open of $T$, and hence its generic point. Thus $t\in S_q$.

4. Fix $y\in Y$ and an algebraic closure $\Omega$ of $\kappa(y)$, giving $\bar
y:P=\operatorname{Spec}\Omega\to Y$; write $r':\overline X_{\bar y}\to P$, $j_{\bar y}$ and
$F_{\bar y}$ for the base changes and $H=j_{\bar y!}F_{\bar y}$. Proper base change
[lem-kun-proper-base-change-torsion-ring] for the proper map $r$, applied to $Dj_!F$, and
[lem-cbc-extension-zero-base-change] for $j$ (degreewise, on the single sheaf $j_!F$) give $\bar
y^{-1}Rf_!F\cong Rr'_*H$ in $D(P_{\mathrm{et}},\Lambda)$. Taking cohomology and stalks commutes by
[lem-kun-stalks-of-cohomology]. By [lem-weil-pbc-geometric-point-pullback-stalk] a stalk at $\bar
y$ is $\Gamma(P,\bar y^{-1}(-))$ and $\Gamma(P,-)$ is exact, so $(G_q)_{\bar y}\cong\mathcal
H^q(\Gamma(P,Rr'_*H))$. Represent $Rr'_*H$ by $r'_*I$ for a K-injective resolution $H\to I$, as in
[def-amb-etale-compact-support]. Termwise $\Gamma(P,r'_*I)=\Gamma(\overline X_{\bar y},I)$ by the
direct-image formula recorded in [def-weil-pbc-cohomology-pullback], whose cohomology is
$H^q(\overline X_{\bar y},H)$ by [def-weil-pbc-etale-cohomology]; module and abelian cohomology
agree by [lem-weil-pbc-etale-module-cohomology-forget]. Therefore $$(G_q)_{\bar y}\cong
H^q(\overline X_{\bar y},j_{\bar y!}F_{\bar y}).$$ All coefficient sheaves are torsion because the
additive exponent of $\Lambda$ kills them; proper base change allows this arbitrary geometric base
change.

5. Give $Z$ its reduced induced closed subscheme structure by
[lem-weil-pbc-reduced-induced-closed-subscheme]. Put $Z_y=Z\times_Y\operatorname{Spec}\kappa(y)$.
If it is nonempty, write $e(y)=\dim Z_y$. The closed immersion into $X_y$ gives $e(y)\le d$:
chains of irreducible closed subsets stay chains in $X_y$. For the field extension
$\kappa(y)\subset\Omega$, [lem-sc-fibre-dimension-after-base-change] preserves local fibre
dimensions. The projection $Z_{\bar y}\to Z_y$ is surjective: above a point $z$ its fibre is the
spectrum of the nonzero ring $\kappa(z)\otimes_{\kappa(y)}\Omega$, nonzero by a vector-space
basis. Consequently $\dim Z_{\bar y}=\dim Z_y=e(y)$. To see the global dimension conclusion from
the local one, use the finite irreducible components of these finite-type schemes,
[lem-sc-dimension-locally-algebraic] on each component, and the definition of local dimension
[def-kun-dimension]: the maximum of component dimensions is both the global dimension and the
maximum of the local dimensions. Empty fibres stay empty.

6. Let $W$ be the closure of $Z_{\bar y}$ in $\overline X_{\bar y}$, with reduced induced
structure [lem-weil-pbc-reduced-induced-closed-subscheme]. Since $Z_{\bar y}$ is closed in the
open $X_{\bar y}$, it is locally closed, hence constructible. Apply
[lem-per-constructible-subset-closure-dimension] over $\Omega$ to get $\dim W=e(y)$ when nonempty.
The sheaf $H=j_{\bar y!}F_{\bar y}$ vanishes outside $W$: it is zero outside $X_{\bar y}$ by
extension by zero and outside $Z_{\bar y}$ inside that open by the closed support of $F$ and
conservativity of geometric stalks [lemma-weil-pbc-geometric-stalk-conservative]. By
[lem-kun-04ca], its underlying abelian sheaf is $i_*i^{-1}H$, where $i:W\hookrightarrow\overline
X_{\bar y}$ is the closed immersion. This also handles $W=\varnothing$, giving $H=0$.

7. For $W\ne\varnothing$, the closed immersion $i$ is finite: on affine charts its map is $A\to
A/I$, generated by $1$ as an $A$-module. Thus [lem-weil-pbc-finite-pushforward-cohomology] gives
$$H^q(\overline X_{\bar y},H)\cong H^q(W,i^{-1}H)\quad(q\ge0)$$ for underlying abelian sheaves.
Module cohomology has the same underlying groups by [lem-weil-pbc-etale-module-cohomology-forget].
The field $\Omega$ is separably closed, so [lem-sf-separably-closed-torsion-cd] gives
$\operatorname{cd}_{\rm tor}(\Omega)\le0$; apply [thm-sc-finite-type-torsion-cd] to the
finite-type $\Omega$-scheme $W$ of dimension $e(y)$ and the torsion sheaf $i^{-1}H$. Combining
with Steps 4--6, the stalk of $G_q$ is zero if $Z_y$ is empty or $q>2e(y)$.

8. Take $q\ge0$ and an irreducible component $T$ of the nonempty closed support $C_q$, with
generic point $t$. By Step 3 the stalk there is nonzero. Step 7 implies $Z_t\ne\varnothing$ and
$q\le2e(t)\le2d$. Choose an irreducible component $B$ of $Z_t$ of dimension $e(t)$ and let $Z'$ be
its closure in $Z$, with reduced induced structure
[lem-weil-pbc-reduced-induced-closed-subscheme]. Then $Z'$ is an irreducible finite-type
$k$-scheme, $\overline{f(Z')}=T$, and its fibre over $t$ has underlying space $B$. For the last
assertion, $Z'\subseteq f^{-1}(T)$ since that is closed and contains $B$. The fibre over the
generic point $t$ embeds topologically into $f^{-1}(t)$ by affine localization (the description of
[def-pc-scheme-fibre]); intersecting the closure of $B$ with that fibre gives its closure in the
fibre, which is $B$ since $B$ is closed there. The generic point $\zeta$ of $Z'$ is the generic
point of $B$ and lies over $t$.

9. Apply [lem-zl-irreducible-fibre-dimension-lower-bound] to $Z'\to Y$: there is $r\ge0$ with
$\dim Z'=\dim T+r$, and the locus where the local fibre dimension equals $r$ is dense open in
$Z'$. This open contains its generic point $\zeta$. The fibre $Z'_t$ is irreducible finite type
over $\kappa(t)$ with underlying space $B$; [lem-sc-dimension-locally-algebraic] therefore says
its local dimension at $\zeta$ equals its dimension $e(t)$. Hence $r=e(t)$ and $$\dim T=\dim
Z'-e(t)\le a-e(t)\le a-\lceil q/2\rceil.$$ Here $\dim Z'\le\dim Z\le a$ follows by including
chains of closed irreducible subsets, and $e(t)\ge\lceil q/2\rceil$ follows from $q\le2e(t)$.

10. Since $q\le2d$, $\lfloor q/2\rfloor\le d$, so $$\dim T\le a-\lceil q/2\rceil=a-q+\lfloor
q/2\rfloor\le a+d-q.$$ The finitely many irreducible components $T$ cover $C_q$, so this bounds
$\dim C_q$: the largest member of a chain of irreducible closed subsets in a finite closed cover
lies in one cover member, by irreducibility, and then the whole chain does. If $a+d-q<0$, a
nonempty component would have dimension at least zero; hence $C_q=\varnothing$, and
geometric-stalk conservativity gives $G_q=0$ [lemma-weil-pbc-geometric-stalk-conservative]. For
empty $C_q$ the asserted dimension bound uses $\dim\varnothing=-\infty$; negative $q$ were covered
in Step 1.
-/
theorem finiteCompactSupportFibreSupportBound
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hf : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (a : ℕ) (hSupp : topologicalKrullDim (sheafSupport F) ≤ (a : WithBot ℕ∞)) :
    (∀ q : ℤ,
      (sheafSupport ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (@HasCompactification.compactification X Y f
            (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))).Nonempty →
      0 ≤ (a : ℤ) + (d : ℤ) - q ∧
      topologicalKrullDim (sheafSupport ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (@HasCompactification.compactification X Y f
            (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≤
        (((a : ℤ) + (d : ℤ) - q).toNat : WithBot ℕ∞)) ∧
    (∀ q : ℤ, (q < 0 ∨ (a : ℤ) + (d : ℤ) < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (@HasCompactification.compactification X Y f
            (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) := by
  sorry

end AlgebraicGeometry.Etale
