/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Ring.ULift
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Open direct-image finiteness over a regular base of dimension at most one

Source: ILO, Travaux de Gabber, Expose XIII, Theorem 2.3.1(i), printed p.197;
Zheng, Six operations and Lefschetz-Verdier formula for Deligne-Mumford stacks,
Proposition 3.16(1), printed p.19
(blueprint: lem-per-low-base-open-sheaf-finiteness).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct images under an open immersion into a separated finite-type scheme
 over a Noetherian regular base of dimension at most one are constructible, with a
 sheaf-dependent upper vanishing bound. Coefficients are the universe lift of F_ell.
 Source: ILO XIII, Theorem 2.3.1(i), printed p.197; Zheng, Proposition 3.16(1), printed p.19.
 (blueprint: lem-per-low-base-open-sheaf-finiteness).

Proof:
1. First $T$ is Noetherian since it is of finite type over $S$. Every open of $T$ is
quasi-compact, so $j$ is quasi-compact and of finite type; in particular its higher direct images
admit the strict-local stalk formula. Regularity makes $S$ normal, and its finitely many
irreducible components are disjoint open integral schemes. Work on each component and combine the
resulting finite stratifications and vanishing bounds at the end. Open restriction commutes with
$Rj_*$. The empty base has empty $T$, hence the assertion is immediate.
Uses: [lem-weil-pbc-finite-type-over-noetherian],
[lem-weil-pbc-noetherian-open-subscheme-noetherian], [lem-weil-pbc-qc-open-immersion-finite-type],
[rem-pc-regular-normal], [lem-weil-pbc-derived-open-restriction].

2. Now $S$ is integral. Apply generic open-image finiteness to obtain a nonempty open $S^\circ$
and a bound $b_0$. By open restriction, $G_q=R^qj_*F$ is constructible on
$T^\circ=T\times_SS^\circ$ and is zero there for $q>b_0$. This generic input has no
finite-type-over-a-field assumption. It applies to the original constant coefficient field $A$.
Uses: [lem-per-noetherian-base-generic-open-finiteness], [lem-weil-pbc-derived-open-restriction].

3. The proper closed subset $E=S\setminus S^\circ$ contains no generic point. Each of its
irreducible components is therefore a single closed point: a strict specialization inside such a
component would, with the generic point of $S$, make a chain of length two, contrary to $\dim
S\leq1$. There are finitely many such components, say $s_1,\ldots,s_r$. If $S$ has dimension zero,
$E$ is empty. Otherwise each $\mathcal O_{S,s_a}$ is regular local of dimension one, hence a DVR.
Put $S_a=\operatorname{Spec}\mathcal O_{S,s_a}$ and form $j_a:V_a\hookrightarrow T_a$ by base
change. The closed fibre of $T_a$ is exactly $T_{s_a}$, with the same residue field.
Uses: [lem-sc-noetherian-closed-subset-finite-components], [def-kun-topological-krull-dimension],
[def-weil-regular-scheme], [lem-sc-regular-dim1-dvr].

4. For each $a$, let $p_a:T_a\to T$ and let $F_a$ be the inverse image of $F$. It is
constructible: pull its finite stratification and its finite constant local trivializations back
to $V_a$. The base map $S_a\to S$ is locally ind-etale: on an affine neighbourhood of $s_a$,
localization is the filtered colimit of the localizations at elements outside its prime, each an
open immersion. The same holds for $p_a$. For a geometric point $t$ of $T_a$, ind-etale
strict-local invariance identifies $(T_a)_{(t)}$ with $T_{(p_at)}$. The two stalk formulas for
$j_a$ and $j$ are thus the cohomology of the identical scheme $V\times_TT_{(p_at)}$ with the
identical pulled-back sheaf. Their canonical restriction maps are isomorphisms. The forgetful
comparison supplies these formulas for $A$-module higher direct images; the maps commute with the
action of every scalar in $A$. Stalk conservativity therefore gives $p_a^{-1}G_q\cong
R^qj_{a*}F_a$ for every $q$. Exact inverse image allows us to commute restriction with cohomology.
Uses: [def-weil-pbc-etale-constructible-sheaf], [lemma-constructible-pullback-stratification],
[def-weil-pbc-ind-etale-algebra], [lem-trf-ind-etale-strict-local-invariance],
[prop-weil-pbc-strict-henselization-stalk-formula],
[lem-sbc-higher-direct-image-forget-comparison], [lemma-weil-pbc-geometric-stalk-conservative],
[prop-weil-pbc-inverse-image-modules-exact], [lemma-openclosed-stalk-upperstar],
[lem-pur-scheme-constructible-preimage].

5. Apply closed-fibre DVR finiteness to $j_a,F_a$; all its hypotheses hold since $\ell$ remains a
unit and separated finite-type morphisms and open immersions retain their properties after base
change. Using the preceding isomorphism and then pulling back to the closed fibre gives that
$G_q|_{T_{s_a}}$ is constructible for every $q$, and zero there for $q>b_a$, for some $b_a\geq0$.
Only this restriction is taken from the local input. No comparison with the direct image of
$j_{s_a}$ is claimed.
Uses: [lem-per-dvr-open-image-closed-fibre-finiteness], [lem-weil-pbc-open-immersion-base-change],
[lem-pod-separated-finite-type-base-change].

6. For fixed $q$, choose finite constructible locally closed stratifications trivializing $G_q$ on
$T^\circ$ and each $T_{s_a}$. Regard these strata as subschemes of $T$ by composing their
immersions with the open immersion $T^\circ\to T$ or the closed immersion $T_{s_a}\to T$. A
locally closed subset of a locally closed subset is locally closed; in the Noetherian space $T$
each such subset is constructible. The finitely many stratifications are disjoint and cover $T$,
and the same finite constant module trivializations still apply. This is precisely the defining
stratification of a constructible $A_T$-module sheaf. Take $c_F=\max(\{0,b_0\}\cup\{b_a:1\leq
a\leq r\})$. If $q>c_F$, every geometric stalk of $G_q$ lies either over $S^\circ$ or over one of
the $s_a$, where the restriction is zero. Stalk conservativity gives $G_q=0$. Taking the maximum
over the finitely many components from step 1 finishes the proof.
Uses: [def-weil-pbc-etale-constructible-sheaf], [lemma-weil-pbc-geometric-stalk-conservative],
[lemma-openclosed-stalk-upperstar]. -/
theorem higherDirectImage_constructible_bounded_of_regular_low_base
    {S T V : Scheme.{u}} [IsNoetherian S] (_hS : IsRegularScheme S)
    (_hdim : topologicalKrullDim S ≤ 1)
    (ell : ℕ) [Fact ell.Prime]
    (_hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    (f : T ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : V ⟶ T) [IsOpenImmersion j]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))))
    (_hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf
      (higherDirectImage (ULift.{u + 1} (ZMod ell)) j (q : ℤ) F)) ∧
    (∃ cF : ℕ, ∀ q : ℕ, cF < q →
      IsZero (higherDirectImage (ULift.{u + 1} (ZMod ell)) j (q : ℤ) F)) := by
  sorry

end AlgebraicGeometry.Etale
