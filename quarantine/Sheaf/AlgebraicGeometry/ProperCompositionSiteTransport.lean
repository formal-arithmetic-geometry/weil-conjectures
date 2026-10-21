/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized
public import Sheaf.Paper.RefinementComparisonIsomorphism

import Sheaf.AlgebraicGeometry.ProperOpenComparison
import Sheaf.AlgebraicGeometry.OpenSectionClopen
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.Paper.ProEtaleCompositionTowerNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Proper-factor composition and site comparison

Source: Stacks Project, more-etale.tex, Tags 0F7J, 0F7I and 0F7B;
main-20261015, thm-sf-comp-composition, Construction paragraph
(blueprint: lem-trf-proper-composition-site-transport).

All comparisons below are assembled from the specified proper counit mate and the
unit-normalized open-extension comparison. The compositor is the recorded compositor
on the full bounded-below etale-origin category, evaluated on the comparison image.

## Main definitions

* `properTransportComparison`: the specified comparison c on a chosen candidate.
* `properTransportEtaleComposition`, `properTransportProEtaleComposition`: the
  recorded compositors transported to arbitrary chosen candidates.

## Main statements

* `properCompositionSiteTransport`: the mixed composition square.
* `properCompositionSiteTransport_refinement`: its mixed refinement compatibility.
* `properCompositionSiteTransport_proper`: identity-open normalization c = b.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The finite-level coefficient ring, in the standard site coefficient universe.
Source: coefficient convention in Stacks 0F7J and the blueprint Construction
(blueprint: lem-trf-proper-composition-site-transport). -/
abbrev properTransportCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) :=
  Padic.coefficientExtensionRing l E n

/-- Register the recorded positive-level finiteness theorem, without an extra hypothesis.
Source: the finite-level coefficient convention in the blueprint Construction
(blueprint: lem-trf-proper-composition-site-transport). -/
instance properTransportCoefficient_finite (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (properTransportCoefficient l E n) :=
  Padic.finite_coefficientExtensionRing l E n n.property

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The named comparison c on a chosen model: first the proper counit mate b,
then the proper direct image of the unit-normalized open comparison e.
The existing ambient comparison has the opposite orientation.
Source: Stacks 099R, 09AF and 0F7J, blueprint defining formula for c
(blueprint: lem-trf-proper-composition-site-transport). -/
def properTransportComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (compactSupportSiteComparison A c).symm.app L

/-- The canonical change of compactification on the full etale-origin category.
It is the unique descent of the ordinary canonical change conjugated by the named
proper/open site comparisons. All ambient morphisms are retained.
Source: Stacks 0F7I and blueprint thm-sf-comp-composition, independence paragraph
(blueprint: lem-trf-proper-composition-site-transport). -/
def properTransportCandidateChange {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (compactSupportSiteComparison A c ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.isoWhiskerRight
          (Etale.rightDerivedLowerShriekOfCompactificationIso A c d)
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) ≪≫
      (compactSupportSiteComparison A d).symm)

/-- Evaluate the recorded pro-etale compositor on arbitrary chosen candidates.
The four factors only change the inner candidate, the outer candidate, apply the
recorded compositor, and change the composite candidate. This is canonical comparison
transport, not a choice of a natural isomorphism.
Source: blueprint thm-sf-comp-composition, Construction and independence
(blueprint: lem-trf-proper-composition-site-transport). -/
def properTransportProEtaleComposition {X Y Z : Scheme.{u}}
    (h : X ⟶ Y) (f : Y ⟶ Z) [QuasiCompact h] [QuasiCompact f]
    (ch : Compactification h) (cf : Compactification f)
    (chf : Compactification (h ≫ f))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  letI : HasCompactification h := ⟨⟨ch⟩⟩
  letI : HasCompactification f := ⟨⟨cf⟩⟩
  letI : HasCompactification (h ≫ f) := ⟨⟨chf⟩⟩
  let K := (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).mapIso
      ((properTransportCandidateChange A ch
        (HasCompactification.compactification h)).app K) ≪≫
    (properTransportCandidateChange A cf
      (HasCompactification.compactification f)).app ((originCompactSupport A h).obj K) ≪≫
    (originCompositionAmbient A h f).app K ≪≫
    (properTransportCandidateChange A (HasCompactification.compactification (h ≫ f))
      chf).app K

/-- The specified ordinary compositor on arbitrary compactification candidates.
Source: Stacks 0F7J, compatible-tower calculation and compactification independence
(blueprint: lem-trf-proper-composition-site-transport). -/
def properTransportEtaleComposition {X Y Z : Scheme.{u}}
    (h : X ⟶ Y) (f : Y ⟶ Z) [QuasiCompact h] [QuasiCompact f]
    (ch : Compactification h) (cf : Compactification f)
    (chf : Compactification (h ≫ f)) :=
  letI : HasCompactification h := ⟨⟨ch⟩⟩
  letI : HasCompactification f := ⟨⟨cf⟩⟩
  letI : HasCompactification (h ≫ f) := ⟨⟨chf⟩⟩
  Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationIso A ch
        (HasCompactification.compactification h))
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) h)
      (Etale.rightDerivedLowerShriekOfCompactificationIso A cf
        (HasCompactification.compactification f)) ≪≫
    Etale.unboundedEtaleLowerShriekCompIso A h f ≪≫
    Etale.rightDerivedLowerShriekOfCompactificationIso A
      (HasCompactification.compactification (h ≫ f)) chf

/-- Evaluate c_f at F_h L, using the canonical bounded-below representative of F_h L.
The first and last factors are precisely the inclusion compatibilities; no choice of
representative or extra boundedness assumption is made.
Source: Stacks 0F7J and blueprint c-composition equation on D-plus
(blueprint: lem-trf-proper-composition-site-transport). -/
def properTransportComparisonAfterInner {X Y Z : Scheme.{u}}
    {h : X ⟶ Y} {f : Y ⟶ Z} (ch : Compactification h) (cf : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) ch).app L).symm) ≪≫
    properTransportComparison A cf
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) ch).obj L) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) ch).app L))

/-- The named composition square, on every bounded-below etale complex, with exactly
one-or-both proper factors allowed and arbitrary specified compactifications.
Source: Stacks 0F7J, 0F7B, and main-20261015 thm-sf-comp-composition, Construction
(blueprint: lem-trf-proper-composition-site-transport).

Proof plan (the node's ten steps):
1. Every finite-type $k$-scheme in the statement is Noetherian: a field is Noetherian (its ideals
are $0,k$), and apply [lem-weil-pbc-finite-type-over-noetherian]. A proper map is finite type by
definition, and finite-type morphisms compose [lem-sfb-finite-type-composition-base-change](1).
Compactification ambient schemes are consequently finite type over $k$, so the same Noetherian
result applies to them. They are quasi-compact by the meaning of Noetherian and quasi-separated by
[lem-weil-pbc-locally-noetherian-quasi-separated]; [lem-weil-pbc-qcqs-morphism-permanence](1)
therefore makes all the tower arrows qcqs. In particular the proper factors meet the hypotheses of
the named direct-image comparisons. Fix the notation $P_t^s=Rt_{s,*}$, $J_v^s=v_{s,!}$, and write
$D^s_{t,u}:P_t^sP_u^s\to P_{tu}^s$ for the canonical compositor, the inverse of the comparison in
[lem-weil-derived-direct-image-composition].
2. The etale and pro-etale open extensions are exact, and $C_T=\nu_T^*$ is exact. Thus the sheaf
isomorphism $e_v$ and its open-composition identities descend degreewise through localization at
quasi-isomorphisms. The same applies to its open-unit normalization: it uses only exact open
restrictions, open extensions and $C$. These equations therefore hold on $D^+$. In particular
$e_{\mathrm{id}}=1$: its defining unit equation for the identity open says exactly this. On any
fixed model $u=tv$, first apply $b_{t,J_v^eM}$, then $P_t^p(e_{v,M})$. These are isomorphisms and
give exactly $c_u$ in the statement. Here $J_v^eM\in D^+$ and the comparison exhibits $F_u^pC M$
as the etale-origin object with witness $F_u^eM$.
3. Use [lem-cbc-compactifiable-compatible-tower] on the chosen compactifications of $f$ and $fh$.
It supplies a compatible model $$V\xrightarrow{i}\overline V\xrightarrow qW,\quad U\xrightarrow
a\overline U\xrightarrow p\overline V,\quad H=\overline U\times_{\overline V}V,$$ with
$b:H\hookrightarrow\overline U$, $r:H\to V$, $j:U\hookrightarrow H$, $bj=a$, $rj=h$, and Cartesian
square $pb=ir$. The models for $h,f,fh$ are $(j,r),(i,q),(a,qp)$. Put $K=J_j^eL$. Write
$\gamma^s:J_i^sP_r^s\to P_p^sJ_b^s$ for the proper/open map. On this tower
[lem-amb-unbounded-compact-support-comparisons] gives $\alpha^e=D^e E^e(P_q^e\gamma^e J_j^e)$ and
specifies $\gamma^e$ as the adjoint of inverse open restriction. The new tower-normalization
statement gives the same formula for the actual $\alpha^p$ with its open-adjoint $\gamma^p$,
rather than taking that formula from a proof of another node. The ordinary general comparison
covers both proper-factor cases; the narrower proper-composition lemma applies when the INNER
factor $h$ is proper.
4. For $N\in D^+(H_e,\Lambda)$ set $$S_N=J_i^p(b_{r,N})e_{i,P_r^eN},\qquad
T_N=P_p^p(e_{b,N})b_{p,J_b^eN}.$$ Let $\lambda_N^s:i_s^*P_p^sJ_b^sN\to P_r^sN$ be open-restriction
exchange followed by $P_r^s((\eta_b^s)^{-1})$. For $s=p$ its input is $C_HN$. Apply
[lem-weil-pbc-transport-identifies-exchange] to $pb=ir$ at $J_b^eN$; its equation is precisely
compatibility of the TWO exchange arrows with $a_i,a_b,b_p,b_r$. Postcompose with the inverse
open-unit comparisons. Naturality of $b_r$ moves $(\eta_b^e)^{-1}$ through $b_r$, and the
open-unit normalization for $e_b$ cancels $b_p^*e_b\,a_b\,C_H\eta_b^e=\eta_b^p$. Consequently
$$\lambda^p_{C_HN}\,i_p^*(T_N)\,a_{i,P_p^eJ_b^eN}=b_{r,N}\,C_V(\lambda^e_N).$$ All compositions
are in $D^+(V_p,\Lambda)$; Step 2 supplies the derived open-unit equation. This is exchange
compatibility on a proper, possibly nonfinite, Cartesian square.
5. Take the two maps $\gamma^p_{C_HN}S_N$ and $T_NC_{\overline V}(\gamma^e_N)$ from $C_{\overline
V}J_i^eP_r^eN$ to $P_p^pJ_b^pC_HN$. Precompose each with $e_{i,P_r^eN}^{-1}$ and transpose under
$J_i^p\dashv i_p^*$. For the first, the transpose followed by $\lambda^p$ is $b_{r,N}$ by the
defining transpose of $\gamma^p$. For the second, use the equation in Step 4 and the unit
normalization for $e_i$; it becomes
$$b_{r,N}\,C_V(\lambda^e_N\,i_e^*(\gamma^e_N)\,\eta^e_{i,P_r^eN})=b_{r,N}.$$ The parenthesized map
is the identity because the ordinary tower statement defines $\gamma^e$ as the adjunct of
$(\lambda^e)^{-1}$. Since $\lambda^p$ is invertible and the adjunction is a bijection, the two
maps agree: $$\gamma^p_{C_HN}S_N=T_NC_{\overline V}(\gamma^e_N).$$ Thus this is an equality of the
named mixed-site interchanges; separate naturality was not used in its place.
6. Write $\mathcal R=\alpha^p_{f,h,C_UL}F_f^p(c_{h,L})c_{f,F_h^eL}$. Expand the two $c$'s and the
pro-etale tower formula at $K=J_j^eL$. In the following expression $D^pE^p$ denotes the final two
compositors to $P_{qp}^pJ_a^p$, and juxtaposition is composition, read right to left. Naturality
of $\gamma^p$ at the morphism $e_{j,L}:C_HK\to J_j^pC_UL$ (both objects of bounded-below etale
origin), that is $\gamma^p_{J_j^pC_UL}\,J_i^pP_r^p(e_{j,L})=P_p^pJ_b^p(e_{j,L})\,\gamma^p_{C_HK}$,
gives $$\mathcal
R=D^pE^p\,P_q^pP_p^pJ_b^p(e_{j,L})\,P_q^p(\gamma^p_{C_HK}J_i^p(b_{r,K})e_{i,P_r^eK})\,b_{q,J_i^eP_
r^eK}.$$
Substitute Step 5, not an inferred interchange law. The parenthesized factor becomes
$P_p^p(e_{b,K})b_{p,J_b^eK}C_{\overline V}(\gamma^e_K)$, so $$\mathcal
R=D^pE^p\,P_q^pP_p^p(J_b^p(e_j)e_{b,K})\,P_q^p(b_{p,J_b^eK})\,P_q^pC_{\overline
V}(\gamma^e_K)\,b_{q,J_i^eP_r^eK}.$$ The first equality is naturality of the specified tower map;
the second is the actual mixed square proved above.
7. Naturality of $b_q$ changes the last two factors of Step 6 to
$b_{q,P_p^eJ_b^eK}\,C_W(P_q^e\gamma_K^e)$. The COMPOSITE law of
[prop-weil-pbc-comparison-direct-image], with the counit-mate identification in
[lem-weil-pbc-transport-identifies-exchange], is
$$D^p_{q,p}\,P_q^p(b_p)\,b_qP_p^e=b_{qp}\,C_W(D^e_{q,p}).$$ The open-composition law is
$$E^p_{b,j}\,(J_b^pe_j)\,(e_bJ_j^e)=e_a\,C_{\overline U}(E^e_{b,j}).$$ Use these two equations in
the expanded expression, and naturality of the direct-image compositors to move the open factors
through $D^p$. The result is $$\mathcal
R=P_{qp}^p(e_{a,L})\,b_{qp,J_a^eL}\,C_W(D^eE^e\,P_q^e\gamma^e_K)=c_{fh,L}C_W(\alpha^e_{f,h,L}).$$
This proves the equation on the compatible tower, with both compositors named. No compatibility of
$b$ with composition is inferred from its naturality.
8. We next prove the required refinement square. For a refinement $u:c_1\to c_2$, write
$c_i=(j_i,t_i)$, so $t_1=t_2u$. Let $A_u^s:J_{j_2}^s\to P_u^sJ_{j_1}^s$ be the specified
proper/open map, and put $T=P_u^p(e_{j_1})b_u$. [lem-sf-proper-open-comparison-site-normalization]
states $A_u^pe_{j_2}=T C(A_u^e)$, hence $$(A_u^p)^{-1}T=e_{j_2}C((A_u^e)^{-1}).$$ For the ordinary
refinement statement, specialize its inner proper map to $\mathrm{id}$ and its outer map to the
morphism being compactified; thus its refinement formula covers every morphism here. On
bounded-below inputs the ordinary refinement comparisons of
[lem-amb-unbounded-compact-support-comparisons] restrict, with the same normalization, to those of
[lem-amb-etale-compact-comparisons], which are built from the map of
[def-weil-pbc-proper-open-comparison]; so the etale $A_u^e$ here is exactly the $\alpha^e_u$ of
the site-normalization lemma, and $A_u^p$ is the pro-etale $\alpha_u$ used in
[def-sf-refinement-comparison-isomorphism](a). The ACTUAL refinement maps, by
[def-sf-refinement-comparison-isomorphism](b) on the pro-etale side and the normalized ordinary
comparison statements on the etale side, are (up to taking inverses, which Step 9 allows)
$$\theta_u^s=P_{t_2}^s((A_u^s)^{-1})(D^s_{t_2,u})^{-1}.$$ We use these formulas, not just the
separate cocycle laws on the two sites. The normalization lemma applies to this Noetherian
proper/open square even when it is not Cartesian.
9. Apply the $b$ composite equation from Step 7 to $(t_2,u)$ and use naturality of $D$. With
$b_{t_2}$ below evaluated at $P_u^eJ_{j_1}^eL$, expansion gives
$$\theta_u^pc^{c_1}=P_{t_2}^p((A_u^p)^{-1}T)\,b_{t_2}\,C((D^e_{t_2,u})^{-1}).$$ Substitute Step 8,
then naturality of $b_{t_2}$ at $(A_u^e)^{-1}$:
$$\theta_u^pc^{c_1}=P_{t_2}^p(e_{j_2})\,b_{t_2,J_{j_2}^eL}\,C(P_{t_2}^e((A_u^e)^{-1})(D^e_{t_2,u})
^{-1})=c^{c_2}C(\theta_u^e).$$
This proves the mixed refinement square. It also holds for inverse comparisons and finite
composites, by multiplying the displayed equality by inverses and composing. Through a common
refinement it therefore holds for every canonical comparison. Choose a common refining tower using
the compatible-tower lemma. The separate compactification independence of the ordinary and
pro-etale $\alpha$ maps now conjugates the equality of Step 7 to the originally chosen
compactifications. This conjugation is legitimate because the mixed refinement square has just
been proved.
10. For a proper $u$ take $(\mathrm{id},u)$. Its two candidates are exactly $P_u^e$ and $P_u^p$ by
the compact-support definitions. Step 2 gives $e_{\mathrm{id}}=1$, so the defining formula is
$c_u=P_u^p(1)b_u=b_u$. If both factors are proper, choose all identity-open models: the tower
square has identity horizontal arrows, its open-adjoint interchange is the identity, and the tower
formula reduces to $D^s$; the required equation is exactly the $b$ composite equation of Step 7.
For arbitrary compactifications use Step 9. The case with only $f$ proper is covered by the
general ordinary tower formula, and that with $h$ proper agrees with the inner-proper
normalization. We have used no assertion about composition maps from the proper base-change
exchange corollary.
-/
theorem properCompositionSiteTransport
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+)
    {U V W : Scheme.{u}}
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    (h : U ⟶ V) (f : V ⟶ W)
    [h.IsOver (Spec (.of k))] [f.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hproper : IsProper h ∨ IsProper f)
    (ch : Compactification h) (cf : Compactification f)
    (chf : Compactification (h ≫ f))
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology
      (ModuleCat.{u + 1} (properTransportCoefficient l E n)))) :
    (comparisonUpperStar (ModuleCat.{u + 1} (properTransportCoefficient l E n))
      W).mapDerivedCategory.map
          ((properTransportEtaleComposition (properTransportCoefficient l E n)
            h f ch cf chf).hom.app L.obj) ≫
      (properTransportComparison (properTransportCoefficient l E n) chf L).hom =
    (properTransportComparisonAfterInner (properTransportCoefficient l E n) ch cf L).hom ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (properTransportCoefficient l E n)) cf).map
          (properTransportComparison (properTransportCoefficient l E n) ch L).hom ≫
      (properTransportProEtaleComposition (properTransportCoefficient l E n)
        h f ch cf chf L).hom := by
  sorry

/-- The mixed refinement square for the actual canonical refinement map. Thus replacing
any candidate in the composition square by a refinement, its inverse, or a finite
chain through a common refinement preserves that square.
Source: Stacks 0F7I and 0F7J; blueprint proof steps 8--9
(blueprint: lem-trf-proper-composition-site-transport).

Proof: Step 8 identifies the two specified proper/open refinement arrows using the
unit-normalized open comparison and the counit-mate direct-image comparison. Inverting
that equality identifies their inverse proper/open factors. Expand the actual
refinement arrow as the inverse direct-image compositor followed by the proper image
of this inverse proper/open factor. Apply the composite law for b (Step 7), naturality
of b at that inverse arrow, and the equation of Step 8. The result is exactly the
mixed refinement square (Step 9). Multiply by inverses for inverse comparisons, and
compose these equations for finite chains. The common-refinement cocycles on each
site then transport the composition square for the common refining tower to all
three originally chosen candidates. No cartesian-refinement hypothesis is used. -/
theorem properCompositionSiteTransport_refinement
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (properTransportCoefficient l E n)))) :
    (properTransportComparison (properTransportCoefficient l E n) c L).hom ≫
      (properTransportRefinement (properTransportCoefficient l E n) r L).hom =
    (comparisonUpperStar (ModuleCat.{u + 1} (properTransportCoefficient l E n))
      Y).mapDerivedCategory.map
          ((Etale.rightDerivedLowerShriekOfCompactificationIso
            (properTransportCoefficient l E n) c d).hom.app L.obj) ≫
      (properTransportComparison (properTransportCoefficient l E n) d L).hom := by
  sorry

/-- On a proper morphism, c is exactly the specified direct-image counit mate b under
the identity-open compactifications on the two sites.
Source: Stacks 0F7J, identity-open tower; blueprint proof steps 2 and 10
(blueprint: lem-trf-proper-composition-site-transport).

Proof: Step 2 descends the unit-normalized open comparison degreewise. Its identity-open
unit equation says e_id is the identity after the displayed identity-open adjunction
identifications. In c = P_f(e_id) b_f, functoriality sends that identity to an identity,
leaving precisely b_f (Step 10). The preceding mixed refinement square transports this
equation to any proper compactification. When both factors are proper, the compatible
tower has identity horizontal arrows and reduces to the direct-image composite law
of Step 7. The argument includes identity maps, empty schemes and zero complexes. -/
theorem properCompositionSiteTransport_proper
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (properTransportCoefficient l E n)))) :
    (compactSupportSiteComparisonPlus (properTransportCoefficient l E n)
        (Compactification.ofIsProper f)).hom.app L ≫
      (properCoincidenceIdentityOpenPlus (properTransportCoefficient l E n) f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} (properTransportCoefficient l E n))
          X).mapDerivedCategoryPlus.obj L) =
    (comparisonUpperStar (ModuleCat.{u + 1} (properTransportCoefficient l E n))
      Y).mapDerivedCategoryPlus.map
          ((Etale.properCoincidenceIdentityOpenPlus (properTransportCoefficient l E n) f).hom.app
            L) ≫
      (fixedComparisonDirectImageMatePlus (properTransportCoefficient l E n) f).app L := by
  sorry

end AlgebraicGeometry.ProEtale
