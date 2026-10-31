/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects
import WeilConjectures.SecSmoothPurity.ReductionExceptionalRealization
import WeilConjectures.SecSmoothPurity.ReductionExceptionalConservativity
import WeilConjectures.SecSmoothPurity.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility

/-!
# Exceptional inverse image and coefficient extension

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.md` (blueprint: det-sp-reduction-exceptional).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem reductionCtf_good (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (M : proEtaleDerivedCategory T A) :
    spFiniteConstructibleTor T A M ↔
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj M)} ∧
        (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
          ((DerivedCategory.homologyFunctor _ i).obj M)) ∧
        HasFiniteProEtaleTorAmplitude T A M := by
  constructor
  · rintro ⟨⟨a, b, hab, hz⟩, hc, ht⟩
    refine ⟨?_, hc, ht⟩
    apply Set.Finite.subset (Set.finite_Icc a b)
    intro i hi
    constructor <;> by_contra! hn
    · exact hi (hz i (.inl hn))
    · exact hi (hz i (.inr hn))
  · rintro ⟨hb, hc, ht⟩
    obtain ⟨a, ha⟩ := hb.bddBelow
    obtain ⟨b, hb⟩ := hb.bddAbove
    refine ⟨⟨min a b, b, min_le_right _ _, ?_⟩, hc, ht⟩
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi

private theorem reductionCtf_iso {T : Scheme.{u}} {A : Type u}
    [CommRing A] [Finite A] {K L : proEtaleDerivedCategory T A}
    (e : K ≅ L) (h : spFiniteConstructibleTor T A K) :
    spFiniteConstructibleTor T A L := by
  obtain ⟨hb, hc, a, b, ht⟩ := (reductionCtf_good T A K).mp h
  apply (reductionCtf_good T A L).mpr
  refine ⟨hb.subset (fun i hi hz ↦ hi
    (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)),
    ?_, a, b, ht.1, ?_⟩
  · intro i
    apply (proEtaleModuleRestriction_constructible_iff T A _).mpr
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e))
      ((proEtaleModuleRestriction_constructible_iff T A _).mp (hc i))
  · intro N P hN f hf hP M i hi
    obtain ⟨q⟩ := hN
    exact ht.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem reductionMate_existsUnique
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {LA : C ⥤ D} {GA : D ⥤ C} {LB : E ⥤ F} {GB : F ⥤ E}
    (a : LA ⊣ GA) (b : LB ⊣ GB) (S : C ⥤ E) (T : D ⥤ F)
    (β : LA ⋙ T ≅ S ⋙ LB) :
    ∃! c : GA ⋙ S ⟶ T ⋙ GB,
      ∀ K, LB.map (c.app K) ≫ b.counit.app (T.obj K) =
        β.inv.app (GA.obj K) ≫ T.map (a.counit.app K) := by
  let c := (mateEquiv a b (TwoSquare.mk S LA LB T β.inv)).natTrans
  have hc (K : D) : LB.map (c.app K) ≫ b.counit.app (T.obj K) =
      β.inv.app (GA.obj K) ≫ T.map (a.counit.app K) :=
    mateEquiv_counit a b (TwoSquare.mk S LA LB T β.inv) K
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  ext K
  apply (b.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using (hc' K).trans (hc K).symm

/-- The canonical exceptional coefficient comparison on Dctf.
Source: blueprint latest, sk-lem-sp-reduction-exceptional.md
(blueprint: det-sp-reduction-exceptional).

Lean assembly: construct the realized adjunctions using
`reductionExceptionalRealization_exists`, form the mate of the direct-image comparison,
and use `reductionExceptional_chartEquation` and `reductionExceptional_components_isIso`.
The thirteen source steps underlying those lemmas are recorded below:

1. Put $T_X=(-)_B$, $T_Y=(-)_B$, $F_R=Rf_{!,R}$ and $G_R=f_R^!$. By
[det-sp-scalar-extension-functor](1),(2), $T_X,T_Y$ preserve the indicated categories. By
[sk-prop-sf-rf-shriek-preservation], $F_R\dashv G_R$ is an adjunction on them. Applying
[det-sp-reduction-direct-image] to $G_AK$ gives the natural isomorphism $b(G_AK):T_YF_AG_AK\to
F_BT_XG_AK$. Thus $\tau_K=T_Y(\varepsilon_A(K))b(G_AK)^{-1}$ is a well-typed map $F_BT_XG_AK\to
T_YK$, with no flatness requirement on $B$ over $A$.

2. Under the adjunction of [sk-prop-sf-rf-shriek-preservation], define $c_K$ to be the transpose
of $\tau_K$. The inverse transpose of $h:T_XG_AK\to G_BT_YK$ is $\varepsilon_B(T_YK)F_B(h)$.
Hence its counit identity is exactly the displayed identity in the statement, and this identity
determines $c_K$ uniquely. For $u:K\to L$, naturality of $b$ [det-sp-reduction-direct-image] and
of $\varepsilon_A$ gives $T_Y(u)\tau_K=\tau_LF_BT_XG_A(u)$. Naturality of $\varepsilon_B$
identifies the left side with the inverse transpose of $G_BT_Y(u)c_K$ and the right side with
the inverse transpose of $c_LT_XG_A(u)$. Injectivity of the hom bijection proves naturality of
$c$.

3. For any scheme $T$ used below and $R=A,B$, the finite ring $R$ is discrete Noetherian: every
ascending chain of ideals stabilizes since the underlying set is finite. The scheme $T$ is
Noetherian by [lem-weil-pbc-finite-type-over-noetherian], hence qcqs. Apply
[det-pe-finite-tor-comparison-noetherian]: $\nu_T^*$ is an equivalence on the bounded
constructible finite-Tor categories, preserving and reflecting every Tor interval. Thus its
stated conclusion supplies exactly the finite-Tor equivalence needed by
[det-sp-et-proet-adjunction-transfer], for arbitrary finite rings, not just DVR quotients.
Comparison inverse image is exact and carries constant rings to constant rings by
[lem-sf-comparison-pullback-exact]; its tensor comparison is
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. These comparisons identify coefficient
extension and the pullback, Tate-tensor and shift functors on the two sites. The Tate sheaves
are locally free of rank one by [lem-asd-finite-etale-twist-line]. The ordinary compact-support
functor also restricts to these subcategories. Indeed its value $F^{\mathrm{et}}L$ on bounded
input is bounded below, since it is $Rr_*j_!L$ with $j_!$ exact. The site comparison of
[lem-sp-et-proet-coefficient-compatibility] identifies $\nu^*F^{\mathrm{et}}L$ with $F\nu^*L$,
which is in $\Dctf$ by [sk-prop-sf-rf-shriek-preservation]. Choose bounded constructible etale
origin $M$ for this object using [lem-weil-pbc-finite-ring-constructible-derived-origin]. Full
faithfulness on $D^+$ [thm-weil-pbc-site-comparison] lifts the isomorphism
$\nu^*F^{\mathrm{et}}L\simeq\nu^*M$ to $F^{\mathrm{et}}L\simeq M$. The Tor reflection already
cited then gives $F^{\mathrm{et}}L\in\Dctf$.

4. We compute the ordinary-etale chart adjunction in Steps 7–11 and then transport it. Its right
functor $H_{g,R}=e^*p_d^*(-)(d)[2d]$ restricts to the finite-Tor constructible categories: after
$\nu^*$ it is the pro-etale pullback followed by a locally trivial rank-one tensor and a shift.
Pullback preserves $\Dctf$ by [det-proper-base-change-unbounded-pullback], with the finite-ring
module-object/ordinary-module identification of [sk-prop-sf-rf-shriek-preservation]; rank-one
tensor is locally the identity, and shifts preserve boundedness and translate Tor intervals. The
equivalence of Step 3 reflects this membership. The specified site comparison
$c_{g,R}:\nu_Y^*F^{\mathrm{et}}_{g,R}\simeq F_{g,R}\nu_U^*$ is an isomorphism by
[lem-sp-et-proet-coefficient-compatibility]. Consequently [det-sp-et-proet-adjunction-transfer]
identifies the transported right adjoint with $g_R^!$, retaining the actual counit
$$\epsilon^{\mathrm{pro}}_{g,R}=\nu_Y^*(\epsilon^{\mathrm{et}}_{g,R})c_{g,R}^{-1}.$$ The first
square and its following counit clause in [lem-sp-et-proet-coefficient-compatibility] carry a
coefficient-counit identity with the ordinary-etale $\beta_g$ to that same identity with the
named pro-etale $b_g$. We use that precise assertion in Step 11, so the transported comparison
is the fixed-compactification map of the statement.

5. For $q:\mathbf P^1_S\to S$ over any base chart in our setting, choose $N=\ell^n$ annihilating
both rings and put $R_0=\mathbf Z/N$. The bases and projective lines are Noetherian and $N$ is
invertible; Noetherianity follows from [lem-weil-pbc-finite-type-over-noetherian]. By
[lem-asd-ordinary-finite-p1-adjunction], for $R=A,B$ the splitting $s_R:R_S(1)[2]\oplus
R_S\xrightarrow{\sim}Rq_*R_{\mathbf P^1_S}(1)[2]$ has components the shifted unit and the
scalar-extended Kummer class $h_R$. More precisely, the cited statement defines $h_R$ by first
taking the Kummer class over $R_0$, extending scalars to $R$ on $\mathbf P^1_S$, and then
applying inverse-image/direct-image adjunction. Write $H_0:(R_0)_{\mathbf
P^1_S}\to(R_0)_{\mathbf P^1_S}(1)[2]$ for that Kummer morphism. Then $H_R=H_0\otimes^L_{R_0}R$
has adjunct $h_R$. Derived tensor associativity gives
$(H_0\otimes^L_{R_0}A)\otimes^L_AB=H_0\otimes^L_{R_0}B$, with the canonical identifications of
both endpoints; hence $(H_A)_B=H_B$. Step 6 checks the corresponding direct-image equality with
the named coefficient map by transposition.

6. On the ordinary etale site put $b_q=\beta_q^{\mathrm{et}}$, the proper comparison explicitly
defined and asserted invertible in [lem-sp-et-proet-coefficient-compatibility], evaluated on
$A_{\mathbf P^1_S}(1)[2]$. The source twist is locally free of rank one by
[lem-asd-finite-etale-twist-line]. Thus its derived scalar extension is ordinary tensor and is
canonically $B_{\mathbf P^1_S}(1)[2]$: on an etale trivialization the map is $A\otimes_A B\to
B$, $a\otimes b\mapsto ab$, and these maps respect the transition units of $\mu_N$. On the two
components of the splitting of Step 5 the comparison sends the unit to the unit and $(h_A)_B$ to
$h_B$. For the unit this follows from the defining counit-transpose projection map: its
composite with the pullback/direct-image unit is the coefficient-extended unit, by the
adjunction triangle identity; for the second component, take the inverse transpose of
$b_q(h_A)_B$ under $q_B^*\dashv Rq_{*,B}$. The defining counit identity for $b_q$ and naturality
give $(\epsilon_{q,*,A}\,q_A^*h_A)_B=(H_A)_B=H_B$, where $\epsilon_{q,*,A}$ is the ordinary
pullback/direct-image counit, not the exceptional counit. The inverse transpose of $h_B$ is also
$H_B$ by definition; injectivity of this hom bijection gives $b_q(h_A)_B=h_B$. Thus
$b_q(s_A)_B=s_B$. By [def-amb-p1-trace], $t_{q,R}=\operatorname{pr}_2s_R^{-1}$. Multiplying the
preceding equality by inverses gives $$t_{q,B}\,b_q=(t_{q,A})_B.$$ Indeed both composites with
$(s_A)_B$ are the projection onto the second summand. This is a two-component calculation with
an invertible splitting, not an extra lemma asserting the desired exceptional comparison.

7. The actual projective-line counit is $\epsilon_{q,R,K}=(1_K\otimes t_{q,R})\pi_R^{-1}$ with
the tensor unit constraint, by [lem-asd-ordinary-finite-p1-adjunction] and [def-amb-p1-trace].
Put $L_R=R_{\mathbf P^1_S}(1)[2]$ and $F_R=Rq_{*,R}$, so $G_{q,R}K=q_R^*K\otimes_R^L L_R$. The
canonical tensor/pullback comparison is [lem-weil-pbc-ringed-topoi-derived-tensor-pullback].
Apply the square of [lem-weil-pbc-ringed-exchange-tensor-coherence] to the ringed-topos square
with scheme maps $q,q$ and coefficient change $A\to B$. After its canonical tensor and symmetry
identifications, the square says exactly $$ F_B(a_{q,K})\,b_q(G_{q,A}K)\,(\pi_A)_B
=\pi_B\,(1_{K_B}\otimes b_q(L_A)), $$ where
$a_{q,K}:(q^*K(1)[2])_B\xrightarrow{\sim}q^*(K_B)(1)[2]$. Both sides start at
$K_B\otimes_B^L(F_AL_A)_B$ and end at $F_BG_{q,B}(K_B)$. Compose with
$\epsilon_{q,B,K_B}=(1\otimes t_{q,B})\pi_B^{-1}$. The right side becomes
$1_{K_B}\otimes(t_{q,B}b_q(L_A))=1_{K_B}\otimes(t_{q,A})_B$ by Step 6; this is
$(\epsilon_{q,A,K})_B(\pi_A)_B$. Here $K$ ranges over $\Dctf(S_{\mathrm{et}},A)$, the only
inputs used in Steps 9–11: then $G_{q,A}K=q^*K\otimes^L_AL_A$ is again bounded constructible of
finite Tor amplitude (pullback, a locally free rank-one twist [lem-asd-finite-etale-twist-line]
and a shift), so $b_q(G_{q,A}K)$ is an isomorphism by
[lem-sp-et-proet-coefficient-compatibility]; $\pi_A$ is invertible because the counit of
[lem-asd-ordinary-finite-p1-adjunction] is written with $\pi^{-1}$. Since $(\pi_A)_B$ and
$b_q(G_{q,A}K)$ are isomorphisms, cancellation gives $$ (\epsilon_{q,A,K})_B\,b_q(G_{q,A}K)^{-1}
=\epsilon_{q,B,K_B}\,Rq_{*,B}(a_{q,K}). $$ Thus the actual counit at every
$K\in\Dctf(S_{\mathrm{et}},A)$ has the required coefficient identity (the uninverted form
$\epsilon_{q,B,K_B}Rq_{*,B}(a_{q,K})b_q(G_{q,A}K)=(\epsilon_{q,A,K})_B$ holds for every $K$).
This argument uses no flatness of $B$ over $A$.

8. For an open immersion $j$ or a separated finite-type etale chart map $e$, use the exact
sum-extension adjunction [lem-amb-etale-adjoint-locality]. Its derived coefficient comparison is
the summandwise tensor identification $\sigma_e$ specified by
[lem-sp-et-proet-coefficient-compatibility]. Compute its counit before passage to the derived
category. The direct-sum presheaf [def-weil-pbc-etale-sum-extension] and its geometric-fibre
description [lem-amb-etale-sum-stalks] give the evaluation map $\bigoplus_x M_x\to M$,
$(m_x)\mapsto\sum_xm_x$. On every summand the two coefficient-extended evaluations agree because
$$ (\sum_xm_x)\otimes b=\sum_x(m_x\otimes b). $$ This is equality of the sheaf maps induced from
the presheaf sums; it is not a test for equality of arbitrary derived morphisms on stalks. The
same degreewise equality on the K-flat representatives computing $\sigma_e$ gives
$$\epsilon_{e,B}\,De_{!,B}(a_e)=T(\epsilon_{e,A})\sigma_e(e_A^*-)^{-1},$$ where $a_e:T
e_A^*\simeq e_B^*T$ is the canonical pullback/tensor comparison. The open case is the same
formula with at most one lift. No flatness of $B$ over $A$ is needed.

9. Use clause (2) of the existing Mathlib leaf [lem-weil-pbc-mate-pasting] for the two
consecutive chart adjunctions $F_{i,R}\dashv G_{i,R}$, $i=1,2$, with coefficient functors
$T_0,T_1,T_2$. The square at stage $i$ is $b_i^{-1}:F_{i,B}T_{i-1}\to T_iF_{i,A}$. Its mate is
$a_i:T_{i-1}G_{i,A}\to G_{i,B}T_i$, precisely because its counit equation is the identity
checked in Steps 7 and 8. Put $$ b_{12}=F_{2,B}(b_1)b_2(F_{1,A}-),\qquad
a_{12}=G_{1,B}(a_2)a_1(G_{2,A}-). $$ Clause (2) states that $a_{12}$ is the mate of the pasted
square $b_{12}^{-1}$ for the composite adjunction of [def-weil-pbc-composite-adjunction]. Taking
its inverse transpose therefore gives
$$\epsilon_{12,B}F_{2,B}F_{1,B}(a_{12})=T_2(\epsilon_{12,A})b_{12}(G_{1,A}G_{2,A}-)^{-1}.$$ This
applies an existing general composition theorem instead of hiding a separate lemma with its own
adjunction hypotheses in the chart calculation.

10. Apply Step 9 first to the open-extension adjunction for $\mathbf A^1_S\hookrightarrow\mathbf
P^1_S$ and the projective-line adjunction from Step 7. This gives the required
coefficient-counit identity for the affine-line adjunction. By [lem-amb-affine-space-top-trace],
the $d$-coordinate adjunction is the ordered composite of these affine-line adjunctions. Its
$d=0$ case is the identity, where both comparisons are identities; if the identity holds for
$d$, apply Step 9 with one further affine-line factor to obtain it for $d+1$. Tensor
associativity and pullback monoidality of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]
identify the resulting $a_{12}$ with $(p_d^*K(d)[2d])_B\simeq p_d^*(K_B)(d)[2d]$. The
left-functor composition isomorphism is supplied by [lem-amb-etale-compact-comparisons]. The
composition square of [lem-sp-et-proet-coefficient-compatibility] identifies $b_{12}$ with the
named compact-support coefficient map after that isomorphism; its refinement square makes this
true for the chosen compactification as well. Thus induction proves the identity with the
specified $b_{p_d}$, not just an unspecified isomorphism between its endpoints.

11. On a chart $g=fj=p_de$ the composite adjunction of Steps 8–10 has right adjoint
$H_{g,R}K=e^*p_d^*K(d)[2d]$ and composite counit, by [def-weil-pbc-composite-adjunction] and the
etale adjunction [lem-amb-etale-adjoint-locality]. After the counit-preserving left-functor
identifications below, the restriction isomorphism $j^*G_R\simeq G_{g,R}$ of
[det-sf-mate-open-restriction] identifies it with this right adjoint by the counit-preserving
uniqueness of right adjoints. Apply the coefficient identities of Steps 7–10 and the transport
of Step 4. With $a_{g,K}:(H_{g,A}K)_B\xrightarrow{\sim}H_{g,B}(K_B)$ they give precisely $$
(\epsilon_{g,A,K})_B\,b_g(H_{g,A}K)^{-1} =\epsilon_{g,B,K_B}\,Rg_{!,B}(a_{g,K}). $$ This
constructs the chart adjunction for arbitrary finite $A,B$ from existing general finite-ring
projective-line and etale adjunctions; the narrower $\mathbf Z/\ell^n$ chart lemma is not
applied to an arbitrary finite ring. The left adjoint of this composite is $Rp_{d!}\circ
De_{\Sigma!}$; by [lem-asd-etale-compact-support-normalization] the identification
$c_e:Re_!^c\simeq De_{\Sigma!}$ carries the compact-support adjunction of $e$ to
$De_{\Sigma!}\dashv e^*$ with its sum/evaluation counit, so composing with the composition map
$\alpha$ identifies the chart left adjoint with $Rg_!$, counits included. The etale
normalization square of [lem-sp-et-proet-coefficient-compatibility] says that under $c_e$ the
coefficient map $\beta_e^c$ is the summandwise tensor identification used for $e$ in Steps 8–10.
Apply the composition and refinement squares of [lem-sp-et-proet-coefficient-compatibility] to
the compactifications of $e$, $p_d$ and $g=p_de$. They identify the coefficient map used in the
composite chart counit with $b_g$ for the chosen compactification. Hence the displayed counit
identity uses exactly the map defining the transpose $c_{g,K}$.

12. The comparison $c_K$ restricts to the comparison for $g=fj$. Here is the complete
cancellation. Write $J_R=j_{!,R}$, $U_R=j_R^*$, and $v_R:J_RU_R\to1$ for the open counit, and
let $a_U:T_UU_A\simeq U_BT_X$ be the restriction/tensor identification. By
[def-weil-pbc-composite-adjunction] and [det-sf-mate-open-restriction], the counit for $g$ is
$\epsilon_{f,R}\,F_{f,R}(v_R G_{f,R})$. The canonical compact-support comparison is
$$b_g(N)=F_{f,B}(b_j(N))\,b_f(J_AN),$$ as follows by the transpose computation in Steps 8–10.
After using $a_U$ to identify $T_UU_AG_AK$ with $U_BT_XG_AK$, the inverse transpose of $U_Bc_K$
under the composite adjunction is $$\epsilon_{f,B}\,F_{f,B}(v_B G_B T_YK)\,F_{f,B}J_B(U_Bc_K)
=\epsilon_{f,B}\,F_{f,B}(c_K)\,F_{f,B}(v_B T_XG_AK),$$ by naturality of $v_B$. The defining
equation of $c_K$ turns this into $$T_Y\epsilon_{f,A}\;b_f(G_AK)^{-1}\;F_{f,B}(v_B T_XG_AK).$$
Step 8's open-counit scalar equality is an equality on the ordinary etale site; the pro-etale
open adjunction $J_R\dashv U_R$ is its transport by [det-sp-et-proet-adjunction-transfer] (Step
4 applied to $j$, all objects having etale origin by Step 3), and the first square of
[lem-sp-et-proet-coefficient-compatibility] carries the identity with $\beta_j$ to the same
identity with $b_j$. So on the pro-etale site $$v_B T_XG_AK=T_X(v_A G_AK)\,b_j(U_AG_AK)^{-1}.$$
Naturality of $b_f$ now rewrites the preceding inverse transpose as
$$T_Y\epsilon_{f,A}\;T_YF_{f,A}(v_A G_AK)\;b_f(J_AU_AG_AK)^{-1}\;F_{f,B}(b_j(U_AG_AK)^{-1})
=T_Y(\epsilon_{g,A,K})\,b_g(U_AG_AK)^{-1}.$$ This is exactly the inverse transpose defining
$c_{g,K}$; hence $j^*c_K=c_{g,K}$. Step 11 says the canonical $a_{g,K}$ has this same inverse
transpose, so uniqueness gives $j^*c_K=a_{g,K}$, the required chart identification and an
isomorphism. Here the composition square of [lem-sp-et-proet-coefficient-compatibility] for the
pair $(j,f)$, after the $\alpha_A,\alpha_B$ identifications, is exactly the displayed formula
$b_g=F_{f,B}(b_j)b_f(J_A-)$. Its refinement square identifies this formula with the comparison
for the fixed compactification of $g$, so the final inverse transpose is the named one defining
$c_{g,K}$.

13. Smooth local normal form [sbc-thm-etale-local-normal-form] gives coordinate charts after
replacing the base and source by affine neighborhoods. Compose its etale map to $\mathbf A^d_V$
with the open immersion $\mathbf A^d_V\hookrightarrow\mathbf A^d_Y$; this is an etale chart over
$Y$. Pure relative dimension fixes its dimension to $d$. The affine neighborhoods cover $X$.
They are Noetherian, as are $X,Y$ and their affine spaces, by
[lem-weil-pbc-finite-type-over-noetherian]. Open subschemes remain Noetherian by
[lem-weil-pbc-noetherian-open-subscheme-noetherian], so the chart open immersions are
quasi-compact and are of finite type by [lem-weil-pbc-qc-open-immersion-finite-type]. By
[lem-weil-pbc-qcqs-morphism-permanence](1), the etale coordinate map from an affine source to
the separated affine-space target is of finite presentation, hence finite type. It is separated:
its relative diagonal is the base change of the closed diagonal of its separated $k$-source
along $U\times_{\mathbf A^d_Y}U\to U\times_kU$, hence closed by
[lem-weil-pbc-proper-fp-permanence](b). Thus all these maps satisfy the hypotheses of the
adjunctions used above. Step 12 makes every restriction of $c_K$ an isomorphism. Clause (3) of
[det-sf-mate-open-restriction] detects isomorphisms on this open cover, and proves $c_K$ is an
isomorphism globally. Only isomorphism detection is used here; no assertion that restriction is
faithful on all derived morphisms is needed.
-/
theorem reductionExceptional_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    ∃ (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
      (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
        spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
      (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
      (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
        spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj)),
      ∃ (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
        (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
        (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
        (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB),
        ∃ (RA : ReductionExceptionalRealization A j p hFA GA adjA)
          (RB : ReductionExceptionalRealization B j p hFB GB adjB),
        ∃ hb : ∀ K : spFiniteConstructibleTorCategory Y A,
          IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj),
        ∃! c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB,
          (∀ K : spFiniteConstructibleTorCategory Y A,
            (reductionCompactSupport B j p).map (c.app K).hom ≫
                (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
              @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
                  (hb K) ≫
                (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) ∧
          (∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)) ∧
          ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB
            RA RB c := by
  classical
  have hF (R : Type u) [CommRing R] [Finite R]
      (hR : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0)
      (M : spFiniteConstructibleTorCategory X R) :
      spFiniteConstructibleTor Y R ((reductionCompactSupport R j p).obj M.obj) := by
    obtain ⟨hb, hc, ht⟩ := (reductionCtf_good X R M.obj).mp M.property
    have h := (reductionDirectImage_isIso ℓ pchar hp hℓ k f j p hf hR hR
      (RingHom.id R) M.obj hb hc ht).2
    exact reductionCtf_iso ((scalarExtensionFunctor_identity Y).app _)
      ((reductionCtf_good Y R _).mpr ⟨h.1, h.2.1, h.2.2.1⟩)
  let hFA := hF A hA
  let hFB := hF B hB
  have hS (T : Scheme.{u}) (M : spFiniteConstructibleTorCategory T A) :
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj M.obj) := by
    obtain ⟨hb, hc, a, b, ht⟩ := (reductionCtf_good T A M.obj).mp M.property
    obtain ⟨hb', hc', ht'⟩ := scalarExtensionFunctor_preserves_constructible_tor
      ℓ hA hB φ T M.obj hb hc a b ht
    exact (reductionCtf_good T B _).mpr ⟨hb', hc', a, b, ht'⟩
  obtain ⟨GA, adjA, ⟨RA⟩⟩ :=
    reductionExceptionalRealization_exists ℓ pchar hp hℓ k f j p hf A hA hFA
  obtain ⟨GB, adjB, ⟨RB⟩⟩ :=
    reductionExceptionalRealization_exists ℓ pchar hp hℓ k f j p hf B hB hFB
  have hcomp (M : spFiniteConstructibleTorCategory X A) :
      IsIso ((reductionDirectImageComparison φ j p).app M.obj) := by
    have hM := (reductionCtf_good X A M.obj).mp M.property
    exact (reductionDirectImage_isIso ℓ pchar hp hℓ k f j p hf hA hB φ M.obj
      hM.1 hM.2.1 hM.2.2).1
  let beta : reductionCtfCompactSupport A j p hFA ⋙ reductionCtfScalar φ Y (hS Y) ≅
      reductionCtfScalar φ X (hS X) ⋙ reductionCtfCompactSupport B j p hFB :=
    NatIso.ofComponents
      (fun M ↦ by
        have := hcomp M
        exact (spFiniteConstructibleTor Y B).fullyFaithfulι.preimageIso
          (asIso ((reductionDirectImageComparison φ j p).app M.obj)))
      (by
        intro M N g
        apply ObjectProperty.hom_ext
        exact (reductionDirectImageComparison φ j p).naturality g.hom)
  obtain ⟨c, hc, hu⟩ := reductionMate_existsUnique adjA adjB
    (reductionCtfScalar φ X (hS X)) (reductionCtfScalar φ Y (hS Y)) beta
  have hc' (K : spFiniteConstructibleTorCategory Y A) :
      (reductionCompactSupport B j p).map (c.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y (hS Y)).obj K)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
          (hcomp (GA.obj K)) ≫
          (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom := by
    exact congrArg (fun v ↦ v.hom) (hc K)
  have hchart := reductionExceptional_chartEquation ℓ pchar hp hℓ k f d j p hf hA hB φ
    hFA hFB (hS X) (hS Y) GA GB adjA adjB RA RB c (fun K ↦ hcomp (GA.obj K)) hc'
  refine ⟨hFA, hFB, hS X, hS Y, GA, GB, adjA, adjB, RA, RB,
    (fun K ↦ hcomp (GA.obj K)), c, ⟨hc', ?_, hchart⟩, ?_⟩
  · exact reductionExceptional_components_isIso ℓ pchar hp hℓ k f d j p hf hA hB φ
      hFA hFB (hS X) (hS Y) GA GB adjA adjB RA RB c hchart
  · intro c' hc'
    apply hu c'
    intro K
    apply ObjectProperty.hom_ext
    exact hc'.1 K

end AlgebraicGeometry.ProEtale
