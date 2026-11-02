/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeStrictCoefficientEquations
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeReconstructionEquations
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeRawCoefficientEquation

/-! # Assembly of the ordered coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- All specified strict coefficient, reconstruction and direct-image/limit normalizations,
including equality of the ordered maps as natural transformations on the full complete category.
Source: main-20261015 blueprint, completed-exchange-coherence, second proof paragraph;
strict coefficient supplement, Stacks 099M, 099N, 0A07 and 0E48
(blueprint: lem-weil-pbc-ordered-exchange-coefficient-comparison).

Proof, following the fourteen steps of the DAG node:

1. Write $r_T=\operatorname{Res}_T$, and distinguish the one-object indexing category from
$J=\mathbf N_{\geq1}^{op}$. The coefficient maps commute with $\underline A\to A_T$: on constant
sections both composites send $a$ to its image, and the finite projections determine the map to
$A_U$. The profinite inverse-image lemma supplies both the coefficient isomorphisms and their
composition/transition compatibility. Flatness of $A_T$ over $\underline A_T$ is supplied by the
constant-completion equivalence. Apply the flat ringed diagram restriction theorem first with
the one-object category and then with $J$. All sites are small; its scalar-square and flatness
hypotheses have just been checked. In the first application it gives $a_u:r_ULu_a^*\simeq
G_ur_V$ and $\chi_u:r_VRu_*\simeq R_u^0r_U$ on AMBIENT module complexes, with the stated adjunct
compatibility. In the second it gives $p_u:r_U\mathscr L_u\simeq G_ur_V$ and $d_u:r_V\mathscr
R_u\simeq R_u^{\mathcal T}r_U$. These use the identified underlying inverse image and direct
image on a K-injective model. Explicitly the left adjoint of restriction is
$A_T\otimes_{\underline A_T}-$, exact by flatness; the right-adjoint K-injective theorem applies
for this reason, not merely because restriction itself is exact.

2. For an ARBITRARY completed-coefficient tower $Z$, apply the ringed tower pushforward/limit
comparison to the identity geometric morphism with structure map $\underline A_T\to A_T$. Its
module direct image is restriction; restriction is exact, so its derived functor is $r_T$. This
gives $\lambda_Z:r_T\mathcal L^aZ\simeq\mathcal Lr_TZ$, without a finite-reduction hypothesis.
Check its normalization together with direct image as follows. Choose a K-injective tower $Z\to
J_Z$; such resolutions exist since the small module diagram categories are Grothendieck.
Restriction preserves its K-injectivity by Step 1. Also $\lim J_Z$ is K-injective: $\lim$ is
right adjoint to the exact constant-diagram functor, so the right-adjoint theorem applies. For
each edge the ordinary and diagram direct images preserve K-injectives, since their identified
inverse images are exact. Thus $J_Z,rJ_Z,u_*J_Z,\lim J_Z$ compute the required derived
composites. Denote their direct-image/limit comparisons by $\kappa_u^a,\kappa_u^0$. On these
models the two routes below are the SAME equality of complexes, $r_Vu_*\lim J_Z=\lim u_*r_UJ_Z$:
$$\mathcal L(d_{u,Z})\lambda_{\mathscr
R_uZ}r_V(\kappa_u^a(Z))=\kappa_u^0(r_UZ)R_u^0(\lambda_Z)\chi_{u,\mathcal L^aZ}.$$ The
K-injective total-derived theorem identifies these models with the canonical derived functors.
This proves compatibility of the specified comparisons, not uniqueness from their finite
projections.

3. The diagram-site realization identifies strict towers with modules on one small ringed site,
with ring $\Delta A_T$. For this $J$, object $1$ is terminal, so
$\operatorname{colim}_J=\operatorname{ev}_1$ is exact. Its right adjoint $\Delta$ therefore
preserves K-injectives by the right-adjoint theorem. An ambient K-injective representative $I_K$
consequently computes $\mathscr R_f\Delta K=\Delta Rf_*K$ by the same complex $\Delta f_*I_K$;
the same argument applies to $f'$ and any ambient input $E$. A diagonal flat-term K-flat
representative is K-flat on the diagram site: its tensor with an acyclic diagram is acyclic at
every level, hence acyclic by levelwise cohomology. Existence of the ambient representative and
the derived tensor comparison are supplied by the K-flat resolution and tensor-descent nodes. On
these representatives the diagonal adjunction bijections are the componentwise ordinary ones.
The characterization of the derived bijection on fraction representatives therefore identifies
diagonal units and counits with the ambient ones. Pullback composition is termwise as well. By
the mate's transpose formula the diagram exchange on $\Delta K$ is $\Delta e$. This comparison
uses no properness or finite-origin witnesses.

4. On the diagram site, the constant-completion equivalence applies to $\Delta\underline
A_T\to\Delta A_T$: constant sheaves and limits are fiberwise under the diagram-site equivalence.
Apply its finite-reduction comparison to $\Delta K$. The strict tensor construction gives
$$\rho_K:r_X\mathcal R_X^aK\simeq\mathcal R_X\bar K.$$ On a flat-term K-flat representative $P$,
both sides are the SAME quotient diagram $(P/I^nP)_n$ with its quotient transitions; the map
sends the class of $p$ to itself. Thus it respects the quotient unit as well. The derived
tensor/pullback comparison and the coefficient identities identify $\mathcal R_U^aLu_a^*L$ with
$\mathscr L_u\mathcal R_V^aL$. Combining this with $p_u$ and the preceding balancing map gives
$\rho_{u,L}:r_U\mathscr L_u\mathcal R_V^aL\simeq G_u\mathcal R_Vr_VL$. These are strict-diagram
comparisons, natural in $L$. Define $$\beta=(G_gR_f^{\mathcal T}\rho_K)(G_gd_f)p_g,\qquad
\delta=(R_{f'}^{\mathcal T}G_{g'}\rho_K)(R_{f'}^{\mathcal T}p_{g'})d_{f'}.$$ Finally $\rho_M$ is
the same reduction comparison for $M$, followed by $\mathcal R(a_g)$ and $\mathcal
R(G_g\chi_f)$. These formulas give exactly the source, target and coefficient identifications
specified in (2).

5. Check the projection-formula equation by transposition, rather than by evaluations. On each
coefficient diagram the projection map is the adjunct of $(\varepsilon_{f,K}\otimes1)t_f$. The
adjunct clause of flat diagram restriction identifies its restricted adjunct with the adjunct of
its restricted transpose, and in particular identifies the restricted counit with the
constant-coefficient counit. Under $\rho$, the tensor factor in that transpose is a quotient: on
a K-flat representative the comparison is $p\otimes\bar a\mapsto p\otimes\bar a$, and the
pullback/tensor comparison sends it to $(p\otimes1)\otimes\bar a$. Applying a morphism $h$
before or after either map sends it to $(h(p)\otimes1)\otimes\bar a$. Use this with the counit
and the identified pullback. Hence the restricted transpose is exactly $(\varepsilon^0_{f,\bar
K}\otimes1)t_f^0$. Bijectivity of the adjunct correspondence identifies the two projection maps.
Apply $G_g$ and use the formulas for $\beta,\rho_M$ in Step 4 to obtain
$$\beta\,r(H^a)=H^0\rho_M.$$ This is an equality of derived diagram morphisms: the tensor
comparisons come from natural maps on the resolving class, and tensor descent makes their
equality an equality after localization. No general monoidal identification of the two ambient
scalar categories is used.

6. Let $W$ be the completed-coefficient strict-diagram exchange at $\mathcal R_X^aK$, defined by
its adjunction mate. Apply ringed exchange/tensor coherence on the completed ringed diagram
sites with object $\Delta K$ and coefficient object $Q_{Y,\bullet}=(\underline{P_n}_Y)_n$. This
theorem allows arbitrary ringed topoi and needs no properness. The coefficient isomorphisms give
$\mathscr L_uQ_{V,\bullet}\simeq Q_{U,\bullet}$, respecting the full quotient diagram and the
square. Step 3 identifies exchange at $\Delta K$ with $\Delta e$. Thus the first composite in
the coherence theorem is $WH^a$, while the second is $H'^a\mathcal R_{Y'}^a(e)$. Its stated
equality gives $$WH^a=H'^a\mathcal R_{Y'}^a(e),\qquad W=v^a.$$ Here right composition with the
specified inverse of $H^a$ gives the second equation. The inverses in the item exist: their
evaluations are perfect projection-formula isomorphisms; their cones have zero evaluated
cohomology and hence zero cohomology diagram. This uses conservativity for isomorphisms from
levelwise exactness, never faithfulness of evaluations on morphisms.

7. Before composing with $\rho_K$, let $b,d$ be the two composites of $p_u,d_u$ for the corners
at $r_X\mathcal R_X^aK$. Transpose $d\,r(W)b^{-1}$ under $G_{f'}\dashv R_{f'}^{\mathcal T}$. The
adjunct clause of flat diagram restriction replaces its counit by the constant-coefficient
counit. Pullback composition is also identified: its K-flat representative multiplies nested
extension scalars, and after restriction both routes are the same composite inverse-image
identification; the coefficient composition compatibility identifies their ring actions.
Consequently its transpose is $$G_{g'}\varepsilon_f^{\mathcal T}\circ\theta^{\mathcal
T}_{\square,R_f^{\mathcal T}r_X\mathcal R_X^aK}.$$ This is precisely the transpose defining
$E^{\mathcal T}_{r_X\mathcal R_X^aK}$. The adjunction bijection gives $d\,r(W)=E^{\mathcal T}b$.
Compose with $R_{f'}^{\mathcal T}G_{g'}\rho_K$ and use naturality of this mate for $\rho_K$;
with Step 6 and the definitions of $\beta,\delta$ this is $$\delta\,r(v^a)=E^{\mathcal
T}_{\mathcal R_X\bar K}\beta.$$ All equalities are in the derived strict-diagram category and
hold for every complete $K$.

8. Only now assume the additional properness and the levelwise etale-origin witnesses in the
strict-tower exchange normalization lemma. Its statement specifies $B_\bullet,D_\bullet$ as
precisely $B^a,D^a$ and $v'_\bullet=H'^a\mathcal R^a(e)(H^a)^{-1}=v^a$. Its $b,d$ are normalized
by the same restricted inverse images and the same K-injective direct images as Step 1.
Therefore the $\beta,\delta$ of Step 4 are those $b,d$ followed by the images of $\rho_K$. The
ordered completed base-change definition has source map $\mathcal L^a(H^a)r_S=s^a$, tower map
$v^a$, and target comparison $c^a$ with the same direction. Substitution gives exactly
$x^a_K=(c^a)^{-1}\mathcal L^a(v^a)s^a$. Since this expression was constructed before witnesses,
it is independent of which witnesses are supplied. No assertion of that lemma was applied to an
unwitnessed input.

9. We fix the completed comparison by its unit. Let $L$ be complete on $V$, and put
$j^a_{u,L}:Lu_a^*L\to F_u^aL$. By the completed-pullback definition and Koszul reconstruction,
this is quotient completion, with its canonical unit. The constant-completion equivalence
identifies this unit with the constant coefficient completion unit. With the strict
pullback/reduction comparison of Step 4 and $\lambda$ of Step 2, set $$\Psi_{u,L}=\mathcal
L(\rho_{u,L})\lambda\,r_U(r_{u,L}):r_UF_u^aL\longrightarrow\mathcal L G_u\mathcal
R_Vr_VL=F_u^0r_VL.$$ Here $r_{u,L}$ is the defining reconstruction into $\mathcal L^a\mathscr
L_u\mathcal R_V^aL$. All factors are isomorphisms. The two maps out of the uncompleted pullback
satisfy $$\Psi_{u,L}\,r_U(j^a_{u,L})=j^0_{u,r_VL}\,a_{u,L}.$$ Indeed they arise from the
identical strict map from the constant representative to its quotient diagram: Step 4 sends $p$
to its same class at every level WITH its transitions, and Step 2 takes the same limit after
restriction. Thus this is equality of induced completion-unit maps, not an argument from
evaluated equalities. The reflector node supplies bijectivity of precomposition with this unit
for maps into any complete object; Koszul reconstruction identifies its unit with the quotient
unit being used.

10. The unit identity in Step 9 identifies $\Psi_{u,L}$ with the stipulated $\phi_{u,L}$, as
follows. For complete $N$ on $U$, the two completed-adjunction Hom bijections first precompose
with $j^a_{u,L}$ or $j^0_{u,r_VL}$ and then use the ambient adjunction. Step 1's adjunct clause
says the second operations agree under $a_u,\chi_u$; Step 9's identity says the first operations
agree under $\Psi_u$. Equivalences on complete objects are fully faithful by constant-completion
equivalence. Hence $\Psi_u$ respects exactly these Hom bijections and is the isomorphism
defining $\phi_u$ in (1). Uniqueness also follows directly from the reflector's injective
precomposition map. Taking identities under these Hom bijections identifies the units and
counits. Direct image preserves completeness by the direct-image-limits node (and on the
constant side by completed-pullback-adjunction); thus the adjunctions are on the full complete
subcategories as required. Finally the explicit conjugate formula, using just the identified
units and counits, carries the specified direct-image composition and identity maps to their
corresponding completed pullback comparisons. This proves all of (1).

11. Apply $\Psi=\phi$ from Steps 9–10 to $(u,L)=(g',K)$. Its defining formula is precisely
$$\mathcal L(\rho_{g',K})\lambda\,r(r_{g',K})=r_{g',K}^0\phi_{g'}.$$ For the source apply it to
$(u,L)=(g,Rf_*K)$; this input is complete by direct-image-limits. Replace $r_YRf_*K$ by
$R_f^0\bar K$ through $\chi_f$. Naturality of the completion unit and of its strict quotient
diagram gives the comparison $F_g^0\chi_f$ on completed pullbacks and $\mathcal R(G_g\chi_f)$ on
the reduction diagram. By Step 4 their composite on the latter diagram is exactly $\rho_M$. With
the source reconstruction $r_S$ this yields $$\mathcal L(\rho_M)\lambda_{\mathcal
R^aM}\,r(r_S)=r_S^0(F_g^0\chi_f)\phi_g=r_S^0\iota_S.$$ For clarity the equality of these
extensions can be tested by precomposing with the completion unit, where both maps are the
strict quotient map followed by $G_g\chi_f$; injectivity of unit precomposition into a complete
target, supplied by the reflector, proves the equality. This derives both fixed reconstruction
equations in (3).

12. The source normalization now follows by functoriality. Since $s^a=\mathcal L^a(H^a)r_S$,
naturality of $\lambda$ and Step 5 give $$\begin{aligned} \mathcal L(\beta)\lambda_{B^a}r(s^a)
&=\mathcal L(\beta\,r(H^a))\lambda_{\mathcal R^aM}r(r_S)\\ &=\mathcal L(H^0)\mathcal
L(\rho_M)\lambda_{\mathcal R^aM}r(r_S)\\ &=\mathcal L(H^0)r_S^0\iota_S=s^0\iota_S.
\end{aligned}$$ The last equality uses exactly the definition of $s$ in
completion-mate-comparison, so an arbitrary source isomorphism has not been substituted.

13. For the target put $u=f'$ and $Z=\mathscr L_{g'}\mathcal R_X^aK$, and abbreviate
$\rho_{g',K}$ to $q$. The definitions give $$c^a=\kappa_u^a(Z)Ru_*(r_{g',K}),\quad
\delta=(R_u^{\mathcal T}q)d_{u,Z},\quad t^0=\kappa_u^0(G_{g'}\mathcal R_X\bar
K)R_u^0(r_{g',K}^0).$$ Use the comparison square of Step 2, followed by naturality of
$\kappa_u^0$ for $q$ and of $\chi_u$ for $r_{g',K}$. It gives, in the written order,
$$\begin{aligned} \mathcal L(\delta)\lambda_{D^a}r(c^a) &=\kappa_u^0(G_{g'}\mathcal R_X\bar K)\,
R_u^0\bigl(\mathcal L(q)\lambda_Zr(r_{g',K})\bigr)\chi_{u,F_{g'}^aK}\\
&=\kappa_u^0(G_{g'}\mathcal R_X\bar K)R_u^0(r_{g',K}^0\phi_{g'})\chi_{u,F_{g'}^aK}\\
&=t^0(R_u^0\phi_{g'})\chi_{u,F_{g'}^aK}=t^0\iota_T. \end{aligned}$$ The second equality is the
target reconstruction identity of Step 11. The direct-image-limits statement and
completion-mate-comparison specify their $c^a,t^0$ by the K-injective direct-image/limit
comparison used in Step 2. Thus this calculation proves compatibility of those specified
comparisons, including $\chi,\lambda,\delta$, rather than assuming a finite-reduction
normalization.

14. Apply $\mathcal L$ to Step 7 and use naturality of $\lambda$. Substitute the source and
target normalizations of Steps 12–13 into $x_K^a=(c^a)^{-1}\mathcal L^a(v^a)s^a$ and cancel the
isomorphisms in order: $$\begin{aligned} \iota_Tr(x_K^a) &=(t^0)^{-1}\mathcal
L(\delta)\lambda_{D^a}\,r(\mathcal L^a(v^a))r(s^a)\\ &=(t^0)^{-1}\mathcal
L(\delta\,r(v^a))\lambda_{B^a}r(s^a)\\ &=(t^0)^{-1}\mathcal L(E^{\mathcal T})\mathcal
L(\beta)\lambda_{B^a}r(s^a)\\ &=(t^0)^{-1}\mathcal L(E^{\mathcal T})s^0\iota_S. \end{aligned}$$
All transformations in the construction are natural: the scalar and finite-reduction
comparisons, the adjuncts, completion units, and the K-injective limit comparisons. The
displayed derivations are operations on those transformations, hence hold naturally for every
morphism of complete $K$. Completed pullback lands in the complete category by its reflector
description, and direct image preserves that category; the same proof therefore applies to those
intermediate complete inputs. Completion-mate-comparison identifies the right-hand expression
with the completed constant-coefficient mate; its Noetherian and perfect-quotient hypotheses are
those of the datum. No identity-square or pasting law is used.
-/
theorem coefficientComparison (sq : ChosenCartesianSquare g' f' f g) :
    (∀ (K : d.derived X) (hK : d.TowerComplete X K),
      (d.towerV' sq K =
        (exchangeRealizationH (f := f) (g := g) d K).inv ≫
          (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
      ((exchangeTowerRes d Y').map
          (exchangeRealizationH (f := f) (g := g) d K).hom ≫
            (beta (f := f) (g := g) d K).hom =
        (rhoM (f := f) (g := g) d K).hom ≫
          (H (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((exchangeTowerRes d Y').map (d.towerV' sq K) ≫
          (delta (f' := f') (g' := g') d K).hom =
        (beta (f := f) (g := g) d K).hom ≫
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
            ((reduction d X).obj ((res d X).obj K))) ∧
      ((res d Y').map (sourceReconstruction (f := f) (g := g) d K).hom ≫
          (lambda d Y').hom.app
            ((completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K))) ≫
          (rlim (A := A) Y').map (rhoM (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom) ∧
      ((lambda d X').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
          (rlim (A := A) X').map (rhoPull (g' := g') d K).hom =
        (phi d g').hom.app ⟨K, hK⟩ ≫
          (reconstruction d g' ((res d X).obj K)).hom) ∧
      ((res d Y').map (sourceA (f := f) (f' := f') (g := g) (g' := g') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (beta (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom ≫
          (S (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((res d Y').map (targetA (g' := g') (f' := f') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K).hom =
        (iotaT (f' := f') (g' := g') d K hK).hom ≫
          (T (f' := f') (g' := g') d ((res d X).obj K)).hom)) ∧
    rawNormalized d sq = constantNormalized d sq ∧
    (∀ [IsProper f] (K : d.derived X) (hK : d.TowerComplete X K)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj K)),
      d.completedExchange sq K = d.completedBaseChangeMap sq K hK W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨h₁, h₂, h₃⟩ := strictCoefficientEquations d sq K hK
    obtain ⟨h₄, h₅, h₆, h₇⟩ := reconstructionCoefficientEquations d sq K hK
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  · apply NatTrans.ext
    funext K
    exact rawCoefficientEquation d sq K
  · intro _ K hK W
    rfl

end AlgebraicGeometry.Scheme.OrderedExchange
