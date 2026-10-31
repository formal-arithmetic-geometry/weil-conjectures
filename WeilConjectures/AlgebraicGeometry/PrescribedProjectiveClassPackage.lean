/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerP1Data
public import WeilConjectures.AlgebraicGeometry.TowerClassTensorPullback

/-! # Prescribed projective class package

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-classes.proof.md`,
clauses (1)--(4) (blueprint: lem-sp-prescribed-projective-class-package).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.SpTowerClasses

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The supplied base, geometric adjunction data and normalized tensor data admit the
prescribed Kummer, diagonal and projective-line class package.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-classes.proof.md`,
clauses (1)--(4) (blueprint: lem-sp-prescribed-projective-class-package).

Proof plan from the DAG:

1. Work throughout in the ringed inverse-system topos, with index $n$ denoting exponent $n+1$.
   On a pro-etale object $U$ of any of $S,P,W$, the etale Kummer lemma on $U$ makes $u\mapsto
   u^{\ell^{n+1}}$ locally surjective. An etale cover of $U$ is a pro-etale cover. Its kernel is
   the actual roots sheaf. Componentwise exactness and $(u^\ell)^{\ell^{n+1}}=u^{\ell^{n+2}}$
   give the short exact sequence of the literal roots, power-unit and constant-unit systems.
   This constructs the Kummer records; it does not apply a theorem already assuming those
   records.

2. Fix a line bundle $L$ on $T=S,P,W$. For frames $e_b=g_{ab}e_a$, glue $G_m\times\mathbf Z$ by
   $(u,m)_b\mapsto(g_{ab}^m u,m)_a$. The cocycle identity gives an extension $0\to G_m\to
   E_L\to\mathbf Z\to0$, with the fibre over $1$ the frame torsor of $L$. The torsor/H1 and
   line-bundle/torsor statements identify its extension class with that of $L$, rather than
   $L^{-1}$. Start with this extension on the etale site, apply exact comparison inverse image
   and the full-units comparison, and take constant systems, as prescribed in the reduction
   definition. The displayed gluing describes the resulting full-units extension. Exact-functor
   compatibility of Ext1 supplies its actual derived arrow $\lambda_L:\mathbf Z_\bullet\to
   G_m^{const}[1]$.

3. On the same inverse-system topos form the ordinary adjunction $R_\bullet\otimes_{\mathbf
   Z_\bullet}-\dashv\operatorname{Res}$ and its total left derivation $T_R$. Forgetting modules
   retains the literal sections, actions and horizontal transitions. The derived change-of-rings
   and derived scalar-adjunction statements supply the universal K-flat model, adjunction and
   its representative transpose equation. For a flat-term K-flat resolution $Q\to K$ on the
   original site, constant inverse image preserves this resolution;
   $R_\bullet\otimes\operatorname{const}(Q)$ computes all finite evaluations with the actual
   quotient transitions. This constructs Reduction, including the representative normalization,
   on each of $S,P,W$; it has no dependence on an independently chosen geometric adjunction.

4. Compute the underlying reduction of $G_m^{const}$ with $Q_n=[\mathbf
   Z\xrightarrow{\ell^{n+1}}\mathbf Z]$ in degrees $-1,0$, transition $(\ell,1)$. Both terms are
   flat systems, and tensoring this bounded complex with an acyclic complex is the cone of a map
   between acyclic complexes, so it is K-flat. Its tensor with $G_m^{const}$ is the Kummer
   two-term complex and has just roots in degree $-1$. Truncation in the module derived category
   gives $T_R(G_m^{const})\simeq\mu_\bullet[1]$. Identify its cohomology module by the unique
   residue action (multiplication by integer representatives). The positive kernel inclusion
   fixes the underlying identification; its shift fixes
   $T_R(G_m^{const}[1])\simeq\mu_\bullet[2]$. Also $T_R(\mathbf Z_\bullet)=R_\bullet$ with
   quotient generator.

5. Verify the target normalization on entire abelian systems. For the Kummer sequence $0\to
   U\xrightarrow{i}M\xrightarrow{f}N\to0$, put $C=[U\to M]$, $D=[M\to N]$, and let $v:C\simeq
   N$, $p:C\to U[1]$, $a:N\to D$ and $j:U[1]\simeq D$ be the quotient, positive projection,
   degree-zero inclusion and positive kernel. The standard boundary is $-pv^{-1}$. The map
   $av+jp$ is nullhomotopic by $h^0=1_M$, since $dh+hd$ has components $i,f$. Hence
   $j^{-1}a=-pv^{-1}$. In the preceding model $a$ is the scalar-insertion unit. After shifting
   this is exactly the target-adjunction normalization, with positive Kummer boundary; the
   homotopy respects the power transitions. The source normalization is the tensor unit on the
   integral generator.

6. Derive the canonical ring-system map $R_\bullet\to A_\bullet$ by the published K-flat scalar
   model. Its unit comparison transposes to the actual unital quotient, since the insertion
   $x\mapsto1\otimes x$ on representatives does so. Apply it to $T_R(\lambda_L)$. The
   compatible-root cover supplies generators $\zeta_{n+1}^\ell=\zeta_n$ on one pro-etale cover;
   there the root module is literally $R_\bullet$, and its ordinary scalar extension is
   $A_\bullet$. Thus the universal derived-to-ordinary comparison on the root module is
   invertible and sends each $a\otimes z$ to that identical tensor. These choices give Chern
   data with all three normalization equations and the precise positive Tate line of its
   definition.

7. Naturality of the reduction/scalar units gives, before any evaluation, that scalar-forgetting
   $c_1(L)$ and precomposing the integer quotient equals $\lambda_L$ followed by the positive
   Kummer boundary and the root inclusion $z\mapsto1\otimes z$. The preceding homotopy
   identifies that boundary on entire systems. Evaluation is exact and commutes with the K-flat
   scalar models, so the same equation is the required finite Chern normalization on $S,P,W$. At
   each positive exponent, the divisible-extension reduction lemma gives the identical
   normalization: its hypotheses hold because the power map on units is epi and multiplication
   on $\mathbf Z$ is mono. This also identifies the evaluated class with the comparison pullback
   of the ordinary etale Kummer class.

8. For $T=S,P$, take as positive ordinary functor tensor with the constructed line module and as
   inverse the sheaf internal Hom from that line. Use exactly $x\mapsto(y\mapsto x\otimes y)$
   and $f\otimes y\mapsto f(y)$ for coevaluation and evaluation. On the compatible-generator
   cover both composites are identity scalar multiplication, so these are isomorphisms of
   sheaves and satisfy the triangle equations. The same local description proves additivity and
   exactness of both functors; it also gives the unit map $a\otimes y\mapsto ay$. Localizing
   these exact functors gives the stipulated ordinary unbounded positive/negative twists. This
   verifies the fields of Twisting rather than choosing an arbitrary equivalence.

9. On an affine base $\operatorname{Spec}B\subset S$, the four standard charts of $W$ have rings
   $B[x,y]$. The diagonal equations are $x-y$ or $xy-1$. The first is monic; for the second,
   $(xy-1)\sum f_k(y)x^k=0$ gives successively $f_0=0$, $f_k=yf_{k-1}=0$. Thus these equations
   are regular even over a nonreduced base. This proves the Cartier hypothesis and identifies
   the divisor line with the dual diagonal ideal. Use the etale pole extension pulled to the
   pro-etale site from the diagonal-system statement, with quotient $t^{-1}\mapsto+1$. Its
   kernel is the pulled etale units $B_0$, and the canonical map $a:B_0\to G_m$ gives the signed
   boundary $\beta=a[1](-pv^{-1})$.

10. Let $\rho:\mathbf Z_W\to\Delta_*\mathbf Z_P$ be the supported integral unit. On equations
   $t_b=g_{ab}^{-1}t_a$, the lifts $t_a^{-1}$ have transition ratio $g_{ab}$. The pullback pole
   extension along $\rho$ is therefore glued by $(b,m)_b\mapsto(g_{ab}^m b,m)_a$. The maps
   $(b,m)\mapsto(a(b),m)$ identify its image in full units with the frame extension of $\mathcal
   O_W(\Delta)$ above: a section over $m$ differs from $t_a^{-m}$ by exactly one kernel section.
   Naturality of the extension boundary gives $\beta\rho=\lambda_{\mathcal O_W(\Delta)}$. Apply
   the same two scalar functors and the same target comparison as for Chern classes; this
   constructs the supported map on whole systems and proves the forget-support equality prior to
   evaluation.

11. The supported integral source $F=\Delta_*\mathbf Z_P$ is torsion-free: multiplication by
   every positive integer is injective sectionwise. Tensoring its constant tower with
   $Q_\bullet$ therefore reduces it to $\Delta_*R_\bullet$, via the literal quotient. This is
   also the source comparison in the diagonal-system statement. A fixed integral basis for
   $\mathcal O_E$ over $\mathbf Z_\ell$ reduces to compatible bases of $A_n$ over $R_n$, so
   $A_\bullet$ is finite free as an $R_\bullet$-module. Consequently extension of this supported
   source is exactly $\Delta_*A_\bullet$; on the chosen finite basis the canonical tensor/push
   map is the identity on a finite sum of copies. The comparison sends the reduced integral
   supported unit to the section $1$ on each pulled-back chart.

12. Identify this supported source with the supplied $g_\Delta$ direct image as follows. At the
   ordinary module level, transpose the constant-coefficient restriction under $g_\Delta$'s
   recorded adjunction, using its supplied CoefficientPullback. Its finite sections are the
   residue-multiple-of-one map, by that record's normalization and the canonical finite
   adjunction package in Geometry. The OrdinaryUnitTransition equation makes these finite
   adjuncts commute with every horizontal quotient map, so they define an actual map of ordinary
   systems to $g_\Delta.push(A_P)$. In the recorded ordinaryPushEvaluation coordinates it is the
   identity supported-coefficient comparison at every level, hence an isomorphism by
   componentwise exactness. Closed pushforward is exact (the Cartier complement is quasi-compact
   on the Noetherian $W$), so its localization and the canonical right-derived comparison give
   sourceIso for precisely $g_\Delta$. The same ordinary transpose calculation sends the scalar
   extension of $\rho$ to unitArrow of its supplied CoefficientPullback, proving the required
   source normalization on whole systems.

13. Apply the Cartier reduction/site comparison with $Z=W,D=\Delta,r=n+1,R=\mathbf Z/\ell^{n+1}$
   and $\Lambda=A_n$. These are finite commutative coefficients killed by that exponent;
   ramification changes neither the exponent nor the unital quotient. The lemma identifies the
   entire supported finite morphism under the canonical quotient-source and roots-target
   comparisons, including the supported restriction unit and positive sign. Those are exactly
   the comparisons constructed above. Scalar-unit naturality then gives the finite supported
   integer-quotient equation required by finite diagonal normalization. This proves the diagonal
   field and its finite normalizations without inferring equality of supported maps from
   equality after forgetting support.

14. Apply the line-pullback existence statement to $g_q$, its supplied CoefficientPullback and
   TensorPullback, and the normalized Chern data just constructed on $S,P$. Its sole
   invertibility hypothesis is satisfied since $\ell$ is invertible on $S$. It supplies
   LinePullback whose ordinary adjoint is coefficient restriction tensored with the actual root
   restriction. Compose the supplied ordinary tensor inverse-image comparison (at the root line)
   with this line isomorphism to obtain PositivePullback for the exact tensor twists. Its finite
   pure tensor goes to the tensor of the two ordinary adjunction units: this follows directly by
   substitution of the two supplied normalization formulas, with the second factor the root
   restriction. Hence this is the precise PositivePullback of the twisting definition for $g_q$.

15. The specified line projection mate is invertible. Write $L=g_q.pull$ and $G=Rg_q.push$ with
   the derived adjunction $L\dashv G$ recorded in $g_q$ [def-sp-tower-shriek-data], and $T_S,T_P$
   for the positive derived twists of the twisting records; both are equivalences, with the
   internal-Hom twists as inverses. The PositivePullback of step 14 is a natural isomorphism
   $\theta:LT_S\xrightarrow{\sim}T_PL$, and by the twisting definition the specified projection
   arrow is its counit mate $\alpha:T_SG\xrightarrow{\eta T_SG}GLT_SG\xrightarrow{G\theta
   G}GT_PLG\xrightarrow{GT_P\varepsilon}GT_P$, both adjunctions being $L\dashv G$. Apply invariance
   of mates under equivalences [lem-weil-mate-iso-along-equivalences] with $\mathcal C=\mathcal
   C'=D(S)$, $\mathcal D=\mathcal D'=D(P)$, both adjunctions $L\dashv G$, $G_{\mathrm{lemma}}=T_S$
   (an equivalence) and $G'_{\mathrm{lemma}}=T_P$ (fully faithful, being an equivalence): $\alpha$
   is a natural isomorphism. Concretely its inverse is read off from the natural bijections
   $\operatorname{Hom}(M,T_SGC)\cong\operatorname{Hom}(T_S^{-1}M,GC)\cong
   \operatorname{Hom}(LT_S^{-1}M,C)\cong\operatorname{Hom}(T_P^{-1}LM,C)\cong
   \operatorname{Hom}(LM,T_PC)\cong\operatorname{Hom}(M,GT_PC)$,
   the third using $\theta$ conjugated by the twist equivalences; the forward composite is
   $\alpha_C\circ-$ by the triangle identities and the line evaluation/coevaluation. No separately
   chosen projection map occurs, and the supplied TensorData ensure that all tensor identifications
   use $b.calculus$ through closed_eq.

16. Use this projection isomorphism to form the Projective record with geometry literally $g_q$.
   The first biproduct arrow is its coefficient unitArrow. For the second, adjoint $c_1(\mathcal
   O_P(1))$, apply the inverse specified projection, then the negative twist and shift by $-2$,
   with the unit/evaluation contractions just constructed. Thus $b_q$ is an actual morphism on
   whole systems before evaluation. The hyperplane line here is the specified relative
   projective twist, not its dual. The section-normalized geometric evaluation theorem carries
   this construction, its adjunction transposes and its contractions to exactly the finite
   unit/hyperplane map in the supplied finite adjunction coordinates.

17. For comparison with the finite projective splitting, the integral frame extension on the
   etale site pulls to the extension with kernel $B_0=\nu^{-1}G_{m,et}$, and
   $(b,m)\mapsto(a(b),m)$ carries it to the full-units extension fixing $\mathbf Z$. Both
   kernels have surjective $\ell^{n+1}$-power maps by Kummer exactness, and $\mathbf Z$ is
   torsion-free. Naturality of the divisible-extension reduction statement for this morphism and
   exact $\nu^{-1}$ identifies the reduced Chern classes. The roots comparison
   $\nu^{-1}\mu_{\ell^{n+1},\mathrm{et}}\to\mu_{\ell^{n+1}}$ is an isomorphism: by
   [lem-cbc-comparison-pullback-sections] its value on a pro-etale object $f:Y\to T$ is
   $\Gamma(Y_{\mathrm{et}},f_{\mathrm{et}}^{-1}\mu_{\ell^{n+1},T})$, and
   [lem-asd-etale-finite-twist-pullback] (with $A=\mathbf Z/\ell^{n+1}$, invertible exponent)
   identifies $f_{\mathrm{et}}^{-1}\mu_{\ell^{n+1},T}$ with $\mu_{\ell^{n+1},Y}$ by the
   inverse-image comparison of roots, whose global sections are the roots of unity of
   $\Gamma(Y,\mathcal O_Y)$; on an etale cover with a primitive root it is the identity on the
   cyclic generator. Thus the evaluated R-coefficient Chern arrow is exactly the
   comparison-pulled etale Kummer arrow in the finite trace proposition, with its positive sign.

18. Apply clause (1) of the pro-etale finite projective-line trace proposition at exponent
   $n+1$. Its Noetherian hypothesis is precisely the finite affine Noetherian cover assumed for
   $S$, and $\ell$ is invertible. It says the actual R-coefficient unit/hyperplane map is an
   isomorphism. In the fixed integral basis, restriction of our A-coefficient map to
   R-coefficients is its finite direct sum: scalar-unit and Chern formulas act on each basis
   vector separately. Derived direct-image composition with exact scalar restriction identifies
   the two pushforwards, and additive direct image preserves finite sums. Restriction retains
   the underlying cohomology sheaves, so reflects isomorphisms. Hence each finite evaluation of
   $b_q$ is invertible; joint conservativity of exact evaluation now makes this already
   constructed whole-system $b_q$ invertible.

19. Twist and shift this $b_q$ and compose with its specified projection isomorphism, giving
   $B:A_S(1)[2]\oplus A_S\simeq Rq_*A_P(1)[2]$. Its two components are exactly twistedUnit and
   the adjoint hyperplane Chern arrow, by the way the second arrow was defined and by the
   adjunction triangle and line contraction identities. Define the trace literally as
   $\operatorname{pr}_2 B^{-1}$, equivalently the inverse-twist/shift formula of the projective
   definition. The composites with these components are
   $\operatorname{pr}_2\operatorname{in}_1=0$ and $\operatorname{pr}_2\operatorname{in}_2=1$ on
   whole systems. Exact evaluation carries these equations to trace_unit and trace_chern at
   every level. No equality of arbitrary derived maps is deduced solely from finite evaluations.

20. Assemble the fields of TowerClasses: base $b$; the three normalized Chern data and their
   finite normalizations; the tensor/Hom twists on $S,P$; the supported diagonal with geometry
   $g_\Delta$ and finite normalization; and the projective record with geometry $g_q$, $b_q$
   invertible and the two evaluated trace identities. The base and geometry equations hold by
   construction (or their equality transports). The auxiliary TensorData were used only for
   these same fixed b-calculi. No projective adjunction, identity comparison or
   second-projection LinePullback is a required field, and none was constructed or assumed. -/
theorem exists_prescribedProjectiveClassPackage
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤)))
    (b : SpTowerShriek.Base l E)
    (g_q : SpTowerShriek.Geometry l E b (ProjectiveLine S ↘ S))
    (g_Δ : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (tensorS : SpTowerP1.TensorData l E b S)
    (tensorP : SpTowerP1.TensorData l E b (ProjectiveLine S))
    (tensorW : SpTowerP1.TensorData l E b (diagonalSurface S))
    (coefficientPullback_q : SpTowerClasses.CoefficientPullback l E b
      (ProjectiveLine S ↘ S) g_q)
    (coefficientPullback_Δ : SpTowerClasses.CoefficientPullback l E b
      (diagonalImmersion S) g_Δ)
    (tensorPullback_q : SpTowerClasses.TensorPullback l E
      (ProjectiveLine S ↘ S) g_q) :
    ∃ C : TowerClasses l E S hS,
      C.base = b ∧ HEq C.projective.geometry g_q ∧ HEq C.diagonal.geometry g_Δ := by
  sorry

end AlgebraicGeometry.ProEtale
