/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q21, N8
-/
module

public import Sheaf.Paper.PurityDiagonalSectionPastingData
import Sheaf.Paper.PurityDiagonalGlobalEquation
import Sheaf.Paper.PurityDiagonalOpenRestriction
import Sheaf.Paper.PurityDiagonalAffineChartEquation

/-! # Assembly of diagonal section pasting

The shared constructions are publicly re-exported from PurityDiagonalSectionPastingData.
The global, open-restriction and affine-chart clauses are assembled below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

/-- Pasting of the orientation-free diagonal section comparison, with its open
restriction and precise ordered difference-coordinate clauses.
Source: blueprint main-20261015, thm-pur-composition-coherence proof Step 1
(blueprint: lem-pur-diagonal-section-pasting).

The following is the complete twelve-step proof recorded on the DAG node. The
re-exported definitions use exactly its mates, coordinate differences and
pullback comparisons, in the canonical finite pro-etale presentation.

Proof step 1. Write $r:Q\to Y$ and $l:W\to X$ for the second projections. The universal property
[def-pc-fibre-product] gives the commutative diagram with rows $W\xrightarrow aQ\xrightarrow bX$
and $X\xrightarrow fY\xrightarrow gZ$, and vertical arrows $l,r,gf$. Its two squares are
Cartesian: $W=Q\times_YX$ and $Q=X\times_ZY$. Its outer rectangle is the base-change square for
$gf$, with $ba=p_{gf}$. Evaluation on pairs gives $at=s$, $lt=1_X$, and $rs=f$. Base-change and
composition permanence [lem-sbc-smooth-relative-dimension-permanence,
lem-pod-separated-finite-type-base-change] give the smooth separated finite-type maps $a,b,ba$ of
dimensions $d,e,d+e$. These are the actual two squares used below; no square involving a
composition isomorphism is regarded as a square of schemes.

Proof step 2. Use $B_{h,v,N}:Lu^*Rh^!N\to Rh'^!Lv^*N$ for the transpose of
$Lv^*\varepsilon_{h,N}\circ\operatorname{Ex}_!^{-1}$ for a Cartesian square $(h,h',v,u)$; its unit
specialization is exactly $\beta_{h,v}$ of [def-pur-co-smoothness]. The horizontal law of
[fix-lem-exchanges](2), inverted and followed by the pulled-back counit, gives transitivity of $B$
for successive base changes. The vertical law in the same clause, with compact-support composition
[thm-sf-comp-composition], gives
$$c_{b,a,L(gf)^*N}\circ B_{gf,gf,N}=Ra^!(B_{g,gf,N})\circ
B_{f,r,Rg^!N}\circ Ll^*c_{g,f,N}.$$ This follows by taking the mates of the two sides of that
vertical exchange equation, using [lem-weil-pbc-mate-pasting](2) and the composite counit
[def-weil-pbc-composite-adjunction]; conjugation reverses composition as in
[def-weil-pbc-adjunction-conjugate]. Thus the geometric exchange equations, as well as the formal
mate law, are used.

Proof step 3. The tensor and base-change clauses (1),(3) of [thm-pur-cohomological-smoothness]
make every displayed $\theta$ and smooth $B$ invertible, and identify
$B_{f,r,N}\,Ll^*\theta_{f,N}$ with $\theta_{a,Lr^*N}(1\otimes\beta_{f,r})$. Set
$$A=\beta_{f,r}:Ll^*\omega_f\to\omega_a,\quad B=\beta_{g,gf}:Lr^*\omega_g\to\omega_b,\quad
D=\beta_{gf,gf}:Ll^*\omega_{gf}\to\omega_{ba}.$$
Apply the vertical identity of Step 2 at
$N=\Lambda$, substitute this tensor compatibility at $N=\omega_g$, and invert $c_{b,a}$.
Naturality of $\theta_a$ in $B$ gives exactly
$$D\,Ll^*\sigma_{f,g}=\sigma_{a,b}(A\otimes
La^*B).\tag{*}$$
All pullback composition in this formula is supplied by
[lem-weil-pbc-proetale-derived-pullback-composition];
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] supplies its tensor comparison. Their
reassociations agree termwise on K-flat flat-term models: both orders send a pure tensor to the
same pulled-back tensor, and both composite pullbacks are the termwise canonical module
comparison. This also fixes all suppressed associators.

Proof step 4. Let $i:W_f\to W$ send $(x,x')$ with $f(x)=f(x')$ to the same pair. Then
$(W_f\xrightarrow iW, X\xrightarrow sQ)$ is the base-change square of $a$, and $i\Delta_f=t$. Let
$j:Q\to W_g$ send $(x,y)$ to $(f(x),y)$; then $(Q\xrightarrow jW_g,X\xrightarrow fY)$ is the
base-change square of $p_g$, and $js=\Delta_gf$. Put $F=\beta_{a,s}:Li^*\omega_a\to\omega_{p_f}$
and $G=\beta_{p_g,f}:Lj^*\omega_{p_g}\to\omega_b$. The comparisons in the statement are
$$\gamma_f=L\Delta_f^*F^{-1}:C_f\to Lt^*\omega_a,\qquad\gamma_g=Ls^*G:Lf^*C_g\to Ls^*\omega_b.$$
Horizontal transitivity from Step 2, applied respectively to the squares for $(f,r)$ then $(a,s)$
and for $(g,g)$ then $(p_g,f)$, gives
$$\alpha_f=(Lt^*A)^{-1}\gamma_f,\quad
Lf^*\alpha_g=(Ls^*B)^{-1}\gamma_g,\quad\alpha_{gf}=(Lt^*D)^{-1}.$$
The last formula is precisely
[lem-pur-diagonal-base-change] for $gf$ since $lt=1$. The same lemma identifies the first two with
the specified $\alpha$, rather than unspecified isomorphisms. Use
[lem-weil-pbc-proetale-derived-pullback-composition] throughout to identify the composed
pullbacks.

Proof step 5. The invertibility in [thm-pur-cohomological-smoothness] and adjunction conjugation
[def-weil-pbc-adjunction-conjugate] of [thm-sf-comp-composition] show that each $\sigma$ is an
isomorphism. The tensor pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback],
$at=s$, and derived pullback composition [lem-weil-pbc-proetale-derived-pullback-composition] make
$\kappa$ exactly $Lt^*\sigma_{a,b}\circ(\gamma_f\otimes\gamma_g)$. Pull (*) back along $t$,
precompose with $\gamma_f\otimes\gamma_g$, and multiply by $(Lt^*D)^{-1}$. The three substitutions
of Step 4 give
$$\alpha_{gf}\kappa=\sigma_{f,g}(\alpha_f\otimes Lf^*\alpha_g).$$
This is a
calculation with the specified maps, requiring both exchange pasting and base-change compatibility
of the tensor map.

Proof step 6. We will also use the cocycle equation
$$\sigma_{vu,w}(\sigma_{u,v}\otimes1)=\sigma_{u,wv}(1\otimes Lu^*\sigma_{v,w}).\tag{**}$$
This is
the tensor-formula composition clause (4) of [thm-pur-cohomological-smoothness] evaluated at
$\omega_w$, followed by the inverse exceptional composition comparison: substitute
$\sigma_{u,v}=c_{v,u}^{-1}\theta_{u,\omega_v}\mathrm{sym}$ on both sides. Naturality moves
$c_{w,v}^{-1}$ through $\theta_u$; clause (4) replaces $\theta_u\circ Lu^*\theta_v$ with the
composite tensor map; the two remaining $c$ composites agree because [thm-sf-comp-composition] is
associative and conjugation [def-weil-pbc-adjunction-conjugate] reverses the same associative
equation. Thus (**) uses the specified $\theta$, not the unspecified isomorphism of the
co-smooth-composition lemma. For an etale $u$,
[lem-pur-finite-etale-dualizing-normalization](1),(3) say $\sigma_{u,v}^{-1}=E_{u,v}$ after
removing $\omega_u$ with $\eta_u$. In particular (**) gives
$$E_{u,wv}\sigma_{vu,w}=Lu^*\sigma_{v,w}(E_{u,v}\otimes1).\tag{***}$$

Proof step 7. Target-open restrictions are Cartesian base changes, so Steps 2-3 and
[fix-lem-exchanges](1),(2) identify every restricted $\beta$ and $\sigma$ with the corresponding
map on the target open. A further source-open immersion $u$ uses the normalized etale comparison
$E_{u,h}$ of [lem-pur-finite-etale-dualizing-normalization], rather than a falsely asserted
Cartesian square. Its compatibility with $\sigma$ is (***); its compatibility with the Cartesian
base-change maps is Step 2 with the etale normalization of that lemma. Restricting the diagonal
pair amounts to restricting both factors, and its diagonal factors through that restriction. Hence
applying the derived pullback comparison [lem-weil-pbc-proetale-derived-pullback-composition] and
the tensor comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the formulas for
$\gamma_f,\gamma_g,\kappa$ proves precisely their asserted compatibility with arbitrary compatible
source and target open restrictions.

Proof step 8. For the base $B$ of the statement, [def-sbc-affine-space] and
[sbc-lem-affine-space-smooth] give the smooth tower $\mathbf A_B^{d+e}\xrightarrow q\mathbf
A_B^e\xrightarrow{P_e}B$. The square with top $\mathbf A_B^{d+e}\to\mathbf A_B^d$ and bottom $P_e$
is Cartesian and $q$ is the pullback of $P_d$. Its $\beta$ gives $Lz_{d+e}^*\omega_q\cong
Lz_d^*\omega_{P_d}=D_d$, while $qz_{d+e}=z_e$ gives $Lz_{d+e}^*Lq^*\omega_{P_e}=D_e$ by
[lem-weil-pbc-proetale-derived-pullback-composition]. Thus the tensor comparison
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and $Lz_{d+e}^*\sigma_{q,P_e}$ give the stated
$\nu_{d,e}$. Its definition uses no trivialization of any dualizing object.

Proof step 9. By Step 7 work on the stated charts and replace $(X,Y,Z)$ by $(U,V,T)$, putting
$B=U$. Write $x=(x_1,\ldots,x_d)$ for the chart coordinates of $U\to\mathbf A^d_V$ and
$y=(y_1,\ldots,y_e)$ for those of $V\to\mathbf A^e_T$. With $Q=U\times_TV$ and $W=U\times_TU$,
define
$$G:Q\to\mathbf A_B^e,\quad(u,v)\mapsto y(v)-y(fu).$$
Put $R=Q\times_{\mathbf A_B^e}\mathbf
A_B^{d+e}=\mathbf A_Q^d$ with projections $q_Q:R\to Q$, $J:R\to\mathbf A_B^{d+e}$. Define
$$H:W\to
R,\quad(u,u')\mapsto((u,fu'),x(u')-x(u)).$$
Then $a=q_QH$, $b=P_eG$, $qJ=Gq_Q$, and $F=JH$ has the
ordered difference coordinates $(x(u')-x(u),y(fu')-y(fu))$. These formulas follow from
[def-pc-fibre-product, def-sbc-affine-space]. $G$ is the base change of the chart of $g$, followed
by translation by $-y(fu)$; $H$ is the base change of the chart of $f$, followed by translation by
$-x(u)$. They are etale by [lem-weil-pbc-etale-ring-base-change]; translation is an isomorphism
with inverse addition of the same coordinates. Likewise $J$ is etale as a base change of $G$. All
these schemes are affine, so that cited affine ring-base-change statement applies, and all maps
are separated finite type. Crucially the square $(W\xrightarrow F\mathbf A_B^{d+e},Q\xrightarrow
G\mathbf A_B^e)$ need not be Cartesian; the square defining $R$ is Cartesian. The sections satisfy
$Gs=z_e$ and $Ft=z_{d+e}$.

Proof step 10. Write $E$ for the normalized comparisons of
[lem-pur-finite-etale-dualizing-normalization]. For the Cartesian square defining $R$, its clause
(3) gives
$$E_{J,q}\sigma_{q_Q,G}=\beta_{q,G}^{-1},\tag{a}$$
after identifying $\omega_G$ with the
unit. Apply (**) to $(q_Q,G,P_e)$ and (***) to $(J,q,P_e)$. Substitute (a) and
$\sigma_{G,P_e}^{-1}=E_{G,P_e}$. Cancellation of the invertible $\sigma_{q_Q,G}$ gives the typed
identity
$$E_{J,P_eq}\sigma_{q_Q,b}=LJ^*\sigma_{q,P_e}\bigl(\beta_{q,G}^{-1}\otimes
Lq_Q^*E_{G,P_e}\bigr).\tag{b}$$
Both sides have domain $\omega_{q_Q}\otimes Lq_Q^*\omega_b$ and
target $LJ^*\omega_{P_eq}$. Now apply (***) with $(H,q_Q,b)$, then pull (b) along $H$.
Associativity of $c$ and the etale-composition normalization in that lemma identify
$E_{F,P_eq}=LH^*E_{J,P_eq}\circ E_{H,bq_Q}$. Hence
$$E_{F,P_eq}\sigma_{a,b}=LF^*\sigma_{q,P_e}\bigl((LH^*\beta_{q,G}^{-1})E_{H,q_Q}\otimes
La^*E_{G,P_e}\bigr).\tag{c}$$
This proves the comparison of the two towers using the Cartesian
square and normalized etale factors separately.

Proof step 11. Check the input identifications in (c) against those defining $\kappa$. Pull the
Cartesian square $(p_f,a,s,i)$ of Step 4 back through $H$. The result is the Cartesian square of
etale maps $H:W\to\mathbf A_Q^d$ and $H_f:W_f\to\mathbf A_B^d$, with base $s:B\to Q$; explicitly
$H_f(u,u')=(u,x(u')-x(u))$. Its zero section is the image of $\Delta_f$. The base-change
compatibility of $\rho$ and $\eta$ in [lem-pur-finite-etale-dualizing-normalization], and vertical
exchange pasting [fix-lem-exchanges](2) for $a=q_QH$, identify $L\Delta_f^*E_{H_f,P_d}$ with
$Lt^*E_{H,q_Q}\gamma_f$, followed by the base-change comparison for $q_Q$ along $s$. Horizontal
exchange pasting identifies that comparison with $Lt^*LH^*\beta_{q,G}^{-1}$ followed by the $D_d$
comparison in Step 8: both are the inverse base-change comparison for $P_d$ along the composite
$B\xrightarrow sQ\xrightarrow G\mathbf A_B^e$, with $Gs=z_e$. Thus the first input of $Lt^*$(c) is
the actual difference-coordinate identification $C_f\to D_d$, using the route through $\gamma_f$,
not an arbitrary isomorphism. For the second input define $G_g:W_g=V\times_TV\to\mathbf A_V^e$ by
$(v,v')\mapsto(v,y(v')-y(v))$. The square with top $j:Q\to W_g$ and bottom $f:B\to V$ is
Cartesian, as is the square of $G_g$ and $G:Q\to\mathbf A_B^e$ over the affine-space pullback
$\mathbf A_B^e\to\mathbf A_V^e$. Vertical exchange pasting for $p_g=P_e^VG_g$, followed by etale
beta normalization, identifies the pullback of the section comparison $L\Delta_g^*E_{G_g,P_e^V}$
with $Ls^*E_{G,P_e}\gamma_g:Lf^*C_g\to D_e$. All composed pullbacks here use
[lem-weil-pbc-proetale-derived-pullback-composition].

Proof step 12. For the output, $Ft=z_{d+e}$ identifies $Lt^*E_{F,P_eq}:C_{gf}\to D_{d+e}$ with the
canonical total difference-coordinate comparison; here $E_F$ is obtained by composing the etale
comparisons for $H,J$, and [lem-pur-finite-etale-dualizing-normalization](2) makes this the
canonical comparison for their composite. Pull (c) back along $t$ and insert
$\gamma_f\otimes\gamma_g$. Step 11 identifies its two inputs with $D_d\otimes D_e$ exactly as in
Step 8; its middle arrow is $Lz_{d+e}^*\sigma_{q,P_e}$. Its left side is the coordinate image of
$\kappa$. This is precisely $\kappa|_U=\nu_{d,e}$. The tensor and pullback comparisons
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-proetale-derived-pullback-composition] give all the displayed source/target
identifications. The statement is conditional on compatible charts; their local availability
follows by applying [sbc-thm-etale-local-normal-form] first to $g$ and then to $f$. Empty charts
cause no assertion; when either block has length zero the translation, zero section and cocycle
calculations have the same formulas with the empty block, including the normalized etale unit. No
orientation or Tate-twist comparison has entered.
-/
theorem diagonalSectionPasting (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    Statement P d e f g aZ := by
  have := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  have := LocallyOfFiniteType.isLocallyNoetherian aZ
  have := QuasiCompact.compactSpace_of_compactSpace aZ
  have : IsNoetherian Z := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Y := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  change ModelStatement P.Coefficient P d e f g aZ
  refine ⟨diagonalSectionPastingEquation P d e f g aZ, ?_⟩
  intro X' Y' Z' f' g' u' v w _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hg
  refine ⟨diagonalSectionPastingOpen P d e f g f' g' u' v w hf hg aZ, ?_⟩
  intro _ _ _ x y _ _ hx hy
  exact diagonalSectionPastingChart P d e f' g' (w ≫ aZ) x y hx hy
end WeilConjectures.PurityFiniteSetting.DiagonalPasting
