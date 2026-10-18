/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.Paper.NormalizedCoefficientFamilies
public import Sheaf.Paper.CompletedCompactSupportExchange
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.Paper.FiniteExtensionCompactSupportBaseChange

import Sheaf.Paper.PbcActualRingedExchange
import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.IntegralCompactSupportUniformRestriction
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.Paper.SbcCompletedOperations
import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.PreservationConstructible
import Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.ProjectionCompactification
import Sheaf.SixFunctors.OpenTensorNormalization


/-! # Coefficient coherence of the normalized compact-support exchange

Source: blueprint main-20261015, `sk-thm-sf-pf-field/thm-cbc-qbar.proof.md`,
opening scalar-extension paragraph; Stacks Tag 0E8I for the open tensor factor
(blueprint: lem-cbc-rational-compact-support-coefficient-coherence).

The compact-support comparisons are specified by the open-unit/proper-counit
mates. The completed pullback comparisons retain their completion units.
The exchange is the rationalization of the actual strict-tower construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [IsNoetherian X'] [IsNoetherian Y']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

/-- The two compact-support families admit their specified exact coefficient
comparisons, coherently with identities, shifts and iterated coefficient extension.
Their composites with the specified completed pullbacks intertwine the rationalization
of the actual strict-tower compact-support exchange. No invertibility of that
exchange is asserted. The two inverse beta specifications are precisely the
open-unit/proper-counit factors, so the comparison is canonically specified.

Source: blueprint main-20261015, thm-cbc-qbar, opening scalar-extension paragraph;
Stacks Tag 0E8I for the open tensor factor
(blueprint: lem-cbc-rational-compact-support-coefficient-coherence).

Proof:
1. Work first with integral ambient derived categories, writing $R_W=\widehat{\mathcal O}_{E,W}$,
$S_W=\widehat{\mathcal O}_{L,W}$, $t=\varpi_E$, $v=\varpi_L$, and $C_W=(-)\otimes^L_{R_W}S_W$. By
[lem-weil-finite-free-completed-scalar-comparison], $S_W$ is finite free over $R_W$, $C_W$
preserves complete objects, and its specified quotient-tower comparison $\chi$ is the natural
isomorphism with the actual integral coefficient extension. Choose an $R_W$-module basis of $S_W$
only for checking isomorphisms at a fixed scheme: it identifies the underlying $R_W$-module
functor $C_W$ with a finite biproduct of copies of the identity. Tensor with $S_W$ is therefore
exact. All maps below are the canonical balanced maps, independent of this checking basis. The
coefficient identifications for scheme inverse image, open restriction and quotient maps are those
of [lem-weil-pbc-profinite-coefficient-inverse-image]; its naturality in the inverse system
identifies the two coefficient maps in every square. Work at intermediate compactification schemes
in ambient categories: no constructibility assertion for an intermediate factor is being assumed.
2. For $k:U\hookrightarrow W$ equal to $j$ or $j'$, construct $\lambda_k:C_Wk_{!,R}\longrightarrow
k_{!,S}C_U$. On the direct-sum extension presheaf its formula is $(i_\alpha x)\otimes s\mapsto
i_\alpha(x\otimes s)$, where $i_\alpha$ denotes a summand indexed by a map to the open. The
inverse of the natural tensor isomorphism in [lem-weil-pbc-ringed-slice-extension-tensor], with
$\mathcal F=S_W$, is exactly this map after sheafification. It is $S_W$-linear: multiplying $s$ by
$s'$ on either side gives $i_\alpha(x\otimes ss')$; balancing over $R_W$ gives the same formula.
Thus it is an isomorphism of $S_W$-module sheaves, not merely of underlying $R_W$-modules.
Extension by zero is exact by [lem-pur-site-restriction-module-adjunction-exact], and tensor with
$S_W$ is exact by step 1. Applying the isomorphism degreewise computes both derived functors;
[lem-sf-exact-functor-derived-triangulated] supplies the exact derived functors and their shift
comparisons. This proves the required derived coefficient-change version without treating the
underived tensor lemma itself as a derived or completed assertion.
3. Check the coherence of $\lambda$ on the same summands. For $E\subset L\subset N$ the
successive-extension composite sends $((i_\alpha x)\otimes s)\otimes z$ to $i_\alpha(x\otimes sz)$
after the balanced associators; the one-step comparison sends it to precisely that element. These
maps respect restrictions and therefore descend to sheafification and complexes. For the repeated
field, the tensor unit sends $(i_\alpha x)\otimes1$ to $i_\alpha x$; after the literal identity
normalization of [prop-weil-pbc-scalar-extension] this is the identity. The maps have degree zero
and are degreewise, so commuting them with a cochain shift introduces no sign; their shift square
is the one supplied in step 2. This establishes the open-factor unit, successive-field and shift
equations, with the specified balanced associators.
4. For every scheme map $q:Z\to W$ used here, use the canonical compatible coefficient
identifications from step 1 and apply [lem-sp-finite-free-direct-image-coherence] to
$R_T=\widehat{\mathcal O}_{E,T}$ and $S_T=\widehat{\mathcal O}_{L,T}$. Step 1 supplies finite
freeness; the lemma imposes no dimension or constructibility hypotheses on intermediate schemes.
It gives the actual $S_W$-linear counit-tensor comparison
$\pi_q:C_WRq_{*,R}\xrightarrow{\sim}Rq_{*,S}C_Z$, its input-shift square, tensor-unit
normalization and successive-coefficient equation. This is the proper direct-image coefficient
comparison specified by [prop-weil-pbc-scalar-extension], because both are defined by that
canonical scalar-extension/projection map. Use this construction for $p,p'$ in the ambient
categories.
5. Record carefully how scalar extension interacts with completion units. Let
$\Lambda_R,\Lambda_{S,t},\Lambda_{S,v}$ denote the Koszul completion reflectors. The DVR
description in [lem-weil-l-adic-extension-integers-dvr] gives $t=u v^e$ in $\mathcal O_L$, with
$u$ a unit and $e\geq1$ (the restricted absolute value gives $0<|t|_L<1$). The local completeness
conditions for $(t)$ and $(v)$ in $S_W$ agree: an element of $(t)$ lies in $(v)$, and for any
local $a\in(v)$ one has $a^e\in(t)$ and $S_W[1/a]=S_W[1/a^e]$. Hence the Hom-bijection in
[lem-weil-pbc-ringed-koszul-completion-reflector] gives a unique unit-preserving natural
isomorphism $\Lambda_{S,t}\cong\Lambda_{S,v}$. Tensor with the finite free $S_W$ commutes with the
strict Koszul-tower limit: after the basis check in step 1, the comparison with products is the
finite-biproduct rearrangement $\bigoplus_{i=1}^d\prod_n^D X_n\cong\prod_n^D\bigoplus_{i=1}^d
X_n$; it commutes with $1-s$ and hence with the natural Roos limit triangle of
[lem-weil-pbc-ringed-strict-tower-homotopy-limit]. At index $n$, tensor sends
$[R_W\xrightarrow{t^n}R_W]$ to $[S_W\xrightarrow{t^n}S_W]$ and sends the transition $(t,1)$ to
$(t,1)$. It therefore gives a unit-preserving isomorphism
$C_W\Lambda_R\cong\Lambda_{S,t}C_W\cong\Lambda_{S,v}C_W$. By [prop-weil-pbc-koszul-reconstruction]
the quotient-tower units are these same units. In particular these are comparisons for the actual
completed functors, including the specified $\chi$ in step 1, not arbitrary identifications of
complete endpoints.
6. Apply [lem-sf-open-tensor-normalization] to the open square $(j,j',\bar g',g')$, also on the
small ringed diagram sites furnished by [lem-weil-pbc-diagram-site-realization]. Its derived
tensor map gives the reduction comparison $j_!K\otimes_R^L R_n\cong j_!(K\otimes_{R_U}^L
R_{n,U})$, with its specified open-unit normalization, for arbitrary complexes. Thus no underived
tensor assertion is being substituted for a derived one. By
[lem-weil-pbc-constant-completion-equivalence], $R_n=(\mathcal O_E/t^n)_W$ and $S_n=(\mathcal
O_L/t^n)_W$ are exactly the completed-ring quotients. Step 1 reduced modulo $t^n$ makes $S_n$
finite free over $R_n$. The relation $t=uv^e$ of step 5 identifies $S_n$ with $(\mathcal
O_L/v^{en})_W$, with its actual quotient maps.
7. In these derived coefficient systems, the open base-change and tensor maps of
[lem-sf-open-tensor-normalization] are characterized by restriction to the identity after the open
adjunction units. Their coefficient square therefore commutes: after transposition under the open
adjunction, both composites are the same balancing map $x\otimes s\mapsto x\otimes s$. On
extension summands this reads $(i_\alpha x)\otimes s\mapsto i_{\alpha'}(g'^*x\otimes s)$ in either
order. The normalization lemma applies to the diagram topoi themselves, so this is an equality of
derived system morphisms, not an inference from equality of evaluations. Applying the total
derived-limit functor preserves that equality. The finite maps are the canonical ones of
[lem-cbc-proetale-extension-zero-base-change], by the last clause of the normalization lemma.
8. For the $L$ coefficients compare the $v$-quotient tower with its $en$ subsequence by
[lem-sp-strict-tower-arithmetic-restriction]. Its canonical restriction isomorphism preserves the
actual quotient-cone unit and commutes with the strict open/tensor square just proved.
Consequently the limit comparison is the unit-preserving comparison of step 5, and the
extension-zero/limit maps defining $\beta$ commute with it. This fixes the specified normalization
of [lem-cbc-completed-extension-zero-comparison] at both fields. Writing
$P_u=Lu^*_{\mathrm{comp}}$ and using the canonical completed balancing $d_u$ of
[prop-weil-pbc-scalar-extension], the resulting square is
$$(j'_!d_{g'})\lambda_{j',P_{g',R}K}C(\beta_R)=\beta_{S,CK}P_{\bar g',S}(\lambda_{j,K})d_{\bar
g',j_!K}.$$ The scalar map is this $d_u$ because the construction preserves both ordinary
balancing and its completion unit. For $e=1$ the restriction is literally the identity.
9. Identify the proper completed factor with its ambient-mate extension, keeping its actual strict
normalization. Use exactly $N,E,F,H,H',v_\bullet,s,c$ of [def-cbc-completed-exchange-map], so
$v_\bullet=H'\mathcal R(e_M)H^{-1}$ and $\gamma_M=c^{-1}R\lim(v_\bullet)s$. Write $\rho_Z:Z\to
R\lim\mathcal R(Z)$ for the quotient-tower unit, $\nu:N\to P_gRp_*M$ for the completed-pullback
unit, and $\nu':F\to Rp'_*P_{\bar g'}M$ for $Rp'_*$ of that unit. The balancing map $t$ sends a
quotient of a section to its pulled-back quotient. The adjunct defining $\Pi$ is counit tensor
identity; after precomposition with the quotient-unit map its adjunct is the counit followed by
the quotient map. Naturality of the counit therefore identifies it with direct image of the
quotient-unit map. These two unit identities give $s\nu=R\lim(H)\rho_N$ and
$c\nu'=R\lim(H')\rho_F$. The direct-image/limit comparison here is precisely the unit-compatible
one of [prop-weil-pbc-direct-image-limits]. Naturality of $\rho$ and cancellation of $H^{-1}H$ now
give the calculation $\gamma_M\nu=c^{-1}R\lim(H'\mathcal
R(e_M)H^{-1})R\lim(H)\rho_N=c^{-1}R\lim(H')\rho_F e_M=\nu'e_M$. The target is complete by
completeness of completed pullback and preservation by direct image. The source is the reflection
of $N$ by [def-weil-pbc-completed-pullback], with the same unit by reconstruction. Thus the
Hom-bijection of [lem-weil-pbc-ringed-koszul-completion-reflector] says that $\gamma_M$ is the
unique map extending $\nu'e_M$ across $\nu$. This proves the characterization for the particular
$v_\bullet$ in the definition; it never infers equality of strict-tower arrows from their
evaluations.
10. For the proper square $(p,p',g,\bar g')$, cartesian by the construction of $c'$, let $e^R,e^S$
be the ambient mates of [def-weil-pbc-ambient-ringed-exchange] for the coefficient sheaves $R_T$
and $S_T$, identified along the square by step 1, and let $\mu_u:Lu_S^*C\xrightarrow{\sim}CLu_R^*$
be the balancing of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], $d_u=\mu_u^{-1}$. First
prove in $D(S_{Y'})$ the ambient equation
$e^S_{CM}\,Lg_S^*(\pi_{p,M})\,d_{g,Rp_*M}=Rp'_{*,S}(d_{\bar g',M})\,\pi_{p',L\bar
g'^*M}\,C_{Y'}(e^R_M)$. By [def-weil-pbc-adjunction-mate] compare transposes under $Lp'^*_S\dashv
Rp'_{*,S}$. The definition in [lem-sp-finite-free-direct-image-coherence] gives
$\varepsilon^S_q\,Lq_S^*\pi_q=C(\varepsilon^R_q)\mu_q$ for $q=p,p'$; the mate definition gives
$\varepsilon_{p'}Lp'^*e=L\bar g'^*(\varepsilon_p)\theta$ for both rings. With naturality of
$\theta$ and $\mu$, the right side transposes to $d_{\bar g'}C(L\bar
g'^*_R\varepsilon^R_p\,\theta^R)\mu_{p'}$ and the left side to $d_{\bar g'}C(L\bar
g'^*_R\varepsilon^R_p)\,\mu_{\bar g'}L\bar g'^*_S(\mu_p)\,\theta^S\,Lp'^*_S(d_g)$. On K-flat
flat-term representatives $C(\theta^R)\mu_{p'}$ and $\mu_{\bar g'}L\bar
g'^*_S(\mu_p)\theta^SLp'^*_S(d_g)$ both send $x\otimes s$ to $x\otimes s$ through $p\bar g'=gp'$.
So the transposes agree as $S$-module arrows. Pass to completed pullbacks using step 5: precompose
with the $S$-completion unit of $C_{Y'}Lg_R^*Rp_{*,R}M$. Step 9 reduces both composites to this
ambient equation followed by $Rp'_*$ of the completion unit on the complete target, so the
reflector Hom-bijection makes them equal: $\gamma_{S,C
M}\,P_{g,S}(\pi_{p,M})\,d_{g,Rp_*M}=Rp'_{*,S}(d_{\bar g',M})\,\pi_{p',P_{\bar
g',R}M}\,C_{Y'}(\gamma_{R,M})$. Here $d$ on completed pullbacks is the completed balancing of
[prop-weil-pbc-scalar-extension], the direct-image/limit comparison is that of
[prop-weil-pbc-direct-image-limits]; step 9 fixed $H,H',v_\bullet$.
11. Let $u:T'\to T$ be $g$ or $g'$ and $M\in\mathcal C_E^{\mathrm{int}}(T)$. By
[lem-weil-pbc-integral-stratified-perfect-characterization] (iii), $M$ is bounded, say in
cohomological degrees $[a,b]$. The augmented two-term resolution $[\mathcal
O_E\xrightarrow{t^n}\mathcal O_E]$ of $\mathcal O_E/t^n$ is
[lem-weil-pbc-standard-quotients-perfect]. The flat constant-to-completed coefficient comparison
of [lem-weil-pbc-constant-completion-equivalence] tensors this to the corresponding resolution
over $R_T$. Hence $M_n$ is represented by $M\otimes^L[R_T\xrightarrow{t^n}R_T]$. The cone triangle
$M\xrightarrow{t^n}M\to M_n\to M[1]$ gives $\mathcal H^i(M_n)=0$ outside $[a-1,b]$ by its
cohomology exact sequence, independently of $n$. This is the common reduction bound required in
the next step.
12. Apply [prop-weil-pbc-preservation-constructible] to the cartesian square with vertical maps
$\mathrm{id}_T,\mathrm{id}_{T'}$ and both horizontal maps $u$. The four schemes are noetherian and
finite-dimensional, the identities are proper with fibres of dimension at most $0$, and $N=\ell$
annihilates $\mathcal O_E/t$ and is invertible on $T,T'$. The preceding step supplies its common
reduction bound. Its stated third conclusion gives $P_uM\in\mathcal C_E^{\mathrm{int}}(T')$, with
the uniform constructibility and compatible etale-origin witnesses required by
[def-weil-pbc-bounded-constructible-complete]. The square and its pullback comparison are
[def-weil-pbc-cartesian-square]. Thus this is preservation in the precise completed PBC category,
without identifying a different coefficient category with it.
13. On the inherited triangulations of [lem-weil-pbc-uniform-complete-triangulated], these
restricted $P_u$ are exact: [def-weil-pbc-completed-pullback] writes them as derived reduction
tower, derived tower pullback, and total derived limit, and
[lem-weil-pbc-ringed-strict-tower-homotopy-limit] makes the last functor exact. They are $\mathcal
O_E$-linear by [lem-sbc-completed-operations-linear-natural-exchange], whose domain is the full
derived-complete category, so its linearity restricts to this full subcategory. This supplies
exactly the hypotheses on $P$ needed for rational transport in the final step. For $f'$ the
separated-finite-type hypotheses follow from [lem-pod-separated-finite-type-base-change];
[def-cbc-compact-support-square] provides the pulled-back compactification. The opens are
quasi-compact by [def-cbc-completed-exchange-map].
14. Define $b^h=Rp_{h,*,S}(\lambda_{j_h})\,\pi_{p_h,j_{h,!}(-)}$. The compactification definition
[def-weil-pbc-projection-compactification] says $H_h=Rp_{h,*}j_{h,!}$. Steps 2 and 4 give an exact
natural isomorphism. Its endpoints lie in the required integral categories by
[lem-cbc-integral-compact-support-uniform-restriction] for $H_h$ and
[prop-weil-pbc-scalar-extension] for scalar extension. No separate constructibility claim for the
intermediate factors is needed. Compose their unit and shift squares to obtain those for $b^h$.
For a tower of fields substitute the successive-field equations for $\lambda$ and $\pi$ into
$Rp_*(\lambda)\pi$. Naturality of $\pi$ moves the inner $\lambda$ past $\pi$; the adjacent inverse
associators cancel. The surviving factors are $H_{h,N}(a^{\mathrm{source}(h)})$,
$b^h_{N/L,C_{L/E}K}$, $C_{N/L}(b^h_{L/E,K})$, $(a^{\mathrm{target}(h)})^{-1}$, in this order.
These give exactly the stated $b^h$ equation.
15. Prove the integral compact-support exchange equation by pasting the two established squares.
Set $M=j_!K$ and $B=Rp'_*(\beta)\gamma_M$, exactly the ordered composite in
[def-cbc-completed-exchange-map]. Start with $B_{S,CK}P_{g,S}(b^f)d_{g,H_fK}$. Replace $b^f$ by
$Rp_{*,S}(\lambda_j)\pi_p$. Naturality of $\gamma_S$ with respect to $\lambda_j$ changes the
initial portion to $Rp'_{*,S}(\beta_{S,CK}P_{\bar
g',S}(\lambda_j))\gamma_{S,CM}P_{g,S}(\pi_p)d_g$. Replace the latter three factors using the
proper equality of step 10. Inside $Rp'_{*,S}$ the consecutive factors are then
$\beta_{S,CK}P_{\bar g',S}(\lambda_j)d_{\bar g',j_!K}$; steps 6–8 replaces them by
$(j'_!d_{g'})\lambda_{j',P_{g',R}K}C(\beta_R)$. Naturality of $\pi_{p'}$ moves $C(\beta_R)$ to the
right across that projection comparison. The remaining left factors are
$H_{f',S}(d_{g'})b^{f'}_{P_{g',R}K}$, and the right factors are
$C(Rp'_*(\beta_R)\gamma_{R,j_!K})=C(B_{R,K})$. Therefore $B_{S,CK}b^U=b^V C(B_{R,K})$, with
$b^U=P_{g,S}(b^f)d^g$ and $b^V=H_{f',S}(d^{g'})b^{f'}$. This calculation uses no invertibility of
$B$ or $\gamma$.
16. Finally localize the integral functors and comparisons. By [def-weil-pbc-rational-category]
there are no new objects: a rational arrow is a finite sum of $u\otimes a$, with integral $u$ and
$a\in E$. By [prop-weil-pbc-rational-transport], the exact $\mathcal O_E$-linear $H,P$ and all
their integral natural transformations extend, with component $\eta_K\otimes1$. For the scalar
functor the extension on such an arrow is $C(u)\otimes\iota_{L/E}(a)$; this is well defined by
balancing, since $C(ru)=\iota(r)C(u)$ and every nonzero $r\in\mathcal O_E$ becomes invertible in
$L$. Thus an integral naturality square multiplied by $\iota(a)$ is the required rational
naturality square for $u\otimes a$, and additivity handles a general arrow. Apply localization to
the equations of steps 3, 4, 14 and 15: it preserves compositions, identities, inverses and
shifts. The scalar associators and shifts are those of [prop-weil-pbc-scalar-extension], whose
integral comparisons were used above. Consequently the rational $b^h$ have the displayed unit,
shift and successive-extension laws, their composite comparisons are the stated $b^U,b^V$, and
step 15 becomes $\eta_{L,TK}b^U=b^V T(\eta_{E,K})$ for the rationalization of precisely the
specified strict-normalized exchange. All hypotheses used were the stated integral-operation
domains, finite coefficient extensions and the compactification geometry; no base-field or
smoothness assumption was introduced.
-/
theorem rationalCompactSupportCoefficientCoherence
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (H : CbcCompactSupportCoefficientFamily l Ω c)
      (H' : CbcCompactSupportCoefficientFamily l Ω c')
      (P : CbcCompletedPullCoefficientFamily l Ω g)
      (P' : CbcCompletedPullCoefficientFamily l Ω g'),
      ∃ η : StageSystem.Morphism.Hom (H.family.base.comp P.family.base)
          (P'.family.base.comp H'.family.base),
        ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E)
          (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
          (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
          (hc : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K.obj),
          ∃ (hs : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
              ((cbcCompactSupportSource g c (pbcStageDatum.{u} l Ω E)).obj K.obj))
            (ht : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
              ((cbcCompactSupportTarget g' c' (pbcStageDatum.{u} l Ω E)).obj K.obj)),
            HEq ((η.τ E).app ((pbcStageLocalization l Ω X E).obj K))
              ((pbcStageLocalization l Ω Y' E).map
                (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
                  (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
                    c c' gbar properSquare openSquare r a ha ⟨K.obj, hc⟩))) := by
  sorry

end AlgebraicGeometry.Scheme
