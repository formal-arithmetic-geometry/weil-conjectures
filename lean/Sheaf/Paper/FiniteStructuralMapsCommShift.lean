/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.TraceExceptionalAdmissibility
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekTriangulated
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Canonical finite structural maps and the specified shifts

Source: Stacks, derived.tex, Tags 05SU, 0DVC, 0A8D; more-etale.tex, Tags 0F7B, 0F7J
(blueprint: lem-trf-finite-structural-maps-commshift).

We use the fixed-module coordinates of the canonical constant-ring realization.
The positive exponent is `n + 1`, so every positive finite level occurs. All equations
are on bounded constructibles; compactification maps retain their etale-origin objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Fixed-module coordinates for the recorded positive quotient coefficient ring.
Source: coefficient conventions (blueprint: lem-trf-finite-structural-maps-commshift). -/
abbrev structuralCoefficient :=
  ULift.{u + 1, u} (finiteCoefficientRing l E (n + 1))

/-- The identity-open normalization in the fixed-module presentation.
Source: Stacks 0F7I, proper compactification convention
(blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralProperIdentity {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) (Compactification.ofIsProper f) ≅
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (structuralCoefficient l E n)) (𝟙 X))
        (ProEtale.upperStarId
          (ModuleCat.{u + 1} (structuralCoefficient l E n)) X)) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- Proper coincidence at the chosen compactification: the recorded canonical
compactification comparison followed by the identity-open identification.
Source: Stacks 0F7I (blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralProperComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [HasCompactification f] :=
  trfOriginCompactificationComparison l E n (HasCompactification.compactification f)
      (Compactification.ofIsProper f) ≪≫
    Functor.isoWhiskerLeft
      (ProEtale.DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) X).ι
      (structuralProperIdentity l E n f)


/-- The specified exceptional shift: canonical shifts on R nu_* and nu^*, and the
unique shift on the etale right adjoint compatible with its compact-support adjunction.
Source: Stacks 0A8D (blueprint: lem-trf-finite-structural-maps-commshift). -/
@[instance_reducible]
def structuralExceptionalCommShift {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (trfExceptional l E n f).CommShift ℤ := by
  letI := (Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).rightAdjointCommShift ℤ
  exact inferInstanceAs
    (((ProEtale.comparisonLowerStar
      (ModuleCat.{u + 1} (structuralCoefficient l E n)) Y).rightDerivedFunctor ⋙
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (structuralCoefficient l E n)) f ⋙
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) X).mapDerivedCategory).CommShift ℤ)


/-- The component of the composite shift on Rf_! Rf^!, with precisely the exceptional
shift specified above. Source: Stacks 0A8D
(blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralCounitShift {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  letI := structuralExceptionalCommShift l E n f
  ((trfExceptional l E n f ⋙ ProEtale.rightDerivedLowerShriek
    (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).commShiftIso (1 : ℤ))


/-- The normalized constructible exceptional counit. Its first arrow is the inverse
of the canonical compact-support site comparison in the statement's orientation;
then apply the etale counit and the comparison counit. It is defined only on bounded
constructible objects of finite Tor amplitude, not on arbitrary pro-etale complexes.
Source: Stacks 0A8D; transported counit in det-sp-et-proet-adjunction-transfer
(blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralCounit (k : Type u) [Field k] {X Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (structuralCoefficient l E n))))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (structuralCoefficient l E n)) Y K) :
    (ProEtale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).obj
        ((trfExceptional l E n f).obj K) ⟶ K :=
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  (ProEtale.compactSupportSiteComparison (structuralCoefficient l E n)
      (HasCompactification.compactification f)).hom.app
        ⟨_, ProEtale.plus_etaleRightDerivedUpperShriek_obj f hK.1.bounded.1⟩ ≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (structuralCoefficient l E n)) Y).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).counit.app _) ≫
    (ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} (structuralCoefficient l E n)) Y).counit.app K


/-- The ordinary derived unit on the recorded bounded constructible domain.
Source: Stacks 0DVC (blueprint: lem-trf-finite-structural-maps-commshift). -/
abbrev structuralUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).unit


/-- The ordinary composite's canonical shift comparison.
Source: Stacks 05SU (blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralUnitShift {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (((ProEtale.upperStar (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).leftDerivedFunctor ⋙
    (ProEtale.lowerStar
      (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).rightDerivedFunctor).commShiftIso
        (1 : ℤ))


/-- The recorded compact-support candidate's canonical shift comparison.
Source: Stacks 05SU (blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralSupportShift {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  (ProEtale.rightDerivedLowerShriek
    (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).commShiftIso (1 : ℤ)


/-- The ordinary direct image's canonical derived shift comparison.
Source: Stacks 05SU (blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralDirectShift {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((ProEtale.lowerStar
    (ModuleCat.{u + 1} (structuralCoefficient l E n)) f).rightDerivedFunctor).commShiftIso
      (1 : ℤ)


/-- The composite shift for Rg_! Rf_!, in the same order as its compositor.
Source: Stacks 05SU (blueprint: lem-trf-finite-structural-maps-commshift). -/
def structuralCompositionShift {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] :=
  (ProEtale.rightDerivedLowerShriek
    (ModuleCat.{u + 1} (structuralCoefficient l E n)) f ⋙
      ProEtale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) g).commShiftIso (1 : ℤ)


/-- All four canonical finite-coefficient structural transformations satisfy the shift
square, as do the inverses of proper coincidence and compact-support composition.
The proper maps are restricted to bounded constructibles. The compositor is evaluated
at its recorded origin object, with the shifted origin obtained from the shifted
bounded constructible. The counit is the normalized transported counit on finite-Tor
constructibles, carrying the explicitly specified composite exceptional shift.
Source: Stacks 05SU, 0DVC, 0A8D, 0F7B, 0F7J
(blueprint: lem-trf-finite-structural-maps-commshift).

Proof plan (the node's thirteen steps, with its dependency citations):

1. Fix the shift convention $(K[1])^r=K^{r+1}$, $d_{K[1]}=-d_K$. All pullbacks below use the
specified constant-ring identifications. For pro-etale geometric pullback these identifications
are isomorphisms by [prop-weil-pbc-proetale-constant-ring-map], and
[def-weil-pbc-proetale-operations] identifies $Lu^*$ with exact termwise module inverse image.
For etale geometric pullback use [prop-weil-pbc-inverse-image-modules-exact]; for $H_T=\nu_T^*$
use [lem-sf-comparison-pullback-exact]. Thus their shift comparisons are the degreewise
identities of [lem-weil-pbc-exact-functor-derived-factorization]. For any right derived functor
computed by K-injectives, a resolution $s:K\to I$ can be replaced for $K[1]$ by $s[1]:K[1]\to
I[1]$, by [lem-weil-pbc-kinjective-shift]. The resulting degreewise identification
$u_*(I[1])=(u_*I)[1]$ is precisely the canonical derived shift: comparison with any other
resolving choice is unique in the homotopy category by [lem-sp-kinjective-comparison-principle],
and comparison maps also shift. We will use these representatives for calculations, keeping the
given canonical shifts.

2. The ordinary derived adjunctions, including $H_T\dashv U_T=R\nu_{T,*}$, are compatible with
these shifts. Here is the check rather than an appeal to exactness of the two functors. For an
exact module inverse image $L\dashv u_*$, the complex-level transpose is $a\mapsto
u_*(a)\eta_M$, with inverse $b\mapsto\varepsilon_I L(b)$, by
[lem-weil-pbc-termwise-adjunction-homotopy]. In degree $r$, its transpose at $(M[1],I[1])$ is
the same map in degree $r+1$ as at $(M,I)$: the unit and counit have degree zero, and both
differentials acquire the same minus sign. The canonical derived Hom bijection is the one
characterized by these representatives and resolution comparisons in
[lem-pc-pre-derived-adjoint-functors-general]. Shifting those representatives and
quasi-isomorphisms therefore preserves that bijection. Apply this to the identity of $LM$: its
transpose is the derived unit, so $\chi_{Ru_*L}(M)\eta_{M[1]}=\eta_M[1]$. Apply it to the
identity of $Ru_*K$: its inverse transpose is the derived counit, so
$\varepsilon_{K[1]}=\varepsilon_K[1]\chi_{LRu_*}(K)$. This proves clause (1) for the given
ordinary unit, and also provides both comparison-adjunction equations needed below. The module,
rather than merely abelian-sheaf, adjunction is the one used in step 1.

3. The canonical direct-image composition map $\kappa_{v,u}:R(vu)_*\to Rv_*Ru_*$ commutes with
shifts. Indeed [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] normalizes it on a
K-injective $I$ by $v_*u_*I\xrightarrow{v_*t}v_*J$, where $t:u_*I\to J$ is a K-injective
resolution. Use $I[1],J[1],t[1]$ for the shifted input; these are valid resolutions by step 1.
The normalized arrow is then $v_*(t[1])=(v_*t)[1]$, which is exactly the required square for the
composite shifts. For exact open extension on either site, sheaf-level composition, identity,
and site-comparison maps also commute with shifts after termwise descent: their degree-$r$
component on $K[1]$ is their degree-$(r+1)$ component on $K$, and additivity gives the same
negative differentials. For pro-etale open extension, exactness is
[lem-weil-extension-by-zero-exact]; its composition map is obtained by transposing the identity
$(j_2j_1)^*=j_1^*j_2^*$ under [lem-weil-extension-by-zero-adjunction]. For etale open-extension
exactness use [lem-weil-pbc-extension-by-zero-exact], and for its composition use
[lem-cbc-extension-zero-composition]. The cross-site open comparison is
[lem-cbc-proetale-extension-zero-comparison]. In every case the two sides of the shift square
are thus the same degree-zero chain map.

4. On the etale site consider a commutative proper/open square with vertical maps $r,p$ proper
and horizontal maps $k,i$ open. Its named interchange $\gamma^e:i_!Rr_*\to Rp_*k_!$ has the
normalization of [lem-cbc-proper-open-interchange-coherence]: on a K-injective representative
$J$ it is $i_!r_*J\cong p_*k_!J\to p_*I$, for a K-injective resolution $k_!J\to I$. Choose the
shifted resolution $k_!J[1]\to I[1]$ for $J[1]$. The sheaf-level proper/open identification is
natural in the module, so its degree-$r$ component is the original component in degree $r+1$.
The second arrow is the shift of the chosen resolution arrow. Consequently the whole
representative is the shifted original arrow, proving the shift square for $\gamma^e$ with the
canonical composite shifts. This does not infer shift compatibility from mere naturality. The
cited node supplies the normalization and invertibility on $D^+$ for finite $A$; the calculation
supplies the extra shift equation. Its special case $r=1$, $k=j_1$, $i=j_2$, $p=u$ is the named
etale proper-refinement map.

5. For a proper map $u$, the named site direct-image comparison $b_u:H_VRu^e_*\to Ru^p_*H_U$ is
the mate specified in [lem-weil-pbc-comparison-direct-image-canonical-mate]. Write
$a_u:H_ULu_e^*\to Lu_p^*H_V$ for [lem-weil-pbc-comparison-pullback]. Its module realization
comes from the same inverse-image comparison on sheaves, so it commutes with shifts by the
degreewise calculation of step 3. Set $q=H_U\varepsilon^e_u\circ a_u^{-1}$. The mate formula is
$b_u=Ru^p_*(q)\circ\eta^p_uH_VRu^e_*$. Steps 2 and 3 show that every factor here commutes with
shifts. Composition and whiskering preserve the equation by
[lem-weil-pbc-commshift-nattrans-comp-whisker], so $b_u$ does too. Combining $b_p$ with the
termwise open comparison $e_j:H_{\overline X}j^e_!\to j^p_!H_X$ gives the named compact-support
comparison $$c_c=Rp^p_*(e_j)\circ b_pj^e_!:H_Y(Rp^e_*j^e_!)\xrightarrow{\sim}(Rp^p_*j^p_!)H_X.$$
Its invertibility on the bounded-below etale-origin domain is
[lem-sf-class-compact-support-comparison]. Thus $c_c$ has the shift equation with the specified
derived shifts of the candidate, without redefining either shift.

6. The named proper-refinement comparison on the pro-etale etale-origin domain has the
normalization [lem-sf-proper-open-comparison-site-normalization] $$\alpha^p_u
e_{j_2}=Ru^p_*(e_{j_1})\,b_u j^e_{1!}\,H_{T_2}(\alpha^e_u).$$ Steps 3--5 give the shift equation
for every factor on the right and for $e_{j_2}$. Cancel $e_{j_2}$ to obtain it for $\alpha^p_u$
on $H_XL$. For an arbitrary witness $w:H_XL\xrightarrow{\sim}K$, the definition gives
$\alpha_u(K,L,w)=Ru_*j_{1!}(w)\circ\alpha^p_{u,L}\circ j_{2!}(w)^{-1}$. The shifted witness is
$w'=w[1]\circ\chi_{H_X}(L):H_X(L[1])\to K[1]$. Naturality of the shift comparisons gives
$\chi_{Ru_*j_{1!}}(K)\,Ru_*j_{1!}(w')=Ru_*j_{1!}(w)[1]\,\chi_{Ru_*j_{1!}H_X}(L)$ and the
corresponding equation for $j_{2!}(w')$. Substitution of these two equations and the square
already proved at $L$ cancels $w[1]$ and its inverse, giving the square at $(K,L,w)$. Now
[def-sf-refinement-comparison-isomorphism] specifies a candidate comparison $\theta_u$ as
$\kappa_{p_2,u}$ followed by $Rp_{2*}(\alpha_u^{-1})$. Both factors commute with shifts. For
clarity, if $\chi_G\tau_{[1]}=\tau[1]\chi_F$ and $\tau$ is invertible, multiplying on the left
by $\tau[1]^{-1}$ and on the right by $\tau_{[1]}^{-1}$ gives
$\chi_F\tau_{[1]}^{-1}=\tau[1]^{-1}\chi_G$; this justifies every inverse used here. Comparisons
through common refinements are composites of such arrows by
[prop-compactification-coherence-detailed], so they too commute with shifts. For proper $f$,
take the compactification $(1_X,f)$: its candidate is $Rf_*1_!$, and the identity-open
comparison $1_!\cong1$ is degreewise the identity. Comparing the chosen candidate to this
candidate by $\theta$, then using this identity, is exactly the specified $p_f:Rf_!\to Rf_*$ of
clause (2). This proves its shift equation and that of its inverse.

7. Choose compatible compactifications by [lem-weil-pbc-compatible-compactification-triangle]:
$Y\xrightarrow i\overline Y\xrightarrow sZ$ and $X\xrightarrow a\overline X\xrightarrow
p\overline Y$, with $V$, $b$, $q$, $j$ as there; the square $pb=iq$ is Cartesian. The etale
compositor on this tower is the specified normalization of
[lem-amb-unbounded-compact-support-comparisons]: $$Rs_*i_!Rq_*j_!\xrightarrow{Rs_*\Gamma_Q
j_!}Rs_*Rp_*b_!j_!\xrightarrow{\kappa_{s,p}^{-1}}R(sp)_*b_!j_!
\xrightarrow{R(sp)_*\operatorname{comp}_{b,j}}R(sp)_*a_!,$$
where $\Gamma_Q:i_!Rq_*\to Rp_*b_!$ is its proper/open interchange. By the last sentence of the
same statement, on bounded-below inputs this $\alpha^e_{g,f}$ is the composition isomorphism of
[lem-amb-etale-compact-comparisons] with the same normalization; this is the etale compositor
used in step 9.

8. The interchange $\Gamma_Q$ of step 7 is the map of
[lem-amb-unbounded-proper-open-interchange] for the square $pb=iq$. Its specified representative
on a K-injective $J$, with a K-injective resolution $b_!J\to I$, is $i_!q_*J\cong p_*b_!J\to
p_*I$, where the first map is the canonical sheaf proper-support identification (both sides are
the same subsheaf of $(iq)_*J=(pb)_*J$). For $J$ representing an object of $D^+$ this is exactly
the representative of $\gamma^e_Q$ in [lem-cbc-proper-open-interchange-coherence] used in step
4, so $\Gamma_Q=\gamma^e_Q$ on $D^+$ and the shift calculation of step 4 applies verbatim; its
adjoint description is not needed. Hence each of the three arrows of step 7 commutes with
shifts, by steps 3--4, and $\kappa_{s,p}^{-1}$ does by the inverse calculation of step 6. The
composition and whiskering rule [lem-weil-pbc-commshift-nattrans-comp-whisker] gives the shift
square for the etale compositor $\alpha^e_{g,f}$ on $D^+(X_{\mathrm{et}},A)$.

9. Write $c_h:H F_h^e\to P_hH$ for the candidate comparison of step 5.
[lem-pur-compact-support-site-coherence] names the same map,
$B_h^c=Rp_{p,*}(e_j)\circ\beta_{p,j^e_!}$ with the counit-mate $\beta_p$ and the adjoint open
comparison $e_j$, so $B_h=c_h$. Its hypotheses hold here: its datum [def-pur-conventions] is the
item's ($k=\overline{k_0}$, $\ell\ne p$, $A=A_{E,n}$), the schemes are finite type over $k$, the
three maps are separated finite type, and we use the compatible tower of step 7. Its composition
identity on $D^+(X_{\mathrm{et}},A)$ reads
$c_{gf}H_Z(\alpha^e_{g,f})=\alpha^p_{g,f}H_X\circ(P_gc_f)\circ(c_gF_f^e)$, with $\alpha^e$ the
compositor of [lem-amb-etale-compact-comparisons] (step 7) and $\alpha^p$ that of
[thm-sf-comp-composition]. Since $c_f$ and $c_g$ are invertible (step 5), this is
$$\alpha^p_{g,f,H_XL}=c_{gf,L}H_Z(\alpha^e_{g,f,L})c_{g,F_f^eL}^{-1}P_g(c_{f,L}^{-1}).$$ Step 8
proves the shift square for the etale middle arrow, and step 5 proves it for each $c_h$. By
[lem-weil-pbc-commshift-nattrans-comp-whisker], and step 6 for inverses, the right side has the
shift square with exactly the composite canonical shifts of the statement. This proves it for
the named pro-etale compositor on $H_XL$.

10. For a witness $w:H_XL\xrightarrow{\sim}K$, naturality of the compositor conjugates its value
at $H_XL$ by $P_gP_f(w)$ and $P_{gf}(w)$. Use the shifted witness $w[1]\chi_{H_X}(L)$;
naturality of both composite shift comparisons cancels those two witness factors just as in step
6. The resulting square is the one at $K$. Choice-independence in [thm-sf-comp-composition] and
the cocycle in [prop-compactification-coherence-detailed] conjugate the tower value by the
specified refinement comparisons, whose shift squares were proved in step 6. Composition and
whiskering preserve the square [lem-weil-pbc-commshift-nattrans-comp-whisker]. Thus the original
$\alpha_{g,f}$ commutes with shifts on the stated domain, and the inverse calculation of step 6
gives its inverse square. This proves clause (3).

11. For clause (4), retain the compactification $c=(j,p)$ used in the definition and write
$F^e=Rp^e_*j^e_!$, $G^e=f^{\times}$, $P=Rp^p_*j^p_!$, $H_T=\nu_T^*$, $U_T=R\nu_{T,*}$. By
[lem-weil-pbc-adjunction-shift-compatibility-unique], the right adjoint $G^e$ of $F^e$ has the
unique shift adjoint to that of $F^e$, and its etale counit $\varepsilon^e:F^eG^e\to1$ commutes
with these shifts. This is precisely the $G^e$ shift fixed in the statement. The two other
factors of $R=H_XG^eU_Y$ carry the canonical shifts of step 1, and the comparison adjunction
counit $v_Y:H_YU_Y\to1$ commutes with shifts by step 2. Consequently every factor of the
following natural map commutes with shifts: $$e_M:P
H_XG^eU_YM\xrightarrow{c_c(G^eU_YM)^{-1}}H_YF^eG^eU_YM
\xrightarrow{H_Y\varepsilon^e_{U_YM}}H_YU_YM\xrightarrow{v_{Y,M}}M.$$
Here $c_c$ is exactly the map of step 5. Applying the composition/whiskering equations from
[lem-weil-pbc-commshift-nattrans-comp-whisker] gives $$e_{M[1]}=e_M[1]\,\chi_{PR}(M).$$ This
uses the composite shift of $H_XG^eU_Y$ specified in the question throughout.

12. Identify $e$ with the required constructible counit, including its normalization. By
[lem-sf-proetale-constructible-origin], a bounded constructible $M$ has an etale origin $M\cong
H_YN$; by [lem-sf-comparison-tor-amplitude], finite Tor amplitude is preserved and reflected, so
$N$ belongs to the etale finite-Tor category when $M$ does. The comparison unit $N\to U_YH_YN$
is an isomorphism by [thm-weil-pbc-site-comparison]; by step 2 it is compatible with the
canonical shifts, so the quasi-inverse $U_Y$ has the very shift used in step 11. The finite
coefficient adjunction and its transport by this unit and $c_c$ are stated in
[lem-pur-finite-coefficient-adjoint-comparisons]. The transported counit formula in
[det-sp-et-proet-adjunction-transfer] says on $H_YN$ exactly $H_Y\varepsilon^e_N\circ
c_c(G^eN)^{-1}$, after the equivalence identifications. To make the equivalence identification
explicit, set $t=\eta^\nu_N:N\xrightarrow{\sim}U_YH_YN$. Naturality of $c_c$ and $\varepsilon^e$
gives $$e_{H_YN}\circ P H_XG^e(t)=v_{Y,H_YN}\circ H_Y(t)\circ H_Y(\varepsilon^e_N)\circ
c_c(G^eN)^{-1}=H_Y(\varepsilon^e_N)\circ c_c(G^eN)^{-1},$$ where the last equality is the
comparison triangle identity $v_{Y,H_YN}\circ H_Y(t)=1$. The isomorphism $P H_XG^e(t)$ is
exactly the source identification from $PH_XG^eN$ to $PH_XG^eU_YH_YN$, so this is the stated
transported-counit formula. Thus $e_{H_YN}=\varepsilon_{f,H_YN}$, and naturality along
$H_YN\cong M$ gives $e_M=\varepsilon_{f,M}$ for every $M\in D^b_{ctf}(Y,A)$. These are the
constructible maps fixed by [def-trf-admissibility]. If its compact-support functor is expressed
at another compactification, the refinement comparison of step 6 is inserted on the left, and
preserves the equation. This proves clause (4) for the given adjunction and the given shifts.

13. All calculations take place on the required domains. The coefficient ring is finite and
killed by a power of $\ell$, with $\ell$ invertible on every scheme. The field $k$ is Noetherian
because its only ideals are $0$ and $k$; its one-affine spectrum is therefore Noetherian.
Finite-type schemes over $k$ and the proper ambient schemes of a compactification are Noetherian
by [lem-weil-pbc-finite-type-over-noetherian] applied first to $\operatorname{Spec}k$ and then
to the proper maps; the starting schemes are qcqs by [lem-weil-pbc-qcqs-over-affine], since they
are separated finite type over $\operatorname{Spec}k$. Thus the compatible-tower and proper/open
comparison hypotheses used above hold. The etale-origin categories are preserved by compact
support by [thm-sf-comp-composition]; shifting a witness $H_TN\cong K$ gives $H_T(N[1])\cong
K[1]$ by step 1, so every shift equation stays in its domain. Bounded constructible inputs have
such witnesses by [lem-sf-proetale-constructible-origin]. For the exceptional counit the
preservation and adjunction on finite-Tor constructibles are supplied by
[lem-pur-finite-coefficient-adjoint-comparisons], so each term of steps 11--12 is defined there.
No assertion about a right adjoint on all pro-etale complexes is needed. Combining the equations
proved above gives exactly $\chi_G(M)\tau_{M[1]}=\tau_M[1]\chi_F(M)$ for all four specified
transformations. The elementary inverse calculation in step 6 gives the two remaining inverse
equations.
-/
theorem finiteStructuralMaps_commShift
    (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hl : l ≠ D.p)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    (∀ [IsProper f]
      (M : DerivedCategory (Sheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (structuralCoefficient l E n)))),
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) Y M →
      (structuralUnit l E n f).app (M⟦(1 : ℤ)⟧) ≫
          (structuralUnitShift l E n f).hom.app M =
        (shiftFunctor _ (1 : ℤ)).map ((structuralUnit l E n f).app M)) ∧
    (∀ [IsProper f]
      (M : DerivedCategory (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (structuralCoefficient l E n))))
      (hM : ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) X M),
      ((structuralProperComparison l E n f).hom.app
          ⟨M⟦(1 : ℤ)⟧, (hM.shift 1).plusEtaleOrigin⟩ ≫
            (structuralDirectShift l E n f).hom.app M =
        (structuralSupportShift l E n f).hom.app M ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((structuralProperComparison l E n f).hom.app ⟨M, hM.plusEtaleOrigin⟩)) ∧
      ((structuralProperComparison l E n f).inv.app
          ⟨M⟦(1 : ℤ)⟧, (hM.shift 1).plusEtaleOrigin⟩ ≫
            (structuralSupportShift l E n f).hom.app M =
        (structuralDirectShift l E n f).hom.app M ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((structuralProperComparison l E n f).inv.app ⟨M, hM.plusEtaleOrigin⟩))) ∧
    (∀ (M : DerivedCategory (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (structuralCoefficient l E n))))
      (hM : ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) X M),
      ((ProEtale.originCompositionAmbient (structuralCoefficient l E n) f g).hom.app
          ⟨M⟦(1 : ℤ)⟧, (hM.shift 1).plusEtaleOrigin⟩ ≫
            (structuralSupportShift l E n (f ≫ g)).hom.app M =
        (structuralCompositionShift l E n f g).hom.app M ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((ProEtale.originCompositionAmbient (structuralCoefficient l E n) f g).hom.app
              ⟨M, hM.plusEtaleOrigin⟩)) ∧
      ((ProEtale.originCompositionAmbient (structuralCoefficient l E n) f g).inv.app
          ⟨M⟦(1 : ℤ)⟧, (hM.shift 1).plusEtaleOrigin⟩ ≫
            (structuralCompositionShift l E n f g).hom.app M =
        (structuralSupportShift l E n (f ≫ g)).hom.app M ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((ProEtale.originCompositionAmbient (structuralCoefficient l E n) f g).inv.app
              ⟨M, hM.plusEtaleOrigin⟩))) ∧
    (∀ (M : DerivedCategory (Sheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (structuralCoefficient l E n))))
      (hM : ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (structuralCoefficient l E n)) Y M),
      structuralCounit l E n D.k f (M⟦(1 : ℤ)⟧) (hM.shift 1) =
        (structuralCounitShift l E n f).hom.app M ≫
          (shiftFunctor _ (1 : ℤ)).map (structuralCounit l E n D.k f M hM)) := by
  sorry

end WeilConjectures
