/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedComparisonCoordinates
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.AlgebraicGeometry.LocallyClosedCounitComparison
import Sheaf.AlgebraicGeometry.LocallyClosedRelativeHomIdentity
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion

/-!
# Locally closed exceptional comparison with its adjunction normalization

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, second paragraph
(blueprint: lem-weil-finite-duality-locally-closed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- All clauses of locally closed exceptional comparison, on exactly bounded
constructible targets and bounded-below etale-origin tests. The natural transformations
are fixed by the counit and comparison-unit equations. The relative Hom equation is
required for every witness of etale origin and every normalized comparison-class datum.
Source: blueprint locally closed exceptional comparison, Steps 1--12
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
structure LocallyClosedExceptionalComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] where
  adjoints : LocallyClosedComparisonAdjoints A c
  bounded (M : Etale.BoundedConstructibleDerivedCategory A T) :
    _root_.DerivedCategory.TStructure.t.plus ((adjoints.etaleRight v).obj M.obj)
  gamma :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ adjoints.etaleRight v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        adjoints.proetaleRight v
  counit (M : Etale.BoundedConstructibleDerivedCategory A T) :
    (locallyClosedExtensionComparison A c v).hom.app
        ⟨(adjoints.etaleRight v).obj M.obj, bounded M⟩ ≫
      (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
      (adjoints.proetalePasted v).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        ((adjoints.etalePasted v).counit.app M.obj)
  transport :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        adjoints.proetaleRight v ≅
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        sfFiniteExceptionalAt A (locallyClosedImageCompactification (c ≫ v))
  unit_normalization (M : Etale.BoundedConstructibleDerivedCategory A T) :
    gamma.hom.app M ≫ transport.hom.app M =
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
        ((locallyClosedEtaleRightIso v adjoints).hom.app M.obj ≫
          (locallyClosedEtaleExceptional A (c ≫ v)).map
            ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M.obj))
  relative_hom
      (B : FixedComparisonClassAdjunction A (c ≫ v)
        (locallyClosedImageCompactification (c ≫ v))
        (locallyClosedEtaleExceptional A (c ≫ v))
        (Adjunction.ofIsLeftAdjoint _)
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S)
        _root_.DerivedCategory.TStructure.t.plus)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S K)
      (M : Etale.BoundedConstructibleDerivedCategory A T)
      (hM : _root_.DerivedCategory.TStructure.t.plus
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj))
      (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (w : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj L.obj ≅ K)
      (h : (locallyClosedProEtaleExtension A c v).obj K ⟶
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :
    ((adjoints.proetalePasted v).homEquiv _ _) h ≫ transport.hom.app M =
      B.homEquiv (locallyClosedImageCompactification (c ≫ v)) K hK
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) hM
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
            (locallyClosedImageCompactification (c ≫ v))).map w.inv ≫
          (fixedCompactSupportComparisonIso A
            (locallyClosedImageCompactification (c ≫ v))).hom.app L ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
            ((locallyClosedEtaleSupportIso A c v).inv.app L.obj) ≫
          (locallyClosedExtensionComparison A c v).hom.app L ≫
          (locallyClosedProEtaleExtension A c v).map w.hom ≫ h)

/-- Locally closed exceptional inverse image commutes with etale/pro-etale comparison,
with the specified counit, relative adjunction, comparison-unit normalization and
factorization coherence. Positive levels are indexed by `n + 1`, hence cover all n >= 1.
The existential typeclass witnesses are consequences of finite type, not extra premises.
Source: Weil blueprint, main-20261015, locally closed comparison sentence in the second
paragraph of lem-weil-finite-duality-site-comparison.proof.md
(blueprint: lem-weil-finite-duality-locally-closed-comparison).

Proof plan (the node's twelve steps):
1. Write $C_W=\nu_W^*$, $I_e=Rc_{et}^!$, $I_p=Rc_{proet}^!$, $N=v_{et}^*M$ and $H=I_eN$. The
schemes $S,T$ are Noetherian: a field has only the ideals $0,1$, so its spectrum is Noetherian,
and finite type over it is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. The open-
subscheme theorem gives Noetherian $V$ and quasi-compactness of all the complementary opens. The
open $V$ is still finite type over $k$: cover $T$ by finitely many affine finite-type charts, and
cover the intersection of $V$ with each chart by finitely many principal opens, possible by this
quasi-compactness. Their rings are localizations of finite-type $k$-algebras at one element,
hence generated by the original generators and that inverse. Separatedness restricts to an open
subscheme by restriction of the closed diagonal. Exact inverse image and [lem-weil-pbc-exact-
functor-bounded-below] give $\mathcal H^r(N)=v^*\mathcal H^r(M)$; constructible pullback
therefore gives $N\in D^b_c(V_{et},A)$ [prop-constructible-pullback]. Apply [lem-weil-finite-
duality-closed-comparison] to $c$ and $N$. Its bounded-below conclusion gives $H=J_{et}M\in
D^+(S_{et},A)$, so the named closed direct-image comparison can be evaluated at $H$.

2. Use $b:C_Vv_{et}^*\xrightarrow{\sim}v_{proet}^*C_T$ for [lem-weil-pbc-comparison-pullback] and
$o:C_Tv_{et,!}\xrightarrow{\sim}v_{proet,!}C_V$ for [lem-cbc-proetale-extension-zero-comparison].
Their open unit normalization is [lem-sf-open-comparison-unit-normalization]. These sheaf
comparisons and their normalization hold also on ordinary derived categories: the two open
extensions are exact [lem-weil-pbc-extension-by-zero-exact, lem-weil-extension-by-zero-exact],
and comparison and open restriction are exact inverse images [lem-sf-comparison-pullback-exact,
prop-weil-pbc-inverse-image-modules-exact, prop-weil-pbc-proetale-constant-exact]. Apply the
comparisons degreewise. The termwise-adjunction theorem carries the units, counits and triangle
identities to complexes; the localization universal property descends these transformations and
their equalities, since the exact functors preserve quasi-isomorphisms. Thus, writing
$r=v_{et}^*$ and $t=v_{proet}^*$ and the open units as $u^e,u^p$, we have
$$t(o_L)\,b_{v_{et,!}L}\,C_V(u^e_L)=u^p_{C_VL}.$$ This uses the specified $b,o$, rather than
choices of isomorphisms with the same endpoints.

3. Let $e^e,e^p$ be the open counits. The preceding unit equation implies
$$e^p_{C_TM}\,v_{proet,!}(b_M)\,o_{rM}=C_T(e^e_M).$$ Indeed, transpose $C_T(e^e_M)o_{rM}^{-1}$
under the pro-etale open adjunction. Its transpose is $$tC_T(e^e_M)\,t(o_{rM}^{-1})u^p_{C_VrM}
=tC_T(e^e_M)\,b_{v_{et,!}rM}C_V(u^e_{rM}) =b_M C_V\bigl(r(e^e_M)u^e_{rM}\bigr)=b_M.$$ The first
equality is the unit normalization, the second naturality of $b$, and the third the etale
triangle identity. Inverse transposition gives the displayed counit equation.

4. The closed comparison theorem gives the natural isomorphism $$\alpha_N:C_S
I_eN\xrightarrow{\sim}I_p C_VN$$ and the equation
$$k^p_{C_VN}\,c_{proet,*}(\alpha_N)\,\delta_H=C_V(k^e_N),$$ where $k^e,k^p$ are the closed
counits and $\delta:C_Vc_{et,*}\xrightarrow{\sim}c_{proet,*}C_S$ is the specified closed direct-
image comparison. Define $$\gamma_M=I_p(b_M)\,\alpha_N:C_SJ_{et}M\longrightarrow
I_pv_{proet}^*C_TM=J_{proet}C_TM.$$ Both factors are natural isomorphisms. The closed theorem
applies because Step 1 proved exactly its bounded constructible input hypothesis; no assertion
about closed ordinary restriction commuting with internal Hom is used.

5. For bounded-below $L$ set $$\Delta_L=v_{proet,!}(\delta_L)\,o_{c_{et,*}L}.$$ This is exactly
the named comparison in the statement: the closed map is [lem-weil-pbc-comparison-direct-image-
canonical-mate], and the open map is [lem-cbc-proetale-extension-zero-comparison]. Since $c$ is
finite [lem-weil-pbc-closed-immersion-finite], its exact etale direct image preserves the lower
bound [lemma-weil-pbc-finite-direct-image-exact], also for constant-$A$ modules by the
underlying-sheaf functor. The maps are therefore defined at every such $L$, in particular at $H$.
By the composite adjunction formula,
$$\epsilon^\tau_M=e^\tau_M\,v_{\tau,!}(k^\tau_{v_\tau^*M}),$$ and the corresponding unit is the
pasted unit. These are the adjunctions fixed in the statement.

6. Expand $\gamma,\Delta$ and the pasted counit in the left side of the required equation.
Naturality of $k^p$ at $b_M:C_VN\to v_{proet}^*C_TM$, followed by Step 4, gives $$\begin{aligned}
\epsilon^p_{C_TM}F_p(\gamma_M)\Delta_H
&=e^p_{C_TM}\,v_{proet,!}(b_M)\,v_{proet,!}\bigl(C_V(k^e_N)\bigr)\,o_{c_{et,*}H}\\
&=e^p_{C_TM}\,v_{proet,!}(b_M)\,o_N\,C_T\bigl(v_{et,!}(k^e_N)\bigr)\\
&=C_T(e^e_M)\,C_T\bigl(v_{et,!}(k^e_N)\bigr) =C_T(\epsilon^e_M). \end{aligned}$$ The second
equality is naturality of $o$ at $k^e_N:c_{et,*}H\to N$; the third is precisely Step 3. This
proves the counit identity for the specified comparisons, not merely existence of an abstract
comparison. Transposition in $F_p\dashv J_p$ says equivalently that $\gamma_M$ is the unique
transpose of $C_T(\epsilon^e_M)\Delta_H^{-1}$.

7. Identify $F_e$ with ordinary etale compact support for $s$. Let $\bar S$ be the scheme-
theoretic closure of $S$ in $T$, with $u:S\hookrightarrow\bar S$ open and $i:\bar
S\hookrightarrow T$ closed. Here $i$ is proper directly from the closed-immersion definition:
affine base change is quotient by the extended ideal, hence closed; its diagonal is an
isomorphism, and the quotient algebra is generated by $1$ as a module. The closure is finite type
over $k$, since on the finite-type affine charts of $T$ its rings are quotients. The normalized
comparison of [lem-sfb-etale-locally-closed-extension-comparison] is $v_!c_*\cong i_*u_!$ on
sheaves. Both sides are exact: open extension is exact and closed direct image is exact by
finiteness. Hence the termwise comparison descends to all derived complexes [lem-weil-pbc-exact-
functor-derived-factorization, lem-weil-pbc-localization-universal-property]. In the closure
compactification, [def-amb-etale-compact-support] gives $Rs_!=Ri_*u_!=i_*u_!$; exactness of $i_*$
means that applying it to a quasi-isomorphism into a K-injective resolution is a quasi-
isomorphism, so this equality holds unboundedly as well. The adjoint exists by [thm-amb-etale-
exceptional-adjoint]. Right-adjoint uniqueness, with its unit and counit normalization [lem-cat-
right-adjoint-composition, def-weil-pbc-adjunction-conjugate], identifies $J_e$ with $s^\times$
compatibly with the chosen identification of left adjoints. On pro-etale categories the
corresponding normalized identification $F_p\cong i_*u_!$ and factorization independence are
supplied by [lem-sfb-locally-closed-extension-coherence].

8. First justify the termwise interpretation of the closed comparison. For either closed
immersion $h=c$ or $h=i$, both $h_{e,*}$ and $h_{p,*}$ are exact: use closed finiteness and
finite etale direct-image exactness, and the pro-etale ringed open/closed theorem. Their
complements are quasi-compact by Noetherianity. The pullbacks and $C$ are exact as in Step 2. At
the sheaf level form the $h_p^*\dashv h_{p,*}$ transpose $\delta_h^0$ of
$$C(\varepsilon^e_{h,L})a_{h,h_{e,*}L}^{-1}.$$ The module adjunction supplies this transpose.
Termwise adjunction and localization carry its defining counit equation to derived categories;
exact-functor factorization identifies $Rh_{\tau,*}$ with termwise $h_{\tau,*}$. Consequently the
descended $\delta_h^0$ is the unique transpose defining $\delta_h$ in [lem-weil-pbc-comparison-
direct-image-canonical-mate]. Thus the named derived comparison equals the termwise sheaf mate on
$D^+$. Its sheaf counit equation is $$\varepsilon^p_{h,C
L}\,h_p^*(\delta^0_{h,L})\,a_{h,h_{e,*}L}=C(\varepsilon^e_{h,L}).$$ Both closed restriction
counits are invertible by [lem-kun-04ca, lem-weil-pbc-proetale-ringed-open-closed]. The equation
therefore says precisely that restriction of $\delta_h$ to the closed source is the identity
under those counits and the specified $a_h$. This normalization holds termwise on complexes. The
open comparison has the analogous normalization by Step 2.

9. Write $E_\tau=i_{\tau,*}u_{\tau,!}$ for the closure compactification and
$q_\tau:F_\tau\xrightarrow{\sim}E_\tau$ for Step 7's identifications, restricting to the identity
on $S$. For $L\in D^+(S_{et},A)$ the closure comparison is $$C_{\bar
s,L}=i_{p,*}(o_{u,L})\,\delta_{i,u_{e,!}L}:C_TE_eL\xrightarrow{\sim}E_pC_SL.$$ This is exactly
the specified $B_{s,L}$ in [lem-pur-bounded-site-adjunction-transpose], for compactification
$(u,i)$: the proper comparison there is the counit-mate comparison for the closed $i$. Exactness
identifies its derived direct image with $i_*$. Define $$D_L=q_{p,C_SL}^{-1}\,C_{\bar
s,L}\,C_T(q_{e,L}):C_TF_eL\longrightarrow F_pC_SL.$$ Step 8 and the open unit normalization show
that both $D_L$ and $\Delta_L$ restrict to $1_{C_SL}$: each closed factor restricts by its
counit, each open factor by its unit, and each $q_\tau$ by its stated identity normalization. The
pullback-composition compatibility of [lem-weil-pbc-comparison-pullback] ensures these use the
same identification $s_p^*C_T\cong C_Ss_e^*$ for both factorizations. Hence the endomorphism
$D_L\Delta_L^{-1}$ of $F_pC_SL$ restricts to the identity. The restriction Hom bijection of [lem-
sfb-locally-closed-extension-coherence], with both arguments $C_SL$, makes this endomorphism the
identity. We have proved the required equality of named maps: $$q_{p,C_SL}\,\Delta_L=C_{\bar
s,L}\,C_T(q_{e,L}).$$

10. Now compute the specified comparison-class transpose. Choose a nonnegative dimension bound
for $\bar S$ by [lem-kun-dimension-finite-type], using $0$ if it is empty. Apply [lem-pur-
bounded-site-adjunction-transpose] to $f=s$, compactification $(u,i)$ and $K=M$. Its hypotheses
hold: these are finite-type $k$-schemes with the same finite coefficient $A$, $s$ is separated
finite type, $M\in D^+$, and $s^\times M$ is bounded below by Steps 1 and 7. Put $B=J_eM$ and
write $$\rho_M=C_S\bigl(s^\times(\eta_M)\bigr)$$ under Step 7's counit-compatible $J_e\cong
s^\times$. For $L\in D^+(S_{et},A)$ and $h:F_pC_SL\to C_TM$, full faithfulness of $C_T$ gives a
unique $h_0:F_eL\to M$ with $h\Delta_L=C_T(h_0)$; $F_eL$ is bounded below by exactness. Let
$g_0:L\to B$ be its etale adjoint. Step 6 and naturality of $\Delta$ give
$$\epsilon^p_{C_TM}F_p(\gamma_MC_Sg_0)=C_T(h_0)\Delta_L^{-1}=h.$$ Thus the ambient transpose of
$h$ is $\gamma_MC_Sg_0$. For closure left adjoints take $a_e=h_0q_{e,L}^{-1}$ and
$a_p=hq_{p,C_SL}^{-1}$. Step 9 gives $$a_pC_{\bar s,L}=C_T(a_e).$$ Use the current statement's
explicit Hom formula with $U_T=R\nu_{T,*}$ and the same closure compactification. Naturality of
the comparison unit gives $$U_T(a_pC_{\bar
s,L})\eta_{T,E_eL}=U_TC_T(a_e)\eta_{T,E_eL}=\eta_Ma_e.$$ Its etale transpose is
$s^\times(\eta_M)\operatorname{adj}_e(a_e)$. Conjugation by $q_e$ identifies
$\operatorname{adj}_e(a_e)$ with $g_0$. Applying $C_S$ in the specified Hom formula therefore
gives exactly $\rho_MC_Sg_0$. Thus both the explicit Hom formula and the cited transpose
conclusion use the comparison unit and the named $B_{s,L}=C_{\bar s,L}$ of Step 9.

11. Since $\eta_M:M\xrightarrow{\sim}R\nu_{T,*}C_TM$ is invertible, define
$$\theta_M=C_S\bigl(s^\times(\eta_M)\bigr)\gamma_M^{-1}:J_pC_TM\xrightarrow{\sim}C_Ss^\times
R\nu_{T,*}C_TM=G_s(C_TM),$$ with Step 7's adjoint identification understood. Step 10 proves that
postcomposition by $\theta_M$ identifies the two Hom bijections. An arbitrary bounded-below
etale-origin test object is isomorphic to $C_SL$; precomposing by this witness proves the same
assertion for it, independently of the witness, as in [thm-sf-ambient-adjoint-class]. In
particular the composite from $C_SJ_eM$ to the transported value is exactly $C_Ss^\times(\eta_M)$
under Step 7, as claimed. The unit is the image of the identity of a left-adjoint value under its
Hom bijection, and the counit is the inverse image of an identity of a right-adjoint value
wherever that comparison-class map is defined. Equality of the Hom bijections therefore
identifies these maps. The ambient $F_\tau\dashv J_\tau$ units and counits are the pasted ones by
the composite adjunction formula. This argument does not assert a compact-support adjunction on
arbitrary pro-etale objects.

12. Finally change the closed-then-open factorization. The normalized etale factorization maps
are given by [lem-sfb-etale-locally-closed-extension-comparison], and the pro-etale maps by [lem-
sfb-locally-closed-extension-coherence]. For any second factorization repeat Steps 8-9 with the
same closure $(u,i)$. Each site's $q_\tau$ restricts to the identity, and its closed/open
comparison is termwise with the specified normalization, so the same restriction Hom bijection
gives $$q'_{p}\Delta'=C_{\bar s}C_T(q'_e),\qquad q_p\Delta=C_{\bar s}C_T(q_e).$$ Cancelling the
common closure map proves equality of the comparison paths after the canonical factorization
identifications. No derived mate is being presumed to be a sheaf map: Step 8 established that
equality before using it here. Conjugation of the normalized left-adjoint identifications gives
canonical right-adjoint identifications, respecting identities and composition [def-weil-pbc-
adjunction-conjugate]. Step 6 uniquely characterizes $\gamma_M$ as a counit transpose, so it
respects these identifications. Their units and counits are the pasted ones by [lem-cat-right-
adjoint-composition, def-weil-pbc-composite-adjunction]. Step 11's transported identification has
the same coherence, since it is the image of the natural comparison unit under the normalized
etale right adjoints followed by $C_S$. This proves independence of the factorization for the
maps and adjunction data on the stated comparison class.
-/
theorem finiteDuality_locallyClosed_comparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {S V T : Scheme.{u}}
    (aS : S ⟶ Spec (.of D.k)) (aT : T ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (_hs : (c ≫ v) ≫ aT = aS) :
    ∃ hT : IsNoetherian T, ∃ hqc : QuasiCompact (c ≫ v),
      Nonempty (@LocallyClosedExceptionalComparison
        (Padic.coefficientExtensionRing l E (n + 1)) inferInstance
        (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
        S V T c v inferInstance inferInstance hT hqc) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have : IsNoetherian T := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aT
    __ := QuasiCompact.compactSpace_of_compactSpace aT }
  have : IsNoetherian S := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aS
    __ := QuasiCompact.compactSpace_of_compactSpace aS }
  have : QuasiCompact (c ≫ v) := inferInstance
  let W : V.Opens := ⟨(Set.range c)ᶜ,
    (IsClosedImmersion.isClosedEmbedding c).isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace V := v.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace W := W.ι.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := inferInstance
  have hij : IsCompl (Set.range c) (Set.range W.ι) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  let a : LocallyClosedComparisonAdjoints A c := {
    etale := (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.rightAdjoint
    proetale := (closedUpperShriek (ModuleCat.{u + 1} A) c W.ι).rightDerivedFunctor
    etaleAdjunction := Adjunction.ofIsLeftAdjoint _
    proetaleAdjunction := derivedLowerStarClosedUpperShriekAdjunction c W.ι hij }
  have bounded (M : Etale.BoundedConstructibleDerivedCategory A T) :
      _root_.DerivedCategory.TStructure.t.plus ((a.etaleRight v).obj M.obj) := by
    obtain ⟨k, b, hkb, hz⟩ := M.property.2
    have : M.obj.IsGE k :=
      (_root_.DerivedCategory.isGE_iff M.obj k).2 (fun i hi ↦ hz i (.inl hi))
    have : ((Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj M.obj).IsGE k :=
      Functor.isGE_mapDerivedCategory_obj _ M.obj k
    refine ⟨k, ?_⟩
    exact exactDerivedAdjunction_isGE (Etale.lowerStar (ModuleCat.{u + 1} A) c)
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory |>
        Functor.isoWhiskerLeft DerivedCategory.Q |>.trans
          (Etale.lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryFactors)
      a.etaleAdjunction _ k
  let g := locallyClosedCounitMate A c v a bounded
  have (M : Etale.BoundedConstructibleDerivedCategory A T) : IsIso (g.app M) :=
    locallyClosedCounitMate_isIso D l _hl E n aS aT c v _hs a bounded M
  have : IsIso g := NatIso.isIso_of_isIso_app g
  let gamma := asIso g
  have hc (M : Etale.BoundedConstructibleDerivedCategory A T) :
      (locallyClosedExtensionComparison A c v).hom.app
          ⟨(a.etaleRight v).obj M.obj, bounded M⟩ ≫
        (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
          (a.proetalePasted v).counit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        ((a.etalePasted v).counit.app M.obj) := by
    have h := ((a.proetalePasted v).homEquiv _ _).symm_apply_apply
      ((locallyClosedExtensionComparison A c v).inv.app
          ⟨(a.etaleRight v).obj M.obj, bounded M⟩ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
          ((a.etalePasted v).counit.app M.obj))
    rw [Adjunction.homEquiv_counit] at h
    change _ ≫ ((locallyClosedProEtaleExtension A c v).map _ ≫ _) = _
    erw [show (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
        (a.proetalePasted v).counit.app _ = _ from h]
    simp
  let CS := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
  let CT := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let U := (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor
  let X := locallyClosedEtaleExceptional A (c ≫ v)
  let r := locallyClosedEtaleRightIso v a
  let eta := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit
  let rho : (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ a.etaleRight v ⋙ CS ⟶
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ CT ⋙ U ⋙ X ⋙ CS := {
    app M := CS.map (r.hom.app M.obj ≫ X.map (eta.app M.obj))
    naturality M N f := by
      have hr := r.hom.naturality f.hom
      change (a.etaleRight v).map f.hom ≫ r.hom.app N.obj =
        r.hom.app M.obj ≫ X.map f.hom at hr
      have he := eta.naturality f.hom
      change f.hom ≫ eta.app N.obj = eta.app M.obj ≫ U.map (CT.map f.hom) at he
      change CS.map ((a.etaleRight v).map f.hom) ≫
        CS.map (r.hom.app N.obj ≫ X.map (eta.app N.obj)) =
          CS.map (r.hom.app M.obj ≫ X.map (eta.app M.obj)) ≫
            CS.map (X.map (U.map (CT.map f.hom)))
      rw [← CS.map_comp, ← CS.map_comp]
      congr 1
      rw [← Category.assoc, hr, Category.assoc, ← X.map_comp, he,
        X.map_comp, Category.assoc] }
  have hrho (M : Etale.BoundedConstructibleDerivedCategory A T) : IsIso (rho.app M) := by
    obtain ⟨k, b, hkb, hz⟩ := M.property.2
    have hM : _root_.DerivedCategory.TStructure.t.plus M.obj :=
      ⟨k, (_root_.DerivedCategory.isGE_iff M.obj k).2 (fun i hi ↦ hz i (.inl hi))⟩
    have : IsIso (eta.app M.obj) :=
      isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) T M.obj hM
    dsimp [rho]
    infer_instance
  have : IsIso rho := NatIso.isIso_of_isIso_app rho
  let theta := gamma.symm ≪≫ asIso rho
  refine ⟨inferInstance, inferInstance, ⟨{
    adjoints := a
    bounded := bounded
    gamma := gamma
    counit := hc
    transport := theta
    unit_normalization := ?_
    relative_hom := ?_ }⟩⟩
  · intro M
    change gamma.hom.app M ≫ (gamma.inv.app M ≫ rho.app M) = rho.app M
    simp
  · exact locallyClosedRelativeHomIdentity A c v a bounded gamma hc


private theorem normalizedComparison_unique
    {C₁ C₂ C₃ C₄ B : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category B]
    (ι : B ⥤ C₁) (CS : C₂ ⥤ C₄) (CT : C₁ ⥤ C₃) (U : C₃ ⥤ C₁)
    (η : 𝟭 C₁ ⟶ CT ⋙ U)
    (J J' X X' : C₁ ⥤ C₂) (P P' : C₃ ⥤ C₄) (hX : X = X')
    (r : J ≅ X) (r' : J' ≅ X')
    (γ : ι ⋙ J ⋙ CS ≅ ι ⋙ CT ⋙ P)
    (γ' : ι ⋙ J' ⋙ CS ≅ ι ⋙ CT ⋙ P')
    (θ : ι ⋙ CT ⋙ P ≅ ι ⋙ CT ⋙ U ⋙ X ⋙ CS)
    (θ' : ι ⋙ CT ⋙ P' ≅ ι ⋙ CT ⋙ U ⋙ X' ⋙ CS)
    (h : ∀ M, γ.hom.app M ≫ θ.hom.app M =
      CS.map (r.hom.app (ι.obj M) ≫ X.map (η.app (ι.obj M))))
    (h' : ∀ M, γ'.hom.app M ≫ θ'.hom.app M =
      CS.map (r'.hom.app (ι.obj M) ≫ X'.map (η.app (ι.obj M)))) :
    ∃! e : (J ≅ J') × (ι ⋙ CT ⋙ P ≅ ι ⋙ CT ⋙ P'),
      HEq (e.1 ≪≫ r') r ∧ HEq (e.2 ≪≫ θ') θ ∧
        ∀ M, CS.map (e.1.hom.app (ι.obj M)) ≫ γ'.hom.app M =
          γ.hom.app M ≫ e.2.hom.app M := by
  subst X'
  -- Both comparisons factor through the common normalized values.
  refine ⟨(r ≪≫ r'.symm, θ ≪≫ θ'.symm), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp
    · simp
    · intro M
      -- The two unit equations reduce the gamma square to inverse cancellation.
      apply (cancel_mono (θ'.hom.app M)).1
      simp only [Category.assoc, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Iso.inv_hom_id_app, Category.comp_id]
      rw [h', h]
      rw [← CS.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  · intro e he
    apply Prod.ext
    · apply Iso.ext
      apply (cancel_mono r'.hom).1
      simpa using congrArg Iso.hom (eq_of_heq he.1)
    · apply Iso.ext
      apply (cancel_mono θ'.hom).1
      simpa using congrArg Iso.hom (eq_of_heq he.2.1)

/-- The normalized comparisons between two closed/open factorizations are unique.
Consequently identity comparisons and composition comparisons satisfy the cocycle law.
`HEq` expresses equality after the equality of the two composite scheme morphisms;
it does not introduce an independently chosen identification of the transported functors.
The first equation fixes the etale map by counit-compatible adjoint uniqueness, the second
fixes the pro-etale map by the transported value, and the last is the gamma square.
Source: blueprint locally closed exceptional comparison, Step 12
(blueprint: lem-weil-finite-duality-locally-closed-comparison).

Proof: identify both left adjoints with closure extension by the unique sheaf maps
restricting to the identity on S. Their localizations have the same normalization.
Step 8 identifies the named derived closed mate with its termwise sheaf mate. The open
unit equation and the restriction Hom bijection of locally closed extension coherence
then give q_p Delta = B C(q_e) for each factorization (Step 9). Transport the normalized
left-adjoint identification by right-adjoint uniqueness to obtain the etale isomorphism.
The counit equation uniquely characterizes gamma as a transpose, hence gives its square.
The formula gamma theta = C(s-times(eta)) gives the transported-value square. Each of the
first two normalizations uniquely determines its isomorphism by cancellation; thus the
identity and composites are the same normalized maps. This is exactly Step 12, using
lem-sfb-etale-locally-closed-extension-comparison, lem-sfb-locally-closed-extension-coherence,
def-weil-pbc-adjunction-conjugate, lem-cat-right-adjoint-composition,
def-weil-pbc-composite-adjunction and thm-weil-pbc-site-comparison. -/
theorem locallyClosed_comparison_factorization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V V' T : Scheme.{u}} [IsNoetherian T]
    (c : S ⟶ V) (v : V ⟶ T) (c' : S ⟶ V') (v' : V' ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v]
    [IsClosedImmersion c'] [IsOpenImmersion v']
    [QuasiCompact (c ≫ v)] [QuasiCompact (c' ≫ v')]
    (_hs : c ≫ v = c' ≫ v')
    (z : LocallyClosedExceptionalComparison A c v)
    (z' : LocallyClosedExceptionalComparison A c' v') :
    ∃! e : (z.adjoints.etaleRight v ≅ z'.adjoints.etaleRight v') ×
        ((Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
            z.adjoints.proetaleRight v ≅
          (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
            z'.adjoints.proetaleRight v'),
      HEq (e.1 ≪≫ locallyClosedEtaleRightIso v' z'.adjoints)
          (locallyClosedEtaleRightIso v z.adjoints) ∧
        HEq (e.2 ≪≫ z'.transport) z.transport ∧
        ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
          (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
              (e.1.hom.app M.obj) ≫ z'.gamma.hom.app M =
            z.gamma.hom.app M ≫ e.2.hom.app M := by
  let CS := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
  let CT := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let U := (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor
  let X := locallyClosedEtaleExceptional A (c ≫ v)
  let X' := locallyClosedEtaleExceptional A (c' ≫ v')
  -- Package the proof-valued instances so congruence identifies the closure functors.
  let exceptional (s : {f : S ⟶ T // IsImmersion f ∧ QuasiCompact f}) :=
    @locallyClosedEtaleExceptional A _ _ S T s.val s.property.1 s.property.2 _
  have hsub : (⟨c ≫ v, inferInstance, inferInstance⟩ :
      {f : S ⟶ T // IsImmersion f ∧ QuasiCompact f}) =
      ⟨c' ≫ v', inferInstance, inferInstance⟩ := Subtype.ext _hs
  have hX := congrArg exceptional hsub
  change X = X' at hX
  exact normalizedComparison_unique
    (Etale.DerivedCategory.isBoundedConstructible A T).ι CS CT U
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit
    (z.adjoints.etaleRight v) (z'.adjoints.etaleRight v') X X'
    (z.adjoints.proetaleRight v) (z'.adjoints.proetaleRight v') hX
    (locallyClosedEtaleRightIso v z.adjoints)
    (locallyClosedEtaleRightIso v' z'.adjoints)
    z.gamma z'.gamma z.transport z'.transport z.unit_normalization z'.unit_normalization

end AlgebraicGeometry.ProEtale
