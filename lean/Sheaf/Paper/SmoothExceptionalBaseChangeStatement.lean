/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

import Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Compactification.BaseChange
import Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange

/-! # Smooth base change for the finite-level exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-smb-extraordinary.md and its proof (blueprint: lem-pur-smb-extraordinary).

The exceptional functors are the recorded finite-level composites ν^* f× Rν_*.
The canonical arrow is pasted from the comparison-site mate and the ordinary etale
exceptional mate. No right adjoint on the ambient pro-etale category is assumed.

## Main declarations

- `smoothExceptionalComparisonMate`: the unit-square-counit comparison-site mate.
- `smoothExceptionalProEtaleBaseChangeMap`: the canonical exceptional comparison.
- `smoothExceptionalBaseChangeStatement`: its invertibility on Dᵇ_ctf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale
open Scheme

/-- Finiteness at the positive coefficient level of the fixed purity setting.
Source: blueprint main-20261015, def-pur-conventions, finite-stage convention;
lem-pur-smb-extraordinary, proof opening (blueprint: lem-pur-smb-extraordinary). -/
noncomputable instance smoothExceptionalCoefficientFinite
    (P : WeilConjectures.PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The canonical comparison v_e^* Rν_Y,* → Rν_Y',* v_p^*.
This is the mate of the inverse comparison-pullback square: first the comparison
unit, then Rν_* of that square, and finally Rν_* of the pulled-back counit.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md, comparison
of actual adjoints and transport of counits (blueprint: lem-pur-smb-extraordinary). -/
noncomputable def smoothExceptionalComparisonMate (A : Type u) [CommRing A]
    {U V : Scheme.{u}} (v : U ⟶ V)
    (K : DerivedCategory
      (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) v).mapDerivedCategory.obj
        ((comparisonLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V).rightDerivedFunctor.obj K) ⟶
      (comparisonLowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).rightDerivedFunctor.obj
          ((sfFixedDerivedPullback A v).obj K) :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).unit.app _ ≫
    (comparisonLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).rightDerivedFunctor.map
        ((sfDerivedComparisonPullbackIso A v).inv.app _ ≫
          (sfFixedDerivedPullback A v).map
            ((derivedComparisonAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V).counit.app K))

/-- The specified comparison Lu^* Rf^! K → Rf'^! Lv^* K, in canonical fixed-scalar
coordinates. Its factors are the comparison-pullback square, the ordinary etale
exceptional counit-transpose, and f'^× applied to the comparison-site mate.
The target compactification is the base change of c. Quasi-compactness of f'
is derived from the Cartesian square, so v is arbitrary.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md, transport
of the specified canonical map (blueprint: lem-pur-smb-extraordinary). -/
noncomputable def smoothExceptionalProEtaleBaseChangeMap
    (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {v : Y' ⟶ Y}
    (sq : IsPullback u' f' f v) [QuasiCompact f] (c : Compactification f)
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfFixedDerivedPullback A u').obj ((sfFiniteExceptionalFixed A c).obj K) ⟶
      (sfFiniteExceptionalFixed A (c.ofIsPullback sq)).obj
        ((sfFixedDerivedPullback A v).obj K) :=
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  letI := c.hasCompactification
  letI := (c.ofIsPullback sq).hasCompactification
  (sfDerivedComparisonPullbackIso A u').hom.app
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj
        ((comparisonLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).rightDerivedFunctor.obj K)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X').mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ u').inv.app _ ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap (ULift.{u + 1, u} A) sq).app
          ((comparisonLowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).rightDerivedFunctor.obj K) ≫
        (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ v).hom.app _ ≫
            smoothExceptionalComparisonMate A v K))

/-- Smooth arbitrary base change for the canonical finite-level exceptional comparison.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-smb-extraordinary.md and its proof (blueprint: lem-pur-smb-extraordinary).

Proof, following the unchanged DAG steps:

1. Work at the finite stage $\Lambda=A=A_{E,n}=\mathcal O_E/\varpi_E^n$, with $n\geq1$ and
$\ell\ne p$, as stipulated in the current [def-pur-conventions]. Its finite-coefficient clause
makes the constructions here finite-level ones; the integral, rational and algebraically closed
versions are separate coefficient transports. Its functor clause specifies separated finite-type
$k$-morphisms between finite-type $k$-schemes and refers to [def-weil-exceptional-inverse-image]
for the actual functor and adjunction domains. The latter definition has precisely this standing
domain, with $k$ the fixed algebraic closure of the finite field. We use those domains, without
taking any preservation or invertibility assertion from the conventions definition. Thus all four
schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since a field is Noetherian.
Choose a compactification $c=(j,p)$ used in that construction for $f$, and use its base change
$c'=(j',p')$ for $f'$, as in [def-cbc-compact-support-square]. This definition states that $c'$ is
a compactification. The compactification comparisons and their compatibility with the Hom
bijections in [thm-sf-ambient-adjoint-class], clause (3), identify these choices with those in the
exceptional functors. Their total spaces are finite type over $k$: the proper part is of finite
type, and finite generating sets for two successive algebra extensions generate the composite.
Their dimensions therefore have finite bounds by [lem-kun-dimension-finite-type], as required by
[thm-sf-ambient-adjoint-class]. Clause (1) of [lem-sbc-smooth-relative-dimension-permanence] gives
that $f'$ is smooth of pure relative dimension $d$. The class-restricted adjunctions in [cor-sf-
ambient-adjoint-discharge] consequently apply to the coefficients here; no unrestricted pro-etale
adjoint datum is being used.
Uses: def-pur-conventions, def-weil-exceptional-inverse-image, lem-weil-pbc-finite-type-over-
noetherian, lem-kun-dimension-finite-type, lem-sbc-smooth-relative-dimension-permanence, thm-sf-
ambient-adjoint-class, cor-sf-ambient-adjoint-discharge, def-cbc-compact-support-square.

2. Write $C_T=\nu_T^*$. Since $K$ is bounded constructible, clause (ii) of [lem-sf-proetale-
constructible-origin] supplies $G\in D^b_c(Y_{\mathrm{et}},A)$ and
$\alpha:C_YG\xrightarrow{\sim}K$. Ordinary etale inverse images $v_e^*$ and $u_e^*$ are exact by
[prop-weil-pbc-inverse-image-modules-exact], so they preserve every cohomological lower bound; in
particular $v_e^*G$ is bounded below. At finite constant coefficients, [def-weil-derived-pullback-
tensor-hom] computes pro-etale derived pullback termwise by inverse image. Apply [lem-weil-pbc-
comparison-pullback] termwise: it gives $C_{Y'}v_e^*G\cong Lv^*C_YG\cong Lv^*K$, naturally in $G$,
and gives $Lu^*C_XM\cong C_{X'}u_e^*M$ for every bounded-below etale complex $M$. These
comparisons respect the chosen Cartesian square, as stated in that lemma.
Uses: lem-sf-proetale-constructible-origin, prop-weil-pbc-inverse-image-modules-exact, def-weil-
derived-pullback-tensor-hom, lem-weil-pbc-comparison-pullback.

3. The natural unit isomorphism $G\xrightarrow{\sim}R\nu_{Y,*}C_YG$ of [thm-weil-pbc-site-
comparison], together with $\alpha$, identifies $R\nu_{Y,*}K$ with $G$. Put $M=f^\times G$. The
finite formula in [def-weil-exceptional-inverse-image] therefore gives $Rf^!K\cong C_XM$. Put
$M'=f'^\times v_e^*G$. Applying the same defining finite formula to the representative $v_e^*G$
and its unit $v_e^*G\xrightarrow{\sim}R\nu_{Y',*}C_{Y'}v_e^*G$ gives $Rf'^!Lv^*K\cong C_{X'}M'$.
Clause (2) of [thm-sf-ambient-adjoint-class] says that the transported composite $R_c$ preserves
bounded-below objects. Hence $C_XM\cong R_cK$ is bounded below. To infer the same for $M$, use
[lem-sf-comparison-pullback-exact]: $\mathcal H^i(C_XM)=C_X\mathcal H^i(M)$. Below a lower bound
the left side is zero. For the degree-zero sheaf $H=\mathcal H^i(M)$, faithfulness of $C_X$ on
$D^+$ implies $1_H=0$, since its image is the identity of the zero object. Thus $H=0$, and $M$ is
bounded below. For $M'$, clause (2) applied to $Lv^*K\cong C_{Y'}v_e^*G$ gives a lower bound for
$C_{X'}M'$. Exactness gives $\mathcal H^i(C_{X'}M')=C_{X'}\mathcal H^i(M')$; in degrees below that
bound, faithfulness on the degree-zero sheaf again gives $1_{\mathcal H^i(M')}=0$. Hence $M'$ is
bounded below as well. This verifies the $D^+$ domains rather than attributing preservation by
$f^\times$ itself directly to the statement of the class theorem. Combining these identifications
with step 2 gives
$$Lu^*Rf^!K\cong C_{X'}u_e^*f^\times G,\qquad Rf'^!Lv^*K\cong C_{X'}f'^\times
v_e^*G.$$
Uses: thm-weil-pbc-site-comparison, def-weil-exceptional-inverse-image, thm-sf-ambient-adjoint-
class, lem-sf-comparison-pullback-exact.

4. Apply [prop-asd-smooth-base-change] to the ordinary etale complex $G$ and the given square. Its
hypotheses are met: $A$ is finite and killed by a power of $\ell$ invertible on all the schemes,
$f$ is smooth separated of pure relative dimension $d$ and has the compactification used above,
and $v$ is a morphism of Noetherian schemes. It supplies the specific isomorphism
$\beta^e:u_e^*f^\times G\xrightarrow{\sim}f'^\times v_e^*G$, defined as the transpose of
$v_e^*\varepsilon^e_G\circ(\operatorname{Ex}_!^e(M))^{-1}$. Denote by $\gamma$ the conjugate of
$C_{X'}\beta^e$ under the two identifications of step 3. We next identify $\gamma$ with the
canonical comparison in the statement.
Uses: prop-asd-smooth-base-change.

5. Let $F_f^e=Rf_!^{\mathrm{et}}$ and $F_f^p=Rf_!^{\mathrm{proet}}$. Denote the natural comparison
of [lem-sf-class-compact-support-comparison] by $a_f:F_f^pC_X\xrightarrow{\sim}C_YF_f^e$,
evaluated on bounded-below etale complexes, and denote the comparison for the base-changed
compactification by $a_{f'}:F_{f'}^pC_{X'}\xrightarrow{\sim}C_{Y'}F_{f'}^e$. With the
identifications of step 3 understood, the pro-etale counit on $K=C_YG$ is
$$\varepsilon^p_K=C_Y(\varepsilon^e_G)\circ a_f(M).$$
Indeed the bounded-class Hom bijection of
[thm-sf-ambient-adjoint-class] is the etale adjunction transported through the compact-support
comparison and the fully faithful $C_T$, as specified in [def-weil-exceptional-inverse-image]. The
identity of $C_Xf^\times G$ corresponds to the identity of $f^\times G$, whose etale transpose is
$\varepsilon^e_G$; substituting the comparison $a_f$ gives exactly this formula. For $f'$, the
identity of $C_{X'}M'$ corresponds to $1_{M'}$ and then to the etale counit
$\varepsilon^{e,f'}_{v_e^*G}$, so
$\varepsilon^{p,f'}_{Lv^*K}=C_{Y'}(\varepsilon^{e,f'}_{v_e^*G})\circ a_{f'}(M')$. This is a
calculation with the defining adjunction bijections, not an assertion of an adjunction on all pro-
etale objects.
Uses: lem-sf-class-compact-support-comparison, thm-sf-ambient-adjoint-class, def-weil-exceptional-
inverse-image.

6. Let $t=\operatorname{Ex}_!^p(C_XM):Lv^*F_f^pC_XM\xrightarrow{\sim}F_{f'}^pLu^*C_XM$. The
theorem [thm-cbc-finite-level-proetale] says that this is the transported finite compact-support
exchange of [def-cbc-exchange-map], and is invertible on the etale-origin bounded-below input
$C_XM$. For the proper parts $p,p'$ of the chosen compactifications, [lem-weil-pbc-transport-
identifies-exchange] identifies the direct-image unit--square--counit exchange with its etale
counterpart. Its quasi-compact and quasi-separated hypotheses hold because these maps are proper.
The compactification formula of [def-cbc-exchange-map] composes that exchange with the specified
extension-by-zero identification; [thm-cbc-finite-level-proetale] states that this whole composite
is transported to the pro-etale exchange. Consequently its comparison with the etale compact-
support exchange is, after the pullback identifications of [lem-weil-pbc-comparison-pullback],
$$a_{f'}(u_e^*M)\circ t=C_{Y'}(\operatorname{Ex}_!^e(M))\circ Lv^*a_f(M).$$
Substitute this
equation and the counit formula of step 5 into the defining transpose of the exceptional
comparison:
$$F_{f'}^pLu^*Rf^!K\xrightarrow{t^{-1}}Lv^*F_f^pRf^!K\xrightarrow{Lv^*\varepsilon^p_K}Lv^*K.$$
Under $a_{f'}$ this composite is exactly
$C_{Y'}\bigl(v_e^*\varepsilon^e_G\circ(\operatorname{Ex}_!^e(M))^{-1}\bigr)$: explicitly, invert
the displayed exchange equation to obtain $Lv^*a_f(M)\circ
t^{-1}=(C_{Y'}\operatorname{Ex}_!^e(M))^{-1}\circ a_{f'}(u_e^*M)$, and cancel the adjacent
comparison isomorphisms. By [prop-asd-smooth-base-change] the resulting etale arrow is the
transpose of $\beta^e$. Here its source input $Lu^*Rf^!K\cong C_{X'}u_e^*M$ is bounded below and
of etale origin by steps 2-3, and its target $Lv^*K$ is bounded below. The transported adjunction
bijection of [thm-sf-ambient-adjoint-class] therefore applies and sends both the canonical
comparison and $\gamma$ to the very same arrow. Injectivity of that bijection proves equality of
the two morphisms. The witness $\alpha$ can be reinserted on both sides by naturality;
independence of isomorphic witnesses is part of the cited compact-support and adjunction
comparisons.
Uses: thm-cbc-finite-level-proetale, def-cbc-exchange-map, lem-weil-pbc-comparison-pullback, lem-
weil-pbc-transport-identifies-exchange, prop-asd-smooth-base-change, thm-sf-ambient-adjoint-class.

7. A functor carries an inverse pair of arrows to an inverse pair. Thus $C_{X'}\beta^e$ is
invertible, and so is its conjugate $\gamma$. Step 6 identifies this conjugate with the canonical
comparison, proving the assertion. None of the steps imposes smoothness or properness on $v$; its
only restrictions are the standing schemes and coefficient domain. The same computation covers
$d=0$, $K=0$, $v$ an identity, and empty source or base, since it uses functors, their natural
isomorphisms, and adjunction bijections without choosing a point or a nonempty cover.
Uses: .
-/
theorem smoothExceptionalBaseChangeStatement
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of P.field.k))]
    [X.Over (Spec (CommRingCat.of P.field.k))]
    [Y'.Over (Spec (CommRingCat.of P.field.k))]
    [Y.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    [u'.IsOver (Spec (CommRingCat.of P.field.k))]
    [f'.IsOver (Spec (CommRingCat.of P.field.k))]
    [f.IsOver (Spec (CommRingCat.of P.field.k))]
    [v.IsOver (Spec (CommRingCat.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : ChosenCartesianSquare u' f' f v)
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f)
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} P.Ring))))
    (_hK : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos Y K) :
    SmoothOfRelativeDimension d f' ∧
      IsIso (smoothExceptionalProEtaleBaseChangeMap P.Ring
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd) c K) := by
  sorry

end AlgebraicGeometry.ProEtale
