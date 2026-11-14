/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.NativeBaseChange.NativeBaseChangeForgetComparison
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison

/-!
# Natural proper base change in the native derived Weil categories

Source: blueprint sec-six-functors-basics/sk-thm-sfb-proper-base-change,
thm-weil-pbc-qbar.proof.md, "Forgetting the Weil structure" and
"Constructibility and the isomorphism".
(blueprint: lem-sf-native-weil-proper-natural-base-change)

The source is the full bounded constructible subcategory of the ordinary derived
category of native Weil modules. The target is the ambient native equivariant
derived category. All operations are the recorded actual equivariant operations.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Natural proper base change for the native ordinary derived Weil categories.

Source: blueprint sec-six-functors-basics/sk-thm-sfb-proper-base-change,
thm-weil-pbc-qbar.proof.md, "Forgetting the Weil structure" and
"Constructibility and the isomorphism".
(blueprint: lem-sf-native-weil-proper-natural-base-change)

Proof: construct the canonical native mate using the existing derived adjunctions.
The theorem `NativeBaseChange.forget_mate` identifies its image under exact forgetting
with the geometric mate conjugated by the canonical source and target comparisons.
Exact forgetting preserves boundedness, and its homology comparison transfers native
constructibility. Apply `NativeBaseChange.geometric_proper_baseChange_isIso` to this
forgotten input and reflect invertibility using `fixedPair_forget_properties`.
Whisker the resulting componentwise invertible natural transformation by the full
bounded constructible inclusion, and take `asIso`.

Expanded proof of the two named intermediate steps:

1. Write $U_S:\mathcal W_S\to\mathcal A_{\bar S}$ for forgetting, and $E_S$ for the native-to-
condensed module encoding. For every scheme, not just separated ones, [lem-sf-native-adic-
encoding-ordinary-operations] supplies the exact equivalence $E_S$, its derived equivalence, and
comparisons with ordinary pullback and pushforward. The native module pullbacks are exact by
[lem-sf-native-adic-pullback-exact-lisse]. The module categories are Grothendieck by the ringed-
site theorem, transported along $E_S$. Frobenius is an exact autoequivalence: it is pullback
along the scheme isomorphism $F_S$, with inverse pullback along $F_S^{-1}$ and the inverse-image
composition comparisons. Apply the general fixed-pair forgetting theorem. Thus $\mathcal W_S$ is
Grothendieck, $U_S$ is exact, preserves K-injectives, and $D(U_S)$ is conservative. Its
comparison with each $Rh_*$ is the canonical one computed on the same K-injective resolution.
These assertions apply simultaneously to $Z,Z',T,T'$; they require no absolute separatedness.
Dependencies: lem-sf-native-adic-encoding-ordinary-operations, lem-sf-native-adic-pullback-
exact-lisse, lem-pur-ringed-site-grothendieck-abelian, lem-sf-fixed-pair-derived-forget-
comparison.

2. For any map $h:S\to H$ of the square, the ordinary native module adjunction $L=\bar h^*\dashv
R=\bar h_*$ is the tensor-formula adjunction of [lem-weil-pbc-ringed-topoi-module-adjunction].
It lifts to the abelian fixed-pair categories by [lem-sf-fixed-pair-adjunction-lift]. Here its
required mate condition is checked before deriving: put $P_S=F_S^*$ and $P_H=F_H^*$. If
$e:P_SL\cong LP_H$ is the pullback composition comparison, the mate $b:P_HR\to RP_S$ has
component $R(P_S\varepsilon_M)R(e^{-1}_{RM})\eta_{P_HRM}$. Transposing this composite gives
$LP_HRM\xrightarrow{e^{-1}}P_SLRM\xrightarrow{P_S\varepsilon_M}P_SM$. The framework's direct-
image Frobenius comparison has exactly this transpose: on a site object both maps pull the same
section through $\bar hF_S=F_H\bar h$ and then evaluate the ordinary counit, with the same
precomposition coefficient action. Its inverse uses $F_H^{-1},F_S^{-1}$. Thus $b$ is the
specified invertible comparison. The lifted functors are the actual native $h^*,h_*$, and their
units and counits forget to the ordinary module ones.
Dependencies: def-sf-native-weil-derived-framework, lem-weil-pbc-ringed-topoi-module-adjunction,
lem-sf-fixed-pair-adjunction-lift, lem-sf-native-adic-pullback-exact-lisse.

3. Derive these adjunctions in the ordinary abelian categories. Grothendieck K-injective
resolutions and [lem-weil-pbc-kinjective-total-derived] give total right derived functors; the
left functors, being exact, derive termwise. The right derived functor is then defined at every
complex $K$ in the sense of [lem-pc-derived-adjoint-functors]: if $K\to I$ is a K-injective
resolution, every quasi-isomorphism $s:K\to K'$ is followed by a map $K'\to I$ in the homotopy
category whose composite with $s$ is $K\to I$, unique because $\operatorname{Hom}_{K}(-,I)$
inverts quasi-isomorphisms [lem-weil-pbc-kinjective-hom-derived], so $I$ is cofinal and the ind-
system is essentially constant with value $h_*I$; the exact left functors are defined termwise.
[lem-pc-derived-adjoint-functors] therefore gives $h^*\dashv Rh_*$. To check the maps as well as
the objects, apply [lem-kun-derived-adjoint-square-comparison] to the square of lifted and
ordinary adjunctions with $V=U_S,W=U_H$. Its underived adjunct condition is step 2. Its
additional right-derived hypothesis holds: postcomposing the K-injective model of $Rh_*$ with
exact $D(U_H)$ is the right-derived model of $U_Hh_*$, by [lem-sf-right-derived-from-adapted-
complexes]. Indeed every complex resolves to a K-injective, and a quasi-isomorphism between
K-injectives is a homotopy equivalence, so its image is invertible. The canonical comparison $b$
is the fixed-pair derived-forgetting isomorphism of step 1, normalized on this common
resolution. The square theorem now identifies the derived units and counits after forgetting.
Apply the same square theorem to the exact encoding equivalences $E_S,E_H$: their ordinary
comparisons respect adjuncts by the ordinary-operations encoding statement, and equivalences
preserve the K-injective computation. Consequently $V_S=D(E_S)D(U_S)$ carries the native derived
adjunction maps to the condensed module ones, without asserting faithfulness of $D(U_S)$.
Dependencies: prose-03-02, lem-weil-pbc-kinjective-total-derived, lem-pc-
derived-adjoint-functors, lem-kun-derived-adjoint-square-comparison, lem-sf-right-derived-from-
adapted-complexes, lem-sf-fixed-pair-derived-forget-comparison, lem-sf-native-adic-encoding-
ordinary-operations, lem-weil-pbc-kinjective-hom-derived.

4. Let $\theta:p'^*u^*\xrightarrow{\sim}v^*p^*$ be the pullback composition comparison of the
cartesian square. The comparisons commute with Frobenius already on sheaves: both composites are
pullback along the same $k_0$-map, and on coefficients both are precomposition of functions.
Apply them termwise. Define in $D(\mathcal W_{T'})$ the natural transformation $$\beta_K=Rp'_*(v
^*\varepsilon_{p,K})\,Rp'_*(\theta_{Rp_*K})\,\eta_{p',u^*Rp_*K}:u^*Rp_*K\longrightarrow
Rp'_*v^*K.$$ This is the unit--square--counit mate, so its naturality is a composition of
naturality squares, not a choice of objectwise isomorphisms. Step 3 and the coefficient
comparisons identify $V_{T'}(\beta_K)$ with the ordinary module square mate. Equivalently,
before encoding, it is the sectionwise ringed exchange of [lem-sf-ringed-restriction-exchange-
open-descent], with the actual inverse-image rings; these agree with $B$ by [lem-sf-native-adic-
pullback-exact-lisse]. No identification of a derived category with fixed pairs is used.
Dependencies: def-weil-pbc-adjunction-mate, def-sf-native-weil-derived-framework, lem-sf-native-
adic-pullback-exact-lisse, lem-sf-ringed-restriction-exchange-open-descent.

5. It remains to prove the underlying mate invertible. Work first with the native geometric
module exchange, forgetting Frobenius. Cover $T$ by affine opens $A$ and cover each $u^{-1}A$ by
affine opens $A'$ of $T'$. Since $T,T'$ are locally of finite type over the field, these affine
charts are finite type. The base changes $Z_A\to A$ and $Z'_{A'}\to A'$ are proper, hence
separated and finite type. Their sources are separated schemes by [lem-sc-separated-over-affine-
scheme-separated], and finite type over $k_0$ by finite-type composition; the targets are
separated finite type as well. Base change to $k$ preserves these conditions by [lem-pod-
separated-finite-type-base-change]. Thus each four-scheme geometric chart square satisfies the
standing separated finite-type hypotheses of rational proper base change. This does not assert
that intersections of affine opens in $T$ are affine, nor that $T$ or $T'$ is separated.
Properness is used only relatively, and no restriction on $u$ is added.
Dependencies: def-weil-proper-morphism, def-weil-finite-type-morphism, lem-weil-pbc-proper-base-
change, lem-sc-separated-over-affine-scheme-separated, lem-sfb-finite-type-composition-base-
change, lem-pod-separated-finite-type-base-change.

6. For $K\in\mathrm{WC}^{\mathrm{der}}(Z)$, let $N$ be its forgotten complex restricted to
$\overline{Z_A}$. Exact forgetting and exact restriction preserve its finite cohomological
support interval. Each native cohomology sheaf remains constructible under this restriction by
[lem-sf-native-adic-constructible-pullback]. The scheme $\overline{Z_A}$ is qcqs, by [lem-weil-
pbc-qcqs-over-affine] applied to its separated finite-type map to $\operatorname{Spec}k$. Hence
[lem-sf-native-adic-qcqs-stratification] replaces its locally given stratifications by finite
global ones. The encoding comparison [lem-sf-weil-verdier-module-constructibility-comparison]
now shows that $D(E)N$ belongs to the condensed $D^b_c(\overline{Z_A},\Omega)$. Its local models
$B_V^{\oplus r}$ are finite constant local models, hence locally finitely presented over the
restricted coefficient ring by [definition-constructible-sheaves--1]; so on each finite
stratum the cohomology is constructible also in the locally finitely presented sense used by the
bounded constructible category of the rational theorem. This verifies the input predicate for
proper base change for the actual native coefficients; merely forgetting Frobenius, without this
coefficient and constructibility comparison, would not suffice.
Dependencies: def-sf-native-weil-derived-framework, lem-sf-fixed-pair-derived-forget-comparison,
lem-sf-native-adic-pullback-exact-lisse, lem-sf-native-adic-constructible-pullback, lem-weil-
pbc-qcqs-over-affine, lem-sf-native-adic-qcqs-stratification, lem-sf-weil-verdier-module-
constructibility-comparison, definition-constructible-sheaves--1.

7. On a chart square, [lem-sf-finite-span-module-derived-comparison] identifies the native
ringed adjunction mate with the condensed module-object mate: its hypotheses hold by step 5, and
its comparison is an equality of the specified derived morphisms, including units, counits and
pullback composition. Apply clause (3) of [proposition-proper-direct-image-constructible-complexes]
with $\Lambda=\Omega$ to the input verified in step 6. This proves the native geometric exchange
invertible on that chart. To relate this to the global morphism, use [lem-sf-ringed-restriction-
exchange-open-descent] for restriction from $T$ to $A$. For the further restriction from
$u^{-1}A$ to $A'$, use [lem-sbc-ringed-topos-sheaf-slice-derived-comparison] on $p'$:
restriction preserves K-injectives and its comparison is the adjunction mate. In the exchange's
stated representative $u^{-1}p_*I\to p'_*v^{-1}I\to p'_*J$, restriction replaces $J$ by its
K-injective open restriction and every section map by the same section map on the slice. Thus it
is precisely the chart exchange, not just an isomorphism between the same two objects. The
geometric opens $\overline{A'}$ cover $\bar T'$, so all these restrictions are invertible.
Dependencies: lem-sf-finite-span-module-derived-comparison, det-thm-sfb-proper-base-change-
rational, lem-sf-ringed-restriction-exchange-open-descent, lem-sbc-ringed-topos-sheaf-slice-
derived-comparison.

8. Open restriction is exact, so each cohomology map of the forgotten $\beta_K$ restricts to an
isomorphism on the covering just obtained. Its kernel and cokernel restrict to zero; a sheaf
zero on a covering is zero, by the sheaf axiom. Every cohomology map is therefore invertible,
and [lem-weil-pbc-unbounded-derived-iso-cohomology] makes the forgotten $\beta_K$ invertible.
Conservativity of $D(U_{T'})$ from [lem-sf-fixed-pair-derived-forget-comparison] makes $\beta_K$
an isomorphism in $D(\mathcal W_{T'})$. This holds for every $K$ in the full bounded
constructible source subcategory. Restrict the natural transformation $\beta$ to that
subcategory and take its componentwise inverses. For $a:K\to L$, the naturality equality
$G(a)\beta_K=\beta_LF(a)$ implies $\beta_L^{-1}G(a)=F(a)\beta_K^{-1}$ by multiplying on the left
and right by the inverses. This gives the inverse natural transformation in the native derived
categories and proves the claimed functor isomorphism. Zero complexes, empty schemes and rank-
zero strata are included in the same argument.
Dependencies: lem-sf-native-adic-pullback-exact-lisse, lem-weil-pbc-unbounded-derived-iso-
cohomology, lem-sf-fixed-pair-derived-forget-comparison.
-/
theorem nativeWeil_proper_natural_baseChange
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {Z' Z T' T : Scheme.{u}}
    [Z'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [T'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
    (v : Z' ⟶ Z) (p' : Z' ⟶ T') (p : Z ⟶ T) (u : T' ⟶ T)
    [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [p.IsOver (Spec (CommRingCat.of k₀))] [u.IsOver (Spec (CommRingCat.of k₀))]
    (_sq : ChosenCartesianSquare v p' p u) [IsProper p]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of k₀))] :
    Nonempty
      (((WeilComplex.objectProperty k₀ l Z).ι ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l u).mapDerivedCategory) ≅
        ((WeilComplex.objectProperty k₀ l Z).ι ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor)) := by
  let F := CategoryTheory.Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l T')
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hF⟩ :=
    CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_forget_properties
      (WeilSheaf.frobeniusPullback k₀ l T')
  let : F.mapDerivedCategory.ReflectsIsomorphisms := hF
  have component_iso (K : WeilComplex k₀ l Z) :
      IsIso ((NativeBaseChange.mate k₀ l _sq.toCommSq).app K.obj) := by
    have hbounded := Functor.bounded_mapDerivedCategory_obj
      (CategoryTheory.Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l Z)) K.property.1
    have hc (n : ℤ) : ProEtale.IsAdicConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ n).obj
          ((NativeBaseChange.forget k₀ l Z).obj K.obj)) := by
      exact (ProEtale.adicConstructibleSheaf l _).prop_of_iso
        (((CategoryTheory.Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategoryHomologyFunctorIso n).app
            K.obj) (K.property.2 n)
    have := NativeBaseChange.geometric_proper_baseChange_isIso k₀ l _sq
      ((NativeBaseChange.forget k₀ l Z).obj K.obj) hbounded hc
    have : IsIso ((NativeBaseChange.forget k₀ l T').map
        ((NativeBaseChange.mate k₀ l _sq.toCommSq).app K.obj)) := by
      rw [NativeBaseChange.forget_mate]
      infer_instance
    exact isIso_of_reflects_iso _ (NativeBaseChange.forget k₀ l T')
  let β := Functor.whiskerLeft (WeilComplex.objectProperty k₀ l Z).ι
    (NativeBaseChange.mate k₀ l _sq.toCommSq)
  have : ∀ K, IsIso (β.app K) := fun K ↦ component_iso K
  have : IsIso β := NatIso.isIso_of_isIso_app β
  exact ⟨asIso β⟩

end AlgebraicGeometry
