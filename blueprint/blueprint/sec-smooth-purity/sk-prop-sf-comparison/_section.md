+++
id = "sk-prop-sf-comparison"
kind = "section"
title = "The pro-étale comparison"
order = 1649
lean = ["AlgebraicGeometry.ProEtale.comparisonUpperStar", "AlgebraicGeometry.ProEtale.full_comparisonUpperStar", "AlgebraicGeometry.ProEtale.faithful_comparisonUpperStar", "AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar"]
+++
*Proposition (sketch).*

For the comparison morphism $\nu_T:T_{\Proet}\to T_{\Et}$ and a finite
coefficient ring, the functor
$\nu_T^*:D^+(T_{\Et},\Lambda)\to D^+(T_{\Proet},\Lambda)$ is exact and fully
faithful, with $\mathrm{id}\cong R\nu_{T,*}\nu_T^*$; it restricts to a functor
$\Dbc(T_{\Et},\Lambda)\to\Dbc(T_{\Proet},\Lambda)$ which is an equivalence onto
the constructible subcategory of the target; the comparison direct image
$\nu_V^*Ru_{\Et,*}\cong Ru_{\Proet,*}\nu_U^*$ is an isomorphism of functors
$D^+(U_{\Et},\Lambda)\to D^+(V_{\Proet},\Lambda)$ for $u$ quasi-compact and
quasi-separated; and a morphism of pro-étale complexes is an isomorphism if
and only if it is one on a pro-étale covering family and on the affine
ind-étale basis. Detection is by covering families, not by geometric points:
clause (4) of lem:cbc-proetale-stalk-conservative records that
geometric-point stalks are *not* conservative on all pro-étale sheaves,
and no argument of this section uses them off the étale-origin objects
([sk-rem-sf-comp-scope]).
Chapter 4 for thm:weil-pbc-site-comparison,
prop:weil-pbc-comparison-direct-image and
lem:weil-pbc-pullback-preserves-bounded-constructible; Chapter 17 for the
detection clauses lem:cbc-proetale-stalk-conservative.

Uses: `lem-cbc-proetale-stalk-conservative`, `lem-weil-pbc-pullback-preserves-bounded-constructible`, `prop-weil-pbc-comparison-direct-image`, `thm-weil-pbc-site-comparison`
