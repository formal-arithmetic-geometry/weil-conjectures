+++
id = "rem-trf-classical-framework"
kind = "remark"
title = "Classical framework convention: no $\\infty$-categories"
order = 2272
uses = ["def-exchange-projection", "def-trf-categorical-trace", "def-weil-algebraically-closed-coefficients", "def-weil-finite-coefficient-point", "def-weil-pbc-proetale-site", "def-weil-rationalization-karoubi", "lem-weil-pbc-reconstruction-uniform-tower", "prop-functor-package"]
+++
Throughout this chapter, and in every statement below, the framework is
the *classical* one of the framework chapter: ordinary categories, ordinary
triangulated categories in the sense of Verdier, sets of morphisms,
exact functors, natural transformations, and 2-categorical (bicategorical)
arguments only. No $\infty$-category, no $\infty$-operad, no
model-independent ``coherent'' higher machinery is used or assumed. The
following conventions fix what this means for every phrase that could be
read either way.

1. *The derived categories.* $D^b_c(X,A)$, $D^b_{ctf}(X,A)$,
$D^b_{\mathrm{fin}}(A)$, and their integral, rational, and
algebraically closed analogues are the classical Verdier derived
categories of the small
pro-etale site (or of the point), localized at quasi-isomorphisms, with
the coefficient constructions of the framework chapter. In particular
$D^b_c(X,A)$ is a triangulated category in the strict sense of
Verdier: the distinguished triangles, the shift functor, and the
octahedral axiom are given data, and there is *no* functorial choice
of mapping cone, no mapping-cone functor, and no model of the derived
category in which cones are strict. Consequently, all arguments below
that involve a distinguished triangle do it in one of two ways:
   1. the statement is about a *functor known to be exact and
triangulated* (e.g. $Lf^*$, $Rf_!$, $Rf^!$, $R\Gamma_c(X,-)$,
$L\bar x^*$), so that the image of a distinguished triangle is
distinguished and the image of a morphism of triangles is a morphism
of triangles, *because the interface records this* (the
exactness clauses of [prop-functor-package]); or
   1. the statement is proved at the level of *explicit bounded
complexes* with the Koszul convention of
[lem-trf-chain-supertrace], i.e. one chooses a representative
(possible because every object of $D^b_{\mathrm{fin}}(A)$ is
represented by a bounded complex of finitely generated projective
$A$-modules), computes there, and shows the result to be a
quasi-isomorphism invariant.
1. *The six-functor package as a 2-categorical datum.* The
six operations, the exchange and projection transformations, the units
and counits of the adjunctions, the composition laws, the smooth-purity
and Verdier-biduality isomorphisms, and the coefficient-passage maps of
the framework chapter, the six-operations
package, are used in the following precise form: they are a datum
consisting of
   - for each $f:X\to Y$ (separated finite type, under the stated
admissibility), the exact functors $Lf^*$, $Rf_*$, $Rf_!$,
$Rf^!$ between the triangulated categories;
   - for each Cartesian square, the exchange transformations
$\operatorname{Ex}_*$, $\operatorname{Ex}_!$ and, for each
$L\in D^b_{ctf}$, the projection transformation
$\operatorname{PF}$ (the framework chapter,
[def-exchange-projection]), each a *natural* transformation
of exact functors;
   - for each composable pair, the composition isomorphisms
$Rg_!\circ Rf_!\cong R(gf)_!$ and their adjoint forms, with the
identity compatibilities and the associativity pentagon;
   - for each $f$, the unit $\eta_f:\operatorname{id}\to Rf^!Rf_!$ and the counit $\varepsilon_f:Rf_!Rf^!\to \operatorname{id}$ of the adjunction $Rf_!\dashv Rf^!$;
   - the compatibility laws connecting these: the base-change
cocycle over a composite of Cartesian squares (the ``outer square''
condition), the compatibility of the composition isomorphisms with
the exchanges, the projection-formula–exchange cocycles, and the
adjunction compatibility of the exchanges; each of these is a
*stated, enumerated law of the interface*, not a consequence of
coherence in a higher structure.
Whenever this chapter writes ``the canonical map'' or ``the canonical
isomorphism'', it means: a map or isomorphism *built from the
data above* by composition, whiskering, and (where an adjoint is
uniquely determined) the mate construction of
is not one of the enumerated laws, the coherence is either proved in
this chapter by an explicit model (e.g. the Koszul computations of
[lem-trf-chain-supertrace] and the split-exact-sequence
computation of [prop-trf-trace-formal-laws]) or proved from the
results of this manuscript with its classical source recorded as
provenance. The four statements that used to be recorded as
unresolved geometric interfaces are now discharged: the étale
exceptional pullback by *Exceptional pullback along an etale morphism*
(smooth purity of the manuscript), the triangle compatibility of the
trace class by [lem-trf-trace-triangle-compatibility] (reduced to
the point normalization [prop-trf-pairing-point-normalization]),
the normal-cone reduction by *Normal-cone reduction for the trace*
(from [thm-pur-dnc-invariance] and
*Normal-cone evaluation of the trace map*), and the normal-cone
evaluation of the contracting trace map by
*Normal-cone evaluation of the trace map* (from the dualizing
and Thom statements of the smooth-purity chapter and the contracting
reduction *Contracting local model at an isolated fixed point*); the contracting
computation *Trace map of a contracting correspondence* is proved from it.
All other steps of the
trace formula are proved inside this chapter: the
proper-pushforward interface by
[thm-trf-trace-proper-compatibility], the étale pullback
compatibility by *Etale pullback compatibility of trace maps*, the
additivity by [prop-trf-trace-class-additivity] and
*Additivity of the categorical traces of the global operators*, the fixed-point
localization by [thm-trf-fixed-point-localization] with the
diagonal case *Localization in the diagonal case*, and the
comparison [thm-trf-lefschetz-verdier].
1. *The trace and the duality data.* The categorical trace of
[def-trf-categorical-trace] is a 1-categorical construction: the
strict symmetric monoidal structure on the model category of bounded
complexes of finitely generated projective modules is made explicit in
[lem-trf-chain-supertrace] (the Koszul braiding, the explicit
coevaluation and evaluation and the verification of the triangle
identities at the level of the model), and the trace is then the
composite of four *morphisms in the model category*, followed by
the identification $\operatorname{End}_{D(A)}(A)\cong A$. No
synthetic or higher-categorical trace is used.
1. *Classical bookkeeping of limits and idempotents.*
The adic passages of [def-trf-adic-system] and below use
*literal* compatible systems of bounded perfect complexes and
*literal* derived inverse limits in the classical sense (the
construction of the proper-base-change chapter,
[lem-weil-pbc-reconstruction-uniform-tower]), and the
$\Qlb$-coefficient category is the *classical*
filtered-colimit/common-stage category of the framework chapter with its
classical idempotent completion (the framework chapter,
[def-weil-algebraically-closed-coefficients]; note that in the
classical triangulated setting the idempotent completion is taken in
the ordinary 1-categorical sense: an object together with
$e\in\operatorname{End}(P)$, $e^2=e$, and the resulting
Karoubian category, as in
[def-weil-rationalization-karoubi] of the framework chapter). The
compatibility of the trace with these operations is proved step by step
(in [prop-trf-adic-coefficient-morphism-systems] and
[thm-trf-integral-adic-coefficient-morphism-trace-formula]) from the explicit
levelwise formulas, never from a general ``limits commute with
functors'' statement in a higher category.
1. *Koszul sign convention.* In every explicit computation
with complexes, the conventions of
[lem-trf-chain-supertrace] are used: the differential of the
tensor product of complexes is
$d(p\otimes q)=dp\otimes q+(-1)^{|p|}p\otimes dq$, the braiding is
$c(p\otimes q)=(-1)^{|p||q|}q\otimes p$, and the internal-Hom and
duality data are the ones displayed there. These are the conventions
of the classical references for the trace-class formalism ($SGA5$,
Exposé III; Milne, *Lectures on Étale Cohomology*, Sections
24–29), which are also written in the classical triangulated framework.
