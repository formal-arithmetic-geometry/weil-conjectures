+++
id = "rem-trf-decomposition-summary"
kind = "remark"
title = "Decomposition summary"
order = 2402
uses = ["cor-trf-point-counting", "def-trf-categorical-trace", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-frobenius-operators", "def-trf-global-operator", "def-trf-graph-correspondence", "def-trf-integration", "def-trf-local-term", "def-trf-strict-weil-complex", "def-trf-trace-class", "lem-trf-adjoint-mate", "lem-trf-chain-supertrace", "lem-trf-proper-pushforward-trace-class", "prop-trf-adic-coefficient-morphism-systems", "prop-trf-fixed-square-cartesian", "prop-trf-graph-frobenius-operator", "prop-trf-graph-operator", "prop-trf-rational-frobenius-integral-model", "prop-trf-trace-class-additivity", "prop-trf-trace-formal-laws", "rem-trf-classical-framework", "rem-trf-verdier-decomposition", "thm-trf-dualizing-complex-composition", "thm-trf-fixed-point-base-change", "thm-trf-fixed-point-localization", "thm-trf-frobenius-fixed-points", "thm-trf-frobenius-local-term", "thm-trf-grothendieck-lefschetz-finite-ring", "thm-trf-grothendieck-lefschetz-qbar", "thm-trf-integral-adic-coefficient-morphism-trace-formula", "thm-trf-internal-hom-pullback", "thm-trf-lefschetz-verdier", "thm-trf-trace-formula-e", "thm-trf-verdier-biduality", "thm-trf-verdier-duality"]
+++
The chapter extracts the two trace-formula inputs of the Weil-conjecture
proof, the fixed-point evaluation and the Lefschetz–Verdier trace
comparison, and decomposes them into the following chain. Throughout,
the framework is the classical 1-categorical one of
[rem-trf-classical-framework] (no $\infty$-categories): the
triangulated categories of the trace-formula chapter, the six-functor package as a
2-categorical datum with the enumerated coherence laws, and the
explicit-model computations of [lem-trf-chain-supertrace].

1. the framework convention and the coefficient conventions
([rem-trf-classical-framework],
[def-trf-strict-weil-complex], [def-trf-frobenius-operators]);
1. the categorical trace and its formal laws
([def-trf-categorical-trace], the explicit Koszul conventions and
computation of [lem-trf-chain-supertrace],
[prop-trf-trace-formal-laws]);
1. the correspondence formalism: [def-trf-correspondence] and
[def-trf-global-operator], the fixed scheme
[def-trf-fixed-scheme] in the Cartesian fixed square
[prop-trf-fixed-square-cartesian], the dualizing complex and Verdier
dual of [def-trf-dualizing-complex] with
[thm-trf-dualizing-complex-composition] and
[thm-trf-verdier-biduality], and the internal-Hom/pullback and
fixed-square base changes ([thm-trf-internal-hom-pullback],
[thm-trf-fixed-point-base-change]); the naive single-leg
identification is explicitly rejected in the preceding discussion,
and only the displayed valid exchanges are used;
1. the trace class, integration, and local terms
([def-trf-trace-class], [def-trf-integration],
[def-trf-local-term]) built on the fixed-point evaluation
[thm-trf-verdier-duality], whose external-duality construction is
proved in this chapter from the Kunneth–Verdier chain, and the
etale-pullback, additivity and localization statements are now
theorems of this chapter; no retired
diagram labels are used. The proper-pushforward compatibility is
discharged by [thm-trf-trace-proper-compatibility]; the precise
inventory of what remains is [rem-trf-verdier-decomposition];
1. the trace-compatibility interfaces: the proper-pushforward
compatibility is proved as [thm-trf-trace-proper-compatibility]
(so the former interface [lem-trf-proper-pushforward-trace-class]
is retired), and the etale-pullback compatibility
*Etale pullback compatibility of trace maps* and the additivity
[prop-trf-trace-class-additivity] are proved; then the
fixed-point localization
[thm-trf-fixed-point-localization] and the assembly
[thm-trf-lefschetz-verdier] of the comparison; the fixed scheme of a
base-changed correspondence is [lem-trf-fixed-map-proper];
1. the Frobenius graph: [def-trf-graph-correspondence],
[prop-trf-graph-operator], the mate lemma
[lem-trf-adjoint-mate] used in
[prop-trf-graph-frobenius-operator], the fixed-point theorem
[thm-trf-frobenius-fixed-points] (with the complete affine
computation and the transversality check) and the local-term formula
[thm-trf-frobenius-local-term];
1. the coefficient descent to the finite-ring, integral, rational and
algebraically closed statements
([thm-trf-grothendieck-lefschetz-finite-ring],
[thm-trf-integral-adic-coefficient-morphism-trace-formula], [thm-trf-trace-formula-e],
[thm-trf-grothendieck-lefschetz-qbar]) and the point-counting
corollary [cor-trf-point-counting]; for an arbitrary, possibly
non-invertible, Weil map at the stage $E$ the descent passes through an
integral model with non-invertible Frobenius coefficient morphisms
([prop-trf-rational-frobenius-integral-model]), their adic assembly
([prop-trf-adic-coefficient-morphism-systems]) and the integral
coefficient-morphism trace formula
[thm-trf-integral-adic-coefficient-morphism-trace-formula].

The chapter has no imported geometric input any more. The four
statements that were carried as classical inputs are now theorems of this
manuscript, each with its classical source recorded as provenance:

1. the exceptional pullback isomorphism for an étale morphism is
proved as *Exceptional pullback along an etale morphism* from the smooth purity
of the manuscript's smooth-purity chapter
([def-pur-smooth-purity-map], [thm-pur-cohomological-smoothness])
and the composition laws of the six-operations package;
1. the additivity of the Verdier trace class along distinguished
triangles [lem-trf-trace-triangle-compatibility] is proved by
reducing it to the point normalization of the supported pairing
([prop-trf-pairing-point-normalization] of the trace-formula chapter) and the
triangle additivity of the categorical trace
([prop-trf-trace-formal-laws]); its classical source is SGA 5,
Exposé III, 4.2 and
[Varshavsky, Section 5](https://arxiv.org/pdf/math/0505564);
1. the deformation-to-the-normal-cone reduction
*Normal-cone reduction for the trace* is proved from the
deformation invariance and the dualizing-object identification of the
smooth-purity chapter of this manuscript
([thm-pur-dnc-invariance], [thm-pur-diagonal-dualizing-object])
together with the normal-cone evaluation and the contracting computation
(*Normal-cone evaluation of the trace map*,
*Trace map of a contracting correspondence*); its classical source is SGA 5,
Exposé III, 4.3–4.4 and Varshavsky 2.1.1;
1. the normal-cone evaluation of the trace map of a contracting
correspondence *Normal-cone evaluation of the trace map* is proved
from the contracting reduction *Contracting local model at an isolated fixed point*, the
point normalization [prop-trf-pairing-point-normalization], the Thom
and affine-line normalizations of the smooth-purity chapter
([thm-pur-rank-one-thom],
*Trace normalization of the affine-line purity*,
[lem-pur-lisse-uniqueness]) and the dualizing composition
[thm-trf-dualizing-complex-composition]; its classical source is
Varshavsky, Theorem 2.1.2 with SGA 5, Exposé III, 4.3–4.4.

Everything else is proved in this chapter or quoted from the trace-formula chapter
(the six-functor package, Verdier biduality, and the base-change and
projection rules). In particular the proper-pushforward trace
identity is [thm-trf-trace-proper-compatibility], the étale
pullback identity is *Etale pullback compatibility of trace maps*, the
additivity is [prop-trf-trace-class-additivity], the fixed-point
localization is [thm-trf-fixed-point-localization], the
comparison is [thm-trf-lefschetz-verdier], and the four
coefficient-level trace formulas are
[thm-trf-grothendieck-lefschetz-finite-ring],
[thm-trf-integral-adic-coefficient-morphism-trace-formula],
[thm-trf-trace-formula-e],
[thm-trf-grothendieck-lefschetz-qbar] with the corollary
[cor-trf-point-counting].
