+++
id = "prop-trf-pairing-point-normalization"
kind = "theorem"
title = "Pairing and its point normalization"
order = 2320
tags = ["latex:proposition"]
uses = ["def-trf-categorical-trace", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-supported-pairing", "prop-trf-trace-formal-laws", "thm-trf-kunneth-verdier", "thm-trf-verdier-biduality"]
+++
Let $P,Q$ be perfect $A$-complexes on $s=\operatorname{Spec}k$, and
let $u:P\to Q$, $v:Q\to P$, both regarded as correspondences with
support $s$. The
supported pairing satisfies

$$
\langle u,v\rangle_{\mathrm{LV}}=\tr_A(vu\mid P),
$$

where the right-hand side is the
ordinary categorical trace.

## Proof

The supported-class bijection of
[def-trf-correspondence], followed by the Kunneth–Verdier
isomorphism [thm-trf-kunneth-verdier], turns $u$ at a point into
$(u\otimes1)\operatorname{coev}_P:A\to Q\otimes_A^{\mathrm L}P^\vee$, and
similarly for $v$. In the recipe of
[def-trf-supported-pairing], contraction of these two classes cancels
the adjacent evaluation–coevaluation pair by a triangle identity. What
remains is precisely the composite defining the categorical trace of
[def-trf-categorical-trace], with endomorphism $vu$; the graded
signs are fixed by the formal laws [prop-trf-trace-formal-laws].
This proves the normalization.

The same adjunction calculation identifies the *diagonal
specialization* on any $X$: if $f:\Fix(c)\to X$ is the canonical map,
its exceptional adjoint is

$$
Rf_!A_{\Fix(c)}\simeq\Delta^*Rc_!A_C
\xrightarrow{\Delta^*\widetilde u}K\otimes_A^{\mathrm L}D_XK
\xrightarrow{\mathrm{ev}\circ\mathrm{sym}}\omega_X .
$$

Indeed, under the tensor–Hom adjunction and biduality ([thm-trf-verdier-biduality]) of
[def-trf-dualizing-complex], the class of the diagonal identity maps
to $1_K$, and the supported cup product reduces by the projection
formula and $!$-base change to the displayed composite. This is the
classical trace-class dictionary used by the proper-comparison input on
the specific representatives.
