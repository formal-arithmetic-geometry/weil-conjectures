+++
id = "lem-sf-kunneth-coherence"
kind = "lemma"
title = "Coherence of the relative product"
order = 2189
uses = ["def-compact-support-direct-image-detailed", "def-sf-pf", "lem-sf-mate", "prop-compactification-coherence-detailed", "prop-sf-pf-coherence", "thm-sf-comp-composition", "thm-sf-kunneth-relative", "thm-sf-pf-finite"]
+++
In the setting of [thm-sf-kunneth-relative], the isomorphism
$R(f\times_Bg)_!(K\boxtimes L)\cong Rf_!K\otimes^LRg_!L$ is compatible with

1. **(i)** the symmetry $K\boxtimes L\cong L\boxtimes K$;
1. **(ii)** the triple product: the two iterated isomorphisms
$R(f\times_Bg\times_Bh)_!(K\boxtimes L\boxtimes M)\cong (Rf_!K\otimes^LRg_!L)\otimes^LRh_!M$ and
$Rf_!K\otimes^L(Rg_!L\otimes^LRh_!M)$ agree;
1. **(iii)** base change of the base $B'\to B$;
1. **(iv)** the projection formula of [def-sf-pf].

Consequently the $n$-fold products, and the closed-subscheme compact-support forms of
[thm-sf-kunneth-relative], are defined without ambiguity.

## Proof

The isomorphism of [thm-sf-kunneth-relative] is, by its proof in this
chapter, the composite of the composition law [thm-sf-comp-composition] of
[def-compact-support-direct-image-detailed] — whose coherence, including the
independence of the compactification and the identifications
$Rf_!\cong Rf_*$ for proper $f$, is [prop-compactification-coherence-detailed]
of the proper-base-change chapter — the exchange $\operatorname{Ex}_!$ of
axiom (A2), which is the compact-support base-change theorem of the
compact-support chapter, and the projection transformation of [def-sf-pf], which is axiom
(A3) and is discharged by [thm-sf-pf-finite] together with
[prop-sf-pf-coherence] below. Each of the four assertions is therefore
an identity between composites of canonical maps attached to the same pasted
squares; such identities are the content of [lem-sf-mate], pasting the
squares and using the pentagon of [prop-compactification-coherence-detailed]:
(ii) reduces to the coherence of the associativity of $\otimes^L$ with
$\operatorname{PF}$, the pentagon of [prop-sf-pf-coherence]; (iv) to the
identity clause of [prop-sf-pf-coherence] and the identity-square clause of
(A2); (iii) is the base-change clause of [prop-sf-pf-coherence] — the
projection transformation commutes with $\operatorname{Ex}_!$ through the
monoidality of pullback — applied to $\operatorname{PF}_q$ and
$\operatorname{PF}_g$, together with the pasting of $\operatorname{Ex}_!$
for the three Cartesian squares over $B'\to B$; and (i) is the mate identity
behind that base-change clause: after reduction to proper $f,g$ by the
independence of the compactification, $\operatorname{PF}\circ(\operatorname{Ex}_!\otimes1)$
is the transpose of the pulled-back counit tensored with the identity (see
the proof of [prop-sf-pf-coherence]), so both the isomorphism and its
swapped version are inverse to the transpose under $L(f\times_Bg)^*\dashv R(f\times_Bg)_*$
of the symmetric map
$Lp^*Lf^*Rf_*K\otimes^LLq^*Lg^*Rg_*L\to Lp^*K\otimes^LLq^*L$ given by the
two counits.
