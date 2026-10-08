+++
id = "sk-thm-sf-pf-proetale"
kind = "section"
title = "Projection formula: the pro-étale realization"
order = 2099
uses = ["sk-thm-sf-pf-field"]
+++
*Theorem (sketch).*

Let $K,L$ be the pro-étale realizations of bounded constructible finite-Tor
complexes, with étale-origin witnesses, at any coefficient stage. Then
$\operatorname{PF}_{f,K,L}$ is an isomorphism in
$D^+(Y_{\Proet},\Lambda)$.

## Proof

The exact comparison pullback $\nu^*$ of thm:weil-pbc-site-comparison
commutes with $Lf^*$ and with $\otimes^L$, and the compact-support comparison
of thm:cbc-finite-level-proetale identifies the transported
$R\bar f_*j_!$ together with its exchange and projection maps; hence the
comparison carries the étale projection transformation to the pro-étale
one, and transporting [sk-thm-sf-pf-finite] along it gives the statement at
every stage ([sk-thm-sf-pf-field] for the non-finite stages).

Uses: `\Cref{thm-sf-pf-field}`, `def-weil-pbc-etale-origin-witness`, `thm-cbc-finite-level-proetale`, `thm-weil-pbc-site-comparison`
