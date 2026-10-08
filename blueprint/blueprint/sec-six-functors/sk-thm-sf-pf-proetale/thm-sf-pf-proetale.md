+++
id = "thm-sf-pf-proetale"
kind = "theorem"
title = "Pro-étale realization"
order = 2100
uses = ["def-sf-datum", "def-sf-pf", "def-weil-pbc-etale-origin-witness", "thm-cbc-finite-level-proetale", "thm-sf-pf-adic", "thm-sf-pf-field", "thm-sf-pf-finite", "thm-weil-pbc-site-comparison"]
+++
In the setting of [def-sf-datum], let $K,L$ be the pro-étale
realizations of bounded constructible finite-Tor complexes, with
étale-origin witnesses or with witnesses supplied by the site comparison,
at any coefficient stage. Then $\operatorname{PF}_{f,K,L}$ is an
isomorphism on the pro-étale site.

## Proof

The projection transformation used below is [def-sf-pf], and the
field case is [thm-sf-pf-field].
The exact comparison inverse image of [thm-weil-pbc-site-comparison]
commutes with $Lf^*$ and with $-\otimes^L$, and the compact-support
comparison of [thm-cbc-finite-level-proetale] identifies the
transported $R\bar f_*j_!$ together with its exchange and projection maps;
hence the comparison carries the étale projection transformation to the
pro-étale one. Transporting [thm-sf-pf-finite] along the comparison
gives the finite-coefficient statement; [thm-sf-pf-adic] gives the
integral stage and [thm-sf-pf-field] gives the field stages.
For objects presented without witnesses, the site
comparison supplies them by [def-weil-pbc-etale-origin-witness].
