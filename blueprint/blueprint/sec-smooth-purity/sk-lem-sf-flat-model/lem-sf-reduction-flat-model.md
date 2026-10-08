+++
id = "lem-sf-reduction-flat-model"
kind = "lemma"
title = "Reduction of the flat model"
order = 1832
uses = ["def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-etale-site", "def-weil-pbc-proetale-site", "lem-exc-constant-inverse-image-flat", "lem-sf-flat-model"]
+++
Let $A_{E,m}$ and $A_{E,n}$ be two finite coefficient stages with
$m\leq n$, let $T$ be a scheme on which $\ell$ is invertible, let
$K\in D^b_c(T,A_{E,n})$ be a bounded constructible complex of
$A_{E,n}$-modules on the small pro-étale site or on the small étale
site, and let $P\cong K$ be a bounded flat model of $K$ in degrees
$[a,b]$ in the sense of [lem-sf-flat-model]: each $P^q$ is a flat
$A_{E,n}$-module sheaf and $P^q=0$ for $q\notin[a,b]$. Write
$K_m=K\otimes^L_{A_{E,n}}A_{E,m}$ for the reduction of $K$. Then
$P\otimes_{A_{E,n}}A_{E,m}$ is a bounded flat model of $K_m$ in the
same interval:

$$
K_m\cong P\otimes_{A_{E,n}}A_{E,m},\qquad
(P\otimes_{A_{E,n}}A_{E,m})^q=0\quad(q\notin[a,b]),
$$

and each term $P^q\otimes_{A_{E,n}}A_{E,m}$ is a flat
$A_{E,m}$-module sheaf. Consequently the reduction $K_m$ has finite
Tor amplitude in $[a,b]$ as soon
as $K$ does.

## Proof

The complex $P$ is bounded and flat, hence K-flat by the argument of
[lem-sf-flat-model]: for an acyclic complex $Q$ of
$A_{E,n}$-module sheaves each $P^q\otimes_{A_{E,n}}Q$ is acyclic,
because $P^q\otimes_{A_{E,n}}-$ is exact by flatness, and the total
complex of a double complex one of whose directions is acyclic is acyclic.
Therefore the derived tensor product $K\otimes^L_{A_{E,n}}A_{E,m}$ is
computed by the ordinary tensor complex
$P\otimes_{A_{E,n}}A_{E,m}$ with the constant sheaf $A_{E,m}$ placed in
degree zero, by [def-weil-derived-tensor]; this is the displayed
isomorphism, and its terms sit in degrees $[a,b]$ because those of $P$
do.
Each term $P^q\otimes_{A_{E,n}}A_{E,m}$ is flat over $A_{E,m}$:
flatness is the condition of [lem-exc-constant-inverse-image-flat],
that tensoring with the sheaf preserves injections of module sheaves; for
an injection $N'\to N$ of $A_{E,m}$-module sheaves the map
$(P^q\otimes_{A_{E,n}}A_{E,m})\otimes_{A_{E,m}}N'\to (P^q\otimes_{A_{E,n}}A_{E,m})\otimes_{A_{E,m}}N$ is, by associativity of
the tensor product, the map $P^q\otimes_{A_{E,n}}N'\to P^q\otimes_{A_{E,n}}N$ of $A_{E,n}$-module sheaves, and that is
injective because $P^q$ is flat over $A_{E,n}$.
The reduction $K_m$ is therefore isomorphic to a bounded complex of flat
$A_{E,m}$-module sheaves concentrated in $[a,b]$, and the equivalence
of [lem-sf-flat-model] turns that flat model into finite Tor amplitude
of $K_m$ in $[a,b]$, which is the last assertion.
