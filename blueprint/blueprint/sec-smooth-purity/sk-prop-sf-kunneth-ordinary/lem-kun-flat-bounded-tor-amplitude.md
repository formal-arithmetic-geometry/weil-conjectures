+++
id = "lem-kun-flat-bounded-tor-amplitude"
kind = "lemma"
title = "Bounded complexes of flat sheaves have tor amplitude"
order = 1714
uses = ["def-kun-derived-tensor", "def-kun-tor-amplitude", "lem-kun-kflat-criteria"]
+++
Let $T$ be a scheme, $\Lambda$ a commutative ring, $a,b\in\mathbf Z$ with $a\le b$, and let $\mathcal E^\bullet$ be a bounded
complex of flat $\Lambda_T$-module sheaves supported in degrees
$[a,b]$. Then $\mathcal E^\bullet$, regarded as an object of
$D(T_{\Et},\Lambda)$, has tor amplitude in $[a,b]$
([def-kun-tor-amplitude]).

## Proof

A bounded-above complex of flat $\Lambda_T$-module sheaves is K-flat
by [lem-kun-kflat-criteria](1), so by
[def-kun-derived-tensor] the derived tensor product
$\mathcal E^\bullet\kunotimes{\Lambda}\mathcal M$ is computed by the
ordinary tensor product $\mathcal E^\bullet\otimes_\Lambda\mathcal M$, whose terms in degrees outside
$[a,b]$ vanish. Hence
$H^i\bigl(\mathcal E^\bullet\kunotimes{\Lambda}\mathcal M\bigr)=0$
for every $i\notin[a,b]$ and every $\Lambda_T$-module sheaf
$\mathcal M$ placed in degree zero, which is tor amplitude in
$[a,b]$ by [def-kun-tor-amplitude].
