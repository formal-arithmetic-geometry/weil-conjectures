+++
id = "lem-weil-karoubi-envelope-idempotent-complete"
kind = "lemma"
title = "The Karoubi envelope is idempotent complete"
order = 1420
uses = ["def-weil-karoubi-envelope"]
+++
Let $\mathcal T$ be an additive category and let $\Kar(\mathcal T)$ be its
Karoubi envelope [def-weil-karoubi-envelope]. Every idempotent endomorphism
of an object of $\Kar(\mathcal T)$ splits.

(*Source note:* no Stacks Project entry states this form for the envelope:
Lemma 12.4.2 (Tag [09SH](https://stacks.math.columbia.edu/tag/09SH))
characterizes the splitting of idempotents — an idempotent endomorphism
$p:z\to z$ of a Karoubian preadditive category admits a direct sum
decomposition $z=x\oplus y$ with $p$ the projection onto $y$ — but states it
as one of three equivalent characterizations of Karoubianity (Definition
12.4.1, Tag [09SG](https://stacks.math.columbia.edu/tag/09SG)), so it cannot
be applied to $\Kar(\mathcal T)$ before the envelope is known to be
Karoubian; the explicit splitting $i=p=f$ of an idempotent of $\Kar(\mathcal
T)$ by the pair of morphisms of $\mathcal T$ is the blueprint's addition, and
it is what makes the envelope a model for the idempotent completion used
below.)

## Proof

Let $(K,e)$ be an object of $\Kar(\mathcal T)$ and let $f:(K,e)\to(K,e)$ be
an idempotent endomorphism. By [def-weil-karoubi-envelope] the endomorphism
$f$ is a morphism $f:K\to K$ of $\mathcal T$ with $f=e\,f\,e$ and $f^2=f$.
Then $e f=e(e f e)=e^2fe=efe=f$ and $f e=(e f e)e=e f e^2=e f e=f$.
Consequently $f^2=f$ makes $(K,f)$ an object of $\Kar(\mathcal T)$, and the
morphisms

$$
 i=f:(K,f)\longrightarrow(K,e),\qquad
 p=f:(K,e)\longrightarrow(K,f)
$$

of $\mathcal T$ are morphisms of $\Kar(\mathcal T)$: for $i$ the condition
$i=e\,i\,f$ reads $f=eff=ef=f$, and for $p$ the condition $p=f\,p\,e$ reads
$f=ffe=fe=f$. Their composite $p\circ i=f\circ f=f$ is the identity of
$(K,f)$, whose identity is $f$ itself, and $i\circ p=f\circ f=f$, so
$f=i\circ p$ exhibits $f$ as the composite of a section and a retraction.
Hence every idempotent of $\Kar(\mathcal T)$ splits.
