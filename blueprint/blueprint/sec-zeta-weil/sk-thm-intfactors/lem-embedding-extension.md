+++
id = "lem-embedding-extension"
kind = "lemma"
title = "Extension of embeddings and intrinsic weights"
order = 2905
uses = ["def-weil-algebraic-closure-q", "def-weil-finite-field-fiber", "def-weil-numbers"]
+++
Fix a prime $p$, $a\in\mathbf Z_{\geq1}$, $q=p^a$, $k_0=\Fq$, and
$k=\Fbar$, the fixed algebraic
closure of $k_0$. Fix a prime $\ell\neq p$, write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$, and
choose an algebraic closure $\overline{\mathbf Q}$ of $\mathbf Q$, and
set

$$
\overline{\mathbf Q}^{(\ell)}=
\{z\in\Qlb:z\text{ is algebraic over }\mathbf Q\}.
$$

An ell-adic realization is an isomorphism
$\jmath:\overline{\mathbf Q}\xrightarrow{\sim}\overline{\mathbf Q}^{(\ell)}$;
this is the algebraic-closure
notion, with the finite-field datum.
Fix $i\in\mathbf Z$, a number field
$L\subset\Qlb$, and a field embedding $\sigma:L\hookrightarrow\mathbf C$.
There is an abstract field isomorphism

$$
\iota:\Qlb\xrightarrow{\sim}\mathbf C
$$

whose restriction to $L$ is $\sigma$. If $\alpha\in\overline{\mathbf Q}$
is such that

$$
|\iota(\jmath(\alpha))|=q^{i/2}
$$

for every ell-adic realization $\jmath$ and every abstract field isomorphism
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$, then

$$
|\tau(\alpha)|=q^{i/2}
$$

for every $\tau:\mathbf Q(\alpha)\hookrightarrow\mathbf C$.
The $q$-Weil-number condition of weight $i$
is stable under
$\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$.

## Proof

First extend $\sigma:L\hookrightarrow\mathbf C$ to an isomorphism
between the algebraic closure of $L$ inside $\Qlb$ and the
algebraic closure of $\sigma(L)$ inside $\mathbf C$.
Both are countable algebraically closed fields. Choose
transcendence bases $B_\ell$ and $B_{\mathbf C}$ over these
respective fields. Each basis has cardinality $2^{\aleph_0}$:
an algebraic extension of the rational function field in a basis
$B$ over a countable field has cardinality
$\max(\aleph_0,|B|)$, whereas both ambient fields have
cardinality $2^{\aleph_0}$.
A bijection $B_\ell\to B_{\mathbf C}$, together with the chosen
isomorphism on the algebraic closures of $L$, defines an
isomorphism of the corresponding rational function fields.
Extending it to their algebraic closures gives an isomorphism
$\iota:\Qlb\to\mathbf C$ restricting to $\sigma$.
The algebraic-closure convention is
[def-weil-algebraic-closure-q].

For an embedding $\tau:\mathbf Q(\alpha)\hookrightarrow\mathbf C$, the
composite $\sigma_\tau:=\tau\circ(\jmath|_{\mathbf Q(\alpha)})^{-1}$
embeds the number field $\jmath(\mathbf Q(\alpha))\subset\Qlb$ into
$\mathbf C$; extending it as above gives an abstract field
isomorphism $\iota_\tau:\Qlb\xrightarrow{\sim}\mathbf C$ with
$\iota_\tau(\jmath(\alpha))=\tau(\alpha)$, so the hypothesis applied
to this $\iota_\tau$ gives $|\tau(\alpha)|=q^{i/2}$.

For the Galois stability, let $\gamma\in\operatorname{Gal} (\overline{\mathbf Q}/\mathbf Q)$ and let
$\tau':\mathbf Q(\gamma(\alpha))\hookrightarrow\mathbf C$. Then
$\tau'\circ\gamma:\mathbf Q(\alpha)\hookrightarrow\mathbf C$ is an
embedding, so by the preceding paragraph
$|\tau'(\gamma(\alpha))|=|(\tau'\circ\gamma)(\alpha)|=q^{i/2}$.
Hence $\gamma(\alpha)$ satisfies the $q$-Weil condition of weight
$i$ of [def-weil-numbers], which proves the stability
assertion.
