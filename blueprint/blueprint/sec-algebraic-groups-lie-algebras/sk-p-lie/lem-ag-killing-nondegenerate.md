+++
id = "lem-ag-killing-nondegenerate"
kind = "lemma"
title = "The Killing form of a semisimple Lie algebra is nondegenerate"
order = 2471
uses = ["def-wf-semisimple-lie-algebra", "lem-wf-cartan-trace-criterion"]
+++
Let $\mathfrak h$ be a finite-dimensional semisimple Lie algebra over
$\overline{\mathbf Q}_\ell$ in the sense of
[def-wf-semisimple-lie-algebra]. Its Killing form

$$
B(X,Y)=\operatorname{tr}(\operatorname{ad}(X)\operatorname{ad}(Y))
$$

is nondegenerate.

## Proof

To see this without a classification, let
$\mathfrak k=\operatorname{rad}(B)$. Invariance of $B$ makes
$\mathfrak k$ an ideal. Choose a vector-space decomposition
$\mathfrak h=\mathfrak k\oplus L$. If $X\in[\mathfrak k,\mathfrak k]$
and $Y\in\mathfrak k$, then $\operatorname{ad}(X)$ and
$\operatorname{ad}(Y)$ have zero lower-right block on
$\mathfrak h/\mathfrak k$, so

$$
\operatorname{tr}_{\mathfrak k}(\operatorname{ad}(X)|_{\mathfrak k}
\operatorname{ad}(Y)|_{\mathfrak k})=B(X,Y)=0.
$$

The trace criterion [lem-wf-cartan-trace-criterion], applied to
the image of $\mathfrak k$ in $\operatorname{End}(\mathfrak k)$,
shows that this image is solvable. Its kernel is the abelian centre of
$\mathfrak k$, so $\mathfrak k$ is solvable. Since $\mathfrak h$
is semisimple, $\mathfrak k=0$.
