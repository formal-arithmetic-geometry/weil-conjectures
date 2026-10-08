+++
id = "pqf-lem-coherent-ft-locnoeth"
kind = "lemma"
title = "Coherence on locally Noetherian schemes"
order = 538
uses = ["pqf-def-coherent", "pqf-def-locnoeth"]
+++
Let $X$ be a
locally Noetherian scheme and
$\mathcal F$ an $\mathcal O_X$-module. Then $\mathcal F$ is coherent
if and only if it is quasi-coherent of finite type.
(*Stacks Project, Cohomology of Schemes, Lemma 30.9.1, Tag
[01XZ](https://stacks.math.columbia.edu/tag/01XZ).*)

## Proof

*($\Leftarrow$).* Let $\mathcal F$ be quasi-coherent and of
finite type on the locally Noetherian $X$ ([pqf-def-locnoeth]) and
let $\varphi:\mathcal O_U^{\oplus n}\to\mathcal F|_U$
be a map over an open $U$. Kernels of maps of quasi-coherent sheaves
are quasi-coherent (checked on affine open subschemes, where they
correspond to kernels of maps of modules), so $\ker\varphi$ is
quasi-coherent; being a quasi-coherent submodule of a finite-rank
free module over each affine Noetherian $\operatorname{Spec}A\subset U$
it is the sheaf $\widetilde K$ of a submodule $K\subset A^n$, and $K$
is finitely generated because $A$ and hence $A^n$ are Noetherian.
Thus $\ker\varphi$ is of finite type, which with $\mathcal F$ of
finite type is the definition of coherence in
[pqf-def-coherent].
*($\Rightarrow$).* Let $\mathcal F$ be coherent; it is of
finite type by definition, and it is quasi-coherent: for an affine
open $\operatorname{Spec}A\subset X$ with $A$ Noetherian, the
coherence condition (finite kernels) gives that
$\mathcal F|_{\operatorname{Spec}A}$ is the sheaf associated with
its module of global sections – the classical finite-relation
argument over Noetherian rings: because $\mathcal F$ is of finite
type there is a surjection $A^n\to\Gamma(\operatorname{Spec}A,\mathcal F)$
whose kernel is finitely generated, the kernel being of finite type
by coherence, so a presentation exists; the same argument on
principal open subschemes $D(g)$ and the exactness of
$(-)\otimes_A A_g$ yield $\Gamma(D(g),\mathcal F)=\Gamma(\operatorname{Spec}A,\mathcal F)_g$, i.e. the sheaf $\mathcal F|_{\operatorname{Spec}A}$ is
$\widetilde{\Gamma(\operatorname{Spec}A,\mathcal F)}$ (cf. the
classical equivalent characterization of coherent modules on
Noetherian schemes, Stacks Project, Cohomology of Schemes, Lemma
30.9.1, [Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)).
Since this holds on every affine open, $\mathcal F$ is
quasi-coherent.
