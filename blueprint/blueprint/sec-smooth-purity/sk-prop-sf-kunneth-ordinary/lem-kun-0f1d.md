+++
id = "lem-kun-0f1d"
kind = "lemma"
title = "Failure of base change produces an integral normal base"
order = 1759
uses = ["def-kun-bc-property", "def-weil-pbc-cartesian-square"]
+++
Let $f:X\to S$ be a morphism of schemes and $n\ge1$ an integer
invertible on $S$ (notation of [def-kun-bc-property]). Assume
that for some $q\ge1$ the property $BC(f,n,q-1)$ holds but
$BC(f,n,q)$ does not. Then there exists a commutative diagram

$$
\begin{array}{ccccc}
X&\longleftarrow&X'&\longleftarrow&Y\\
\Big\downarrow{\scriptstyle f}&&\Big\downarrow{}&&\Big\downarrow{\scriptstyle h}\\
S&\longleftarrow&S'&\longleftarrow&\Spec(K)
\end{array}
$$

with both squares
cartesian, where $S'$ is
affine, integral, and normal with algebraically closed function field
$K$, and an integer $d\mid n$ such that
$R^qh_*(\underline{\mathbf Z/d\mathbf Z})$ is nonzero.
(*Source:* Stacks Project,
[Tag
`0F1D`](https://stacks.math.columbia.edu/tag/0F1D).) In the Stacks Project the proof uses Lemma 59.88.7,
[Tag `0F08`](https://stacks.math.columbia.edu/tag/0F08)
(the witness diagram produced by a failure of $BC(f,n,q)$) and Lemma
59.90.2, [Tag
`0F0B`](https://stacks.math.columbia.edu/tag/0F0B) (the total direct image of $\mathbf Z/d\mathbf Z$ along
the extension of the function field is again $\mathbf Z/d\mathbf Z$).

## Proof

This is the recorded classical input named in the statement, Stacks Project, Tag [0F1D](https://stacks.math.columbia.edu/tag/0F1D): a failure of base change in degree q is witnessed over an affine integral normal base with algebraically closed function field, by a nonzero higher direct image of a constant torsion sheaf. In the Stacks Project the proof uses Lemma 59.88.7 ([Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)) and Lemma 59.90.2 ([Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)). No separate proof is given.
