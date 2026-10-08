+++
id = "lem-sc-divisible-group-structure"
kind = "lemma"
title = "Structure of divisible abelian groups"
lean = ["AddSubgroup.nonempty_addEquiv_torsionBy_of_natCard_eq"]
order = 574
+++
Let $D$ be a divisible abelian group, $\ell$ a prime and
$r\geq0$ an integer such that $D[\ell]$ has order $\ell^r$.
Then $D[\ell^n]\cong(\mathbf Z/\ell^n\mathbf Z)^r$ for every
$n\geq1$.

## Proof

We prove by induction on $n$ that
$D[\ell^n]\cong(\mathbf Z/\ell^n\mathbf Z)^r$, using only
divisibility of $D$ and the given size of $D[\ell]$. The case
$n=1$ is the hypothesis: $D[\ell]$ is a group killed by $\ell$
of order $\ell^r$, hence $\cong(\mathbf Z/\ell\mathbf Z)^r$.

For the induction step, multiplication by $\ell$ gives an exact
sequence

$$
0\longrightarrow D[\ell]\longrightarrow D[\ell^{n+1}]
\xrightarrow{\ \ell\ }D[\ell^n]\longrightarrow0,
$$

surjective on the right by divisibility of $D$. By induction
$D[\ell^n]\cong(\mathbf Z/\ell^n\mathbf Z)^r$, so
$D[\ell^{n+1}]$ is a finite abelian $\ell$-group of order
$\ell^r\cdot\ell^{nr}=\ell^{(n+1)r}$ satisfying
$\ell\cdot D[\ell^{n+1}]=D[\ell^n]\cong(\mathbf Z/\ell^n\mathbf Z)^r$
and $D[\ell^{n+1}][\ell]=D[\ell]\cong(\mathbf Z/\ell\mathbf Z)^r$.
Write $D[\ell^{n+1}]\cong\bigoplus_i\mathbf Z/\ell^{a_i}\mathbf Z$
(classification of finite abelian $\ell$-groups, $a_i\leq n+1$).
The second condition says that the number of cyclic summands is
exactly $r$ (the $\ell$-torsion of $\bigoplus_i\mathbf Z/\ell^{a_i}\mathbf Z$ is $(\mathbf Z/\ell\mathbf Z)^r$), and the
first says that $\ell\cdot D[\ell^{n+1}]$, which is
$\bigoplus_{a_i\geq2}\mathbf Z/\ell^{a_i-1}\mathbf Z$, is
$\cong(\mathbf Z/\ell^n\mathbf Z)^r$; hence there are exactly $r$
summands with $a_i\geq2$, each with $a_i-1=n$. Therefore all
$r$ summands have $a_i=n+1$, and
$D[\ell^{n+1}]\cong(\mathbf Z/\ell^{n+1}\mathbf Z)^r$.
(*cf. the same induction in Stacks Project, Groupoid Schemes,
Proposition 39.9.11, [Tag 03RP](https://stacks.math.columbia.edu/tag/03RP), proof of part (7)*.)
