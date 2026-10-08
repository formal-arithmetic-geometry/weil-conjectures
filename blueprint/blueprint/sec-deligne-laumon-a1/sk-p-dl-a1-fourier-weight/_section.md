+++
id = "sk-p-dl-a1-fourier-weight"
kind = "section"
title = "The Fourier upper weight"
order = 2777
uses = ["sk-cor-plancherel", "sk-l-dl-a1-energy", "sk-p-dl-a1-correction", "sk-p-dl-a1-some-weight"]
lean = ["AlgebraicGeometry.le_add_one_of_isFourierPartner"]
+++
*Proposition (sketch).*

The weight $v$ of $M'$ satisfies $v\le w+1$.

## Proof

Write $r=\operatorname{rank}M$ and $b=\operatorname{rank}B'$.
Purity bounds each trace of $M$ by $rq^{nw/2}$, and the line has $q^n$
rational points. Plancherel applied to $j_!M[1]$ therefore gives

$$
\sum_{y\in A'_0(\mathbf F_{q^n})}|\iota t_{G,n}(y)|^2
\le r^2q^{n(w+2)}.
$$

The weight bound for $B'$ gives the analogous bound
$b^2q^{n(w+1)}$. On $U'_0$, trace additivity says
$t_{M',n}=t_{G,n}-t_{B',n}$, so $|a-b|^2\le2|a|^2+2|b|^2$ yields

$$
S_n(U'_0,M')\le 2r^2q^{n(w+2)}+2b^2q^{n(w+1)}
\le 2(r^2+b^2)q^{n(w+2)}.
$$

Now $M'\ne0$ is pure by [sk-p-dl-a1-some-weight]. Apply
[sk-l-dl-a1-energy] with $B=w+2$ to obtain $v\le w+1$.

Uses: [sk-cor-plancherel], [sk-l-dl-a1-energy], [sk-p-dl-a1-correction], [sk-p-dl-a1-some-weight]
