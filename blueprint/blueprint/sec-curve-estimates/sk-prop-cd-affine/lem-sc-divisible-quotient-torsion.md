+++
id = "lem-sc-divisible-quotient-torsion"
kind = "lemma"
title = "Torsion in a quotient of a divisible group"
order = 1011
+++
Let $G$ be an abelian group, $\Lambda\subseteq G$ a subgroup,
and $n\geq1$. Assume multiplication by $n$ on $G$ is
surjective. Then there is a short exact sequence

$$
0\longrightarrow G[n]/\Lambda[n]
\longrightarrow (G/\Lambda)[n]
\xrightarrow{\delta}\Lambda/n\Lambda\longrightarrow0,
\qquad \delta(g+\Lambda)=ng+n\Lambda.
$$

## Proof

If $g+\Lambda$ is killed by $n$, then $ng\in\Lambda$, so
$\delta$ is defined. Replacing $g$ by $g+\lambda$ changes
$ng$ by $n\lambda$, proving independence of the representative.
The map from $G[n]$ to $(G/\Lambda)[n]$ has kernel
$G[n]\cap\Lambda=\Lambda[n]$. Its image is contained in
$\ker\delta$. Conversely, if $ng=n\lambda$ for
$\lambda\in\Lambda$, then $g-\lambda\in G[n]$ represents the
same quotient class, proving equality with the kernel. Finally,
for $\lambda\in\Lambda$ choose $g\in G$ with $ng=\lambda$;
then $g+\Lambda$ maps to $\lambda+n\Lambda$, proving surjectivity.
