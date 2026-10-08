+++
id = "lemma-nagata-separated-two-open-cover"
kind = "lemma"
title = "[stacks-project]"
order = 236
lean = ["AlgebraicGeometry.IsSeparated.of_two_open_cover"]
uses = ["lemma-nagata-diagonal-mixed-open"]
+++
Let $X=U\cup V$ be an open cover over $S$. Assume that $U\to S$ and
$V\to S$ are separated and that

$$
U\cap V\longrightarrow U\times_SV
$$

is a closed immersion. Then $X\to S$ is separated.

## Proof

The target of $\Delta_{X/S}$ is covered by

$$
U\times_SU,\quad U\times_SV,\quad
V\times_SU,\quad V\times_SV.
$$

On the two unmixed pieces the diagonal is closed by separatedness of $U/S$
and $V/S$. On the mixed pieces use
[lemma-nagata-diagonal-mixed-open]. Closed immersions are local on the
target, so $\Delta_{X/S}$ is closed.
