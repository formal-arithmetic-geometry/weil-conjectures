+++
id = "pqf-lem-going-up"
kind = "lemma"
title = "Going up for an integral extension"
order = 533
uses = ["pqf-lem-lying-over"]
+++
Let $A\to B$ be integral, let
$\mathfrak p\subseteq\mathfrak p'$ be primes of $A$, and let
$\mathfrak q\subset B$ lie over $\mathfrak p$. There is a prime
$\mathfrak q'\supseteq\mathfrak q$ lying over $\mathfrak p'$.

## Proof

The induced map $A/\mathfrak p\hookrightarrow B/\mathfrak q$ is injective
and integral. Localize it at the complement of
$\mathfrak p'/\mathfrak p$. Apply lying over
([pqf-lem-lying-over]) to the maximal ideal of the localized
source. Pulling the resulting prime first back to $B/\mathfrak q$ and
then to $B$ gives $\mathfrak q'$; localization shows that its
contraction is exactly $\mathfrak p'$, and the quotient construction
gives $\mathfrak q\subseteq\mathfrak q'$.
