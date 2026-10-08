+++
id = "lem-a1-finite-length"
kind = "lemma"
title = "Finite length of a lisse Weil sheaf on a curve"
order = 2792
uses = ["def-weil-pbc-constructible-complexes", "def-wf-weil-category"]
+++
Let $C_0$ be a smooth geometrically connected curve and let
$\mathcal F$ be a lisse Weil sheaf
on $C_0$ (lisse in the sense of
[def-weil-pbc-constructible-complexes]). Then
$\mathcal F$ has finite length in the category of lisse Weil sheaves:
there is a finite Frobenius-stable filtration

$$
0=\mathcal F_0\subset\mathcal F_1\subset\cdots\subset\mathcal F_m=\mathcal F
$$

with each graded piece $\mathcal F_r/\mathcal F_{r-1}$ irreducible
(with respect to the Weil-sheaf structure).

## Proof

Every nonzero lisse Weil sheaf has a nonzero lisse Weil subsheaf:
if it is not irreducible, it admits a nonzero proper Weil subsheaf, and
a Weil subsheaf of a lisse sheaf on the connected curve with the
induced Frobenius structure. The rank strictly decreases, so induction
on the rank terminates, giving the filtration with irreducible graded
pieces.
