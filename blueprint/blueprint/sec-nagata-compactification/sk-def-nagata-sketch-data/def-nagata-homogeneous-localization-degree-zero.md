+++
id = "def-nagata-homogeneous-localization-degree-zero"
kind = "definition"
title = "Degree-zero homogeneous localization"
order = 8
lean = ["HomogeneousLocalization.Away"]
+++
Let $R=\bigoplus_{n\geq0}R_n$ be an $\mathbb N$-graded commutative ring and
let $f\in R_d$ be homogeneous with $d>0$. Write $R_{(f),0}$ for the
degree-zero part of the homogeneous localization supplied by Mathlib's
`HomogeneousLocalization.Away`. Its elements are represented by

$$
\frac{x}{f^m},\qquad x\in R_{md},\quad m\geq0,
$$

modulo the ordinary localization relation. This block fixes the notation
used by the chart statements; it does not introduce a second localization
implementation.
