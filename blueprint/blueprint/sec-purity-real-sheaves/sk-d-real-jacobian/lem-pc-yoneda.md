+++
id = "lem-pc-yoneda"
kind = "lemma"
title = "Yoneda"
order = 2607
+++
Let $S$ be a scheme. For any functor
$F:(\mathit{Sch}/S)^{\mathrm{op}}\to\textit{Sets}$ and any scheme $X/S$,
the map

$$
\operatorname{Hom}_{\textit{fun}}(h_X,F)\;\longrightarrow\;F(X),\qquad
\tau\;\longmapsto\;\tau_X(\mathrm{id}_X)
$$

is a bijection, natural in both arguments (Categories, Lemma 4.3.5, Tag
[001P](https://stacks.math.columbia.edu/tag/001P)).

*Mathlib:* `CategoryTheory.Functor.IsRepresentedBy`, `CategoryTheory.Functor.IsRepresentable`, `CategoryTheory.yoneda`. These are basic Mathlib notions used throughout, so they are not mapped as the Lean declarations of this object.

## Proof

Omitted. (Mathlib item.)
