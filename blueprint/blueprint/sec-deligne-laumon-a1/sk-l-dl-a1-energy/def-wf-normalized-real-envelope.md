+++
id = "def-wf-normalized-real-envelope"
kind = "definition"
title = "Normalized real envelope"
order = 2764
uses = ["def-weil-punctual-weights", "def-wf-constant-weil-twist"]
+++
Let $\mathcal F$ be a lisse Weil sheaf punctually $\iota$-pure of
weight $w$ on a separated finite-type $k_0$-scheme, and fix
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$ as in
[def-weil-punctual-weights]. Using $\iota$, define

$$
b=\iota^{-1}\bigl(q^{-w/2}\bigr)\in\Qlb^\times,
\qquad
\mathcal F^0=\mathcal F\otimes\mathcal B_b,
$$

(where $\mathcal B_b$ is the
constant Weil twist of
[def-wf-constant-weil-twist]), and put

$$
\operatorname{Env}_\iota(\mathcal F;b)=\mathcal F^0\oplus
\bigl(\mathcal F^0\bigr)^\vee.
$$

This direct sum is the *normalized real envelope* associated with
$b$.
