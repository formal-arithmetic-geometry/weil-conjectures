+++
id = "lem-trf-exceptional-internal-hom-exchange"
kind = "lemma"
title = "Exceptional internal Hom versus exceptional pullback"
order = 2315
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-tor-amplitude", "prop-functor-package"]
+++
Fix the coefficient
conventions, $A=A_{E,n}$, and let $c:C\to Z$ be a separated
finite-type morphism of finite-type $k$-schemes which is admissible at
$A$ ([def-trf-admissibility]). For
$M,N\in D^b_{ctf}(Z,A)$ the canonical comparison

$$
R\mathcal Hom_A\bigl(c^*M,c^!N\bigr)\xrightarrow{\ \sim\ }
c^!R\mathcal Hom_A(M,N)
$$

is an isomorphism, natural in $M$ and $N$. Its first variable is
required to be an ordinary pullback and its second an exceptional one;
the analogous statement with $c^!$ in the first variable is false, as
recorded in [def-trf-admissibility].

## Proof

Let $P\in D^b_{ctf}(C,A)$ be a test object. The exceptional adjunction
of [def-trf-admissibility] and the tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom] give the chain

$$
\begin{aligned}
\operatorname{Hom}_C\bigl(P,R\mathcal Hom_A(c^*M,c^!N)\bigr)
&\cong\operatorname{Hom}_C\bigl(P\otimes_A^Lc^*M,c^!N\bigr)\\
&\cong\operatorname{Hom}_Z\bigl(c_!\bigl(P\otimes_A^Lc^*M\bigr),N\bigr)\\
&\cong\operatorname{Hom}_Z\bigl(c_!P\otimes_A^LM,N\bigr)\\
&\cong\operatorname{Hom}_Z\bigl(c_!P,R\mathcal Hom_A(M,N)\bigr)\\
&\cong\operatorname{Hom}_C\bigl(P,c^!R\mathcal Hom_A(M,N)\bigr),
\end{aligned}
$$

in which the third arrow is the projection formula of
[prop-functor-package] for the admissible $c$, applied to the
first tensor factor, and the remaining arrows are the two adjunctions.
Every arrow is natural in $P$, so the Yoneda lemma identifies the two
representable functors of $P$ and produces the canonical comparison of
the statement. Naturality in $M$ and $N$, and compatibility with
shifts and distinguished triangles, are the corresponding properties of
the adjunctions and of the projection formula.
