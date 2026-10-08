+++
id = "lem-sc-four-lemma"
kind = "lemma"
title = "The four lemma for exact hexagons"
order = 695
+++
Let
$0\to X_1\to X_2\to X_3\to X_4\to X_5\to X_6\to0$ and
$0\to Y_1\to Y_2\to Y_3\to Y_4\to Y_5\to Y_6\to0$ be exact
sequences of abelian groups with homomorphisms
$f_i:X_i\to Y_i$, $1\leq i\leq6$, making all squares commute.
If $f_2,f_3,f_5,f_6$ are isomorphisms, then so are $f_1$ and
$f_4$.

## Proof

For $f_1$: by exactness the maps $X_1\to X_2$ and $Y_1\to Y_2$
are injective and

$$
X_1\cong\operatorname{im}(X_1\to X_2)=\ker(X_2\to X_3)
\cong\ker(Y_2\to Y_3)=\operatorname{im}(Y_1\to Y_2)\cong Y_1,
$$

the middle isomorphism being the restriction of $f_2$ to kernels
(which uses the commuting of the squares and the isomorphisms
$f_2,f_3$), and the composite is $f_1$ (the squares commute).
For $f_4$, injectivity: if $f_4(x_4)=0$, then, denoting the maps
of the $X$-row by $i_k$ and those of the $Y$-row by $j_k$,
$f_5i_4(x_4)=j_4f_4(x_4)=0$; injectivity of $f_5$ gives
$x_4\in\ker i_4=\operatorname{im}i_3$, so $x_4=i_3(x_3)$ for
some $x_3$. The equality $j_3f_3(x_3)=f_4i_3(x_3)=0$ says
$f_3(x_3)\in\ker j_3=\operatorname{im}j_2$, so $f_3(x_3)=j_2(y_2)$ for
some $y_2$, and $y_2=f_2(x_2)$ for a unique $x_2$ (as $f_2$
is an isomorphism); then
$f_3(x_3)=j_2f_2(x_2)=f_3i_2(x_2)$, so
$f_3(x_3-i_2(x_2))=0$, i.e. $x_3=i_2(x_2)$ (as $f_3$ is injective), and then
$x_4=i_3(x_3)=i_3i_2(x_2)=0$ by exactness at $X_3$.
Surjectivity: let $y_4\in Y_4$. Then
$y_5:=j_4(y_4)\in\ker j_5$, and $y_5=f_5(x_5)$ for some $x_5$
($f_5$ surjective); $j_5f_5(x_5)=f_6i_5(x_5)=0$, and $f_6$ is
injective, so $i_5(x_5)=0$, i.e. $x_5\in\ker i_5= \operatorname{im}i_4$: $x_5=i_4(x_4')$ for some $x_4'\in X_4$.
Then $y_4-f_4(x_4')$ maps to $j_4(y_4)-j_4f_4(x_4')= j_4(y_4)-f_5i_4(x_4')=y_5-f_5(x_5)=0$, so
$y_4-f_4(x_4')\in\ker j_4=\operatorname{im}j_3$:
$y_4-f_4(x_4')=j_3(y_3)$ for some $y_3$, and $y_3=f_3(x_3)$
for some $x_3$ ($f_3$ surjective), whence
$y_4=f_4(x_4')+f_4i_3(x_3)=f_4(x_4'+i_3(x_3))$.
