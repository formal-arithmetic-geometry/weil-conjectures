+++
id = "def-amb-p1-trace"
kind = "definition"
title = "Projective-line trace before an exceptional adjoint"
order = 1571
uses = ["def-coefficient-twists-detailed", "lem-amb-proper-coproducts-projection", "thm-amb-p1-decomposition"]
+++
For $q:\mathbf P^1_S\to S$, define

$$
t_q:Rq_*A(1)[2]\longrightarrow A_S
$$

as the projection onto the second summand of
$Rq_*A(1)[2]\cong A_S(1)[2]\oplus A_S$.
Thus $t_q(h)=1$. For any complex $K$ put

$$
\epsilon_K:Rq_*q^*K(1)[2]
\cong K\otimes_A^LRq_*A(1)[2]
\xrightarrow{1\otimes t_q}K.
$$

The first isomorphism is the proper projection formula of
[lem-amb-proper-coproducts-projection].
The notation refers to the proved projective-line decomposition, and Tate twists.
