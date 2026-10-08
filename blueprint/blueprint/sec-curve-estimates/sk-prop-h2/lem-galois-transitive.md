+++
id = "lem-galois-transitive"
kind = "lemma"
title = "The action of $\\operatorname{Aut}(F)$ is transitive"
order = 972
uses = ["def-galois-category", "lem-galois-aut-profinite", "lem-galois-axioms", "lem-galois-object-exists"]
+++
Let $(\mathcal C,F)$ be a Galois category, $G=\operatorname{Aut}(F)$ and
$X$ connected. Then $G$ acts transitively on $F(X)$.

## Proof

We use the axioms of [def-galois-category] throughout.
Step 1: the directed system of Galois objects. Let $I$ be the set of
isomorphism classes of Galois objects, choose representatives $X_i$ and
elements $\gamma_i\in F(X_i)$. Write $i\ge i'$ if there is a morphism
$f_{ii'}:X_i\to X_{i'}$; post-composing with an automorphism of $X_{i'}$
we may assume $F(f_{ii'})(\gamma_i)=\gamma_{i'}$, and then $f_{ii'}$ is
unique by [lem-galois-axioms](5). The set $I$ is directed: for
$i_1,i_2$ apply [lem-galois-object-exists] to a connected component
of $X_{i_1}\times X_{i_2}$.
Step 2: $F$ is the colimit of the representable functors of the $X_i$.
Let $F'(X)=\varinjlim_I\operatorname{Mor}_{\mathcal C}(X_i,X)$ and define
$t_X(f)=F(f)(\gamma_i)$. Then $t_X$ is injective by
[lem-galois-axioms](5). For surjectivity let $\gamma\in F(X)$; by
axiom (2) we may assume $X$ connected, hence Galois by
[lem-galois-object-exists], so $X\cong X_i$ for some $i$, and
choosing the isomorphism carrying $\gamma_i$ to $\gamma$ (possible
since $X$ is Galois) exhibits $\gamma$ in the image. Hence $t$ is an
isomorphism.
Step 3: the group of the system. Put $A_i=\operatorname{Aut}(X_i)$. For
$i\ge i'$ there is a unique homomorphism $h_{ii'}:A_i\to A_{i'}$ with
$f_{ii'}\circ a=h_{ii'}(a)\circ f_{ii'}$ for all $a\in A_i$, defined
by $F(h_{ii'}(a))(\gamma_{i'})=F(f_{ii'}\circ a)(\gamma_i)$ and
[lem-galois-axioms](5); the $h$ are compatible and
$A_i\to A_{i'}$ is surjective because $F(X_i)\to F(X_{i'})$ is
surjective and $X_{i'}$ is Galois. Let $A=\varprojlim_IA_i$, profinite
by [lem-galois-aut-profinite] or directly as a limit of finite
groups. It acts on the system $(X_i)$ and hence on $F'$ by
precomposition, giving $A^{\mathrm{op}}\to G$. Since $A\to A_i$ is
surjective, $G$ acts transitively on $F(X_i)$ for every $i$.
Step 4: conclusion. Every connected object is dominated by some $X_i$
([lem-galois-object-exists]), and a morphism $X_i\to X$ of connected
objects is an epimorphism inducing a surjection
$F(X_i)\to F(X)$; transitivity on $F(X_i)$ therefore implies
transitivity on $F(X)$.
