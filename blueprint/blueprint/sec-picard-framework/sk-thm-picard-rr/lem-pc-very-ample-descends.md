+++
id = "lem-pc-very-ample-descends"
kind = "lemma"
title = "Very ampleness descends along field extensions"
order = 742
uses = ["def-pc-base-change", "def-pc-morphism-conventions", "def-pc-picard-presheaf", "def-sc-ample", "def-sc-invertible-module", "lem-pc-very-ample-ample", "lem-sc-flat-base-change-coherent"]
+++
Let $k$ be a field, $X$ a scheme of finite type over $k$ and $\mathcal{L}$ an
invertible module on $X$ such that $\mathcal{L}_K$ is
very ample on $X_K$ for a field extension
$K/k$. Then $\mathcal{L}$ is very ample on $X$; in particular $\mathcal{L}$ is
ample if $\mathcal{L}_K$ is.

## Proof

By definition of very ampleness there is an immersion
$i:X_K\to\mathbf P^N_K$ with $i^*\mathcal{O}_{\mathbf P^N}(1)=\mathcal{L}_K$. The
sections $x_1,\dots,x_N$ of $\mathcal{O}_{\mathbf P^N}(1)$ pull back to
sections $s_j$ of $\mathcal{L}_K$ which $K$-linearly generate
$H^0(X_K,\mathcal{L}_K)=H^0(X,\mathcal{L})\otimes_kK$
([lem-sc-flat-base-change-coherent]; the finite generation of the
sections of $i^*\mathcal{O}(1)$: the morphism $i$ is the morphism of the
sections; more precisely the immersion $i$ is given by base point free
sections $t_0,\dots,t_N\in H^0(X_K,\mathcal{L}_K)$ separating points and
tangent directions). Each $t_j$ is a finite combination
$\sum_ac_a u_a$ of elements $u_a\in H^0(X,\mathcal{L})$ (tensor structure
$H^0(X_K,\mathcal{L}_K)=H^0(X,\mathcal{L})\otimes_kK$), so the finite set
$\mathcal U=\{u_a\}\cup\{t_j\}$ of elements of $H^0(X,\mathcal{L})^{\otimes}_k$
(different powers twist to: the $x_j$'s are sections of
$\mathcal{O}(1)$, the $t_j$'s of $\mathcal{L}$; all are sections of $\mathcal{L}$; the
separability: the map to the projective space of the corresponding
subspace of $H^0(X,\mathcal{L})$ (the subspace $V$ spanned by the $u_a$'s)
after base change to $K$ contains the defining sections
$t_0,\dots,t_N$, so the morphism
$\psi:X\to\mathbf P(V)$ (from the $k$-subspace $V$ of $H^0(X,\mathcal{L})$)
has base change $\psi_K:X_K\to\mathbf P(V_K)$ such that $\psi_K=i$
(the same sections): $\psi_K$ is an immersion, and the descent of the
immersion property along a faithfully flat (field) base extension
(Descent, Lemma 35.37.2 for closed immersions and the standard
descendability of open immersions – or: the classical statement: the
property "the morphism of a finite type scheme to projective space
defined by base-point-free sections is an immersion" is descent-stable
because it is precisely the condition that the base-point-freeness and
separation hold, and these conditions are tested on the geometric
points: for the closed-immersion picture of the
$\Gamma$-sections, effective descent along fields for closed
immersions is formal from the affine case along
$k'\to k''$: $A\to A/I$ base changes, and descent of ideals:
$I\otimes_{k'}k''$-preimage: the ideal of a closed subscheme over a
finitely generated subextension is the span of finitely many
elements; descent is classical) gives that $\psi$ is an immersion.
Hence $\mathcal{L}$ is very ample over $k$ ($\psi^*\mathcal{O}_{\mathbf P(V)}(1)=\mathcal{L}$
by construction), and $X$ proper
($\mathbf P(V)$ and the immersion give the image-closedness over $k$),
and ampleness: a very ample module is ample (the
$X_s$-affine basis property, as in
[def-sc-ample] and [lem-pc-very-ample-ample]).
