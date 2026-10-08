+++
id = "thm-pd-spreading-out"
kind = "theorem"
title = "Descent of finitely presented data at a filtered limit"
order = 862
uses = ["def-pc-base-change", "def-pc-morphism-conventions"]
+++
Let $I$ be a directed set, let $(S_i,f_{ii'})$ be an inverse system of schemes
over $I$ with affine transition morphisms and $S_i$ quasi-compact and
quasi-separated, and put $S=\varprojlim_iS_i$. Then:

1. for every morphism of finite presentation $V\to S$ there are $i\in I$ and
a morphism of finite presentation $V_i\to S_i$ with
$V\cong V_i\times_{S_i}S$;
1. given $i$, schemes $V_i,W_i$ of finite presentation over $S_i$ and a
morphism $\psi:V_i\times_{S_i}S\to W_i\times_{S_i}S$, there are $i'\geq i$
and a morphism $\psi_{i'}:V_i\times_{S_i}S_{i'}\to W_i\times_{S_i}S_{i'}$
whose base change to $S$ is $\psi$;
1. given $i$, schemes $V_i,W_i$ of finite presentation over $S_i$ and two
morphisms $\psi_i,\chi_i:V_i\to W_i$ whose base changes to $S$ agree,
there is $i'\geq i$ with
$\psi_i\times_{S_i}S_{i'}=\chi_i\times_{S_i}S_{i'}$.

This is Stacks Project, Limits of Schemes, Lemma 32.10.1, Tag
[01ZM](https://stacks.math.columbia.edu/tag/01ZM).

## Proof

This is Stacks Project, Limits of Schemes, Lemma 32.10.1, Tag
[01ZM](https://stacks.math.columbia.edu/tag/01ZM); the proof is the
standard reduction to the affine case, where it is Algebra, Lemma 10.127.8,
Tag [05N9](https://stacks.math.columbia.edu/tag/05N9): a finitely
presented algebra is the colimit of its finitely generated subalgebras, and
two maps out of a finitely presented algebra agree after passing to a
sufficiently large stage. The passage from the affine case to the general
case is carried out in loc. cit. by choosing finite affine open coverings and
glueing; the three assertions are proved there in the order (3), (2), (1), and
we use them in that order. The only two notions of
[def-pc-morphism-conventions], [def-pc-base-change] that the statement needs
are ``of finite presentation'' and the fibre product $V_i\times_{S_i}S$, which
are the ones appearing in its three clauses. We record the statement here
because the chapter needs exactly those clauses, and because the generality of
the cover $\Spec(k_s)\to\Spec(k)$ is what forces this detour through a filtered
limit.
