+++
id = "lem-exc-proetale-closed-exact"
kind = "lemma"
title = "Exactness of closed direct image"
order = 1855
uses = ["def-weil-pbc-proetale-operations", "def-weil-pbc-scheme-conventions", "lem-exc-closed-cover-extension", "lem-exc-closed-localization", "lem-weil-pbc-ind-etale-basis"]
+++
Let $i:Z\hookrightarrow X$ be a closed immersion whose complementary open
immersion is quasi-compact. Then $i_*$ is exact on all pro-etale module
sheaves over a finite constant ring.

## Proof

As a right adjoint in the pro-etale operations, $i_*$ preserves kernels. We
prove that it preserves epimorphisms by local lifting of sections. Work on
an affine open of $X$ and a basis object $W$, using
[lem-weil-pbc-ind-etale-basis], [lem-exc-closed-localization]. Let $G\to H$
be an epimorphism on $Z$ and let $s\in(i_*H)(W)=H(Z_W)$. This section lifts
to $G$ on a covering of $Z_W$; choose a finite affine ind-etale refinement
by [lem-weil-pbc-ind-etale-basis].

The complement of $Z_W$ is quasi-compact, because the open immersion is the
base change of the quasi-compact complement in the statement. By
[lem-exc-closed-cover-extension], extend the chosen covering to $W$. On each
lifted member, its reduction is the member of the original closed covering,
so the chosen section of $G$ is a lift in $i_*G$. On the remaining open
members the reduction is empty and the section is zero, which also lifts.
Thus $i_*G\to i_*H$ is locally surjective on every basis object and hence an
epimorphism. This proves exactness. The needed finiteness condition is on
the open complement, as in [Stacks Project, Section
61.25](https://stacks.math.columbia.edu/tag/09A9); no condition on the
values of a right adjoint was used.
