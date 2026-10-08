+++
id = "lem-pur-lisse-morphism-rigidity"
kind = "lemma"
title = "Rigidity of morphisms of finite locally constant sheaves"
order = 1957
uses = ["def-pur-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-scheme-morphism-properties", "lem-cbc-proetale-stalk-conservative"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $T$ be a separated
finite-type $k$-scheme and let $L,M$ be finite locally constant
$\Lambda$-sheaves on $T$.

1. *the Hom sheaf.* The
[def-weil-derived-pullback-tensor-hom] internal Hom sheaf
$\mathcal Hom(L,M)$ is finite locally constant on $T$.
1. *rigidity of sections.* If a morphism $\varphi:L\to M$
vanishes at one geometric point of every connected component of
$T$, then $\varphi=0$. In particular, if $T$ is connected,
two morphisms $L\to M$ which agree at one geometric point of
$T$ agree everywhere.

## Proof

Step 1: (1). By [def-weil-scheme-morphism-properties] a sheaf is
locally constant if it becomes constant after pullback along a covering
family of the site; there is a covering family along which both $L$
and $M$ become constant, namely a common refinement of a covering
trivializing $L$ and one trivializing $M$. Formation of the
internal Hom of [def-weil-derived-pullback-tensor-hom] commutes
with pullback, so on that covering $\mathcal Hom(L,M)$ becomes the
constant sheaf with value the finite $\Lambda$-module of morphisms of
the two stalks; its stalks are therefore finite, and it is finite
locally constant.
Step 2: (2). The zero locus of a section of a locally constant sheaf is
open and closed: on a covering trivializing the sheaf, the section
corresponds to a locally constant function with values in a discrete
set, whose zero locus is open and closed, and the assertion descends
because vanishing is a local condition on the site. Apply this to the
section $\varphi$ of the finite locally constant sheaf
$\mathcal Hom(L,M)$ of (1), with the stalks and the geometric points
of [def-weil-scheme-morphism-properties] used to test vanishing:
the zero locus is a union of connected components of $T$, and it
contains one geometric point of every connected component, hence it is
all of $T$: the section $\varphi$ vanishes on all of $T$. To
deduce $\varphi=0$, let $\{v_i:W_i\to T\}$ be the common refinement
of Step 1, along which both $L$ and $M$ become constant. By clause
(1) of [lem-cbc-proetale-stalk-conservative] it suffices to prove
$v_i^*\varphi=0$ for every $i$, inverse image along a member of a
pro-etale covering family reflecting vanishing, and by Step 1
$v_i^*\mathcal Hom(L,M)$ is the constant sheaf with value the finite
$\Lambda$-module $\operatorname{Hom}_\Lambda(L_0,M_0)$. A section of
that constant sheaf is a locally constant function on $W_i$ with
values in a discrete set; it vanishes at every geometric point of
$W_i$, because $\varphi$ vanishes on all of $T$ and every point of
$W_i$ is the image of a geometric point, and a locally constant
function with values in a discrete set that vanishes at every point is
zero. Hence $v_i^*\varphi=0$ and therefore $\varphi=0$. The final
assertion is the first one applied to the difference of the two
morphisms.
