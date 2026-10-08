+++
id = "thm-sp-half-plane-convergence"
kind = "theorem"
title = "Half-plane convergence"
order = 511
uses = ["def-sp-convergence", "def-sp-exact-couple", "def-sp-filtration"]
+++
Let $(D,E_2,\alpha,f,g)$ be the exact couple of
[def-sp-exact-couple]. Assume $D^{p,q}=0$ for $q<a$, and $E_2^{p,q}=0$ unless
$p\geq0$ and $q\geq a$. Put $A^n=D^{0,n}$. Then total degree $n$ contains
only $a\leq q\leq n$, and each entry $E_r^{p,q}$ has stabilized when

$$
 r>\max(q-a+1,\,p),
$$

with the canonical identification $E_r^{p,q}=E_{r+1}^{p,q}$ supplied by page
cohomology. For $q\leq n$, set
$G_qA^n=\operatorname{im}(D^{n-q,q}\xrightarrow{\alpha^{n-q}}A^n)$, and set
$G_qA^n=A^n$ for $q\geq n$. The decreasing filtration
[def-sp-filtration] $F^pA^n=G_{n-p}A^n$ is finite, exhaustive and separated,
and $E_\infty^{p,q}\cong F^pA^{p+q}/F^{p+1}A^{p+q}$. The couple is regular
and complete in the sense of [def-sp-convergence].

## Proof

The page region gives $p\geq0$ and $q\geq a$; on $p+q=n$ these inequalities
give the finite interval $a\leq q\leq n$, so each total degree contains
finitely many entries. For an entry $(p,q)$, the incoming differentials at
page $r$ are

$$
  d_r:E_r^{p-r,q+r-1}\longrightarrow E_r^{p,q},
$$

whose source has first index $p-r<0$, hence vanishes when $r>p$; the outgoing
differentials are

$$
  d_r:E_r^{p,q}\longrightarrow E_r^{p+r,q-r+1},
$$

whose target has second index $q-r+1<a$, hence vanishes when $r>q-a+1$. The
degrees are those of [def-sp-exact-couple]. For $r>\max(q-a+1,p)$, taking
page cohomology identifies the two successive entries. The recursive
subobjects of [def-sp-convergence] therefore stabilize, giving regularity.
For completeness,

$$
 \operatorname{im}(\alpha^r)^{p,q}
 =\operatorname{im}\bigl(\alpha^r:D^{p+r,q-r}\to D^{p,q}\bigr)=0
$$

for $r>q-a$, by the stated hypothesis on $D$. Exactness of the original
couple shows that $\alpha:D^{n-q+1,q-1}\to D^{n-q,q}$ is an isomorphism for
$q>n$: both adjacent $E_2$-terms have negative first index. Thus $A^n$ is the
stable value of this system. Its image filtration has $G_q=0$ for $q<a$ and
$G_q=A^n$ for $q\geq n$.

For completeness, the associated graded calculation can be read directly in
the iterated exact couple. At page $r$, its $D_r$ term at $(u,v)$ is
$\operatorname{im}(D^{u+r-2,v-r+2}\to D^{u,v})$. For $r$ sufficiently large,
the term which maps to $E_r^{p,q}$ is consequently $G_qA^{p+q}$; the image of
the preceding $\alpha_r$-map is $G_{q-1}A^{p+q}$. The following $D_r$-term is
zero, since its source has second index $q-r+1<a$. Exactness therefore gives
$E_r^{p,q}=G_qA^{p+q}/G_{q-1}A^{p+q}$. This is the asserted associated graded
of [def-sp-filtration], and proves convergence in the sense of
[def-sp-convergence].

(Stacks Project: Lemma 12.21.4 (Tag
[011T](https://stacks.math.columbia.edu/tag/011T): $Z_r$, $B_r$ and the rule
for $d_{r+1}$); Lemma 12.23.5 (Tag
[012F](https://stacks.math.columbia.edu/tag/012F): $E_\infty$ and the
associated graded of the cohomology).)
