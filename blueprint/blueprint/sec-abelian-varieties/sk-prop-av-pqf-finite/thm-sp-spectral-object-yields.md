+++
id = "thm-sp-spectral-object-yields"
kind = "theorem"
title = "The spectral sequence of a filtered complex"
order = 515
uses = ["def-sp-convergence", "def-sp-exact-couple", "def-sp-filtration", "def-sp-spectral-sequence", "lem-sp-couple-morphism", "lem-sp-long-exact-of-triangle", "lem-sp-page-induction"]
+++
Let $\mathcal A$ be an abelian category and let $K^\bullet$ be a complex in
$\mathcal A$ equipped with a decreasing filtration
[def-sp-filtration] $F^\bullet K^\bullet$ by subcomplexes which is *bounded*:
for every degree $n$ one has $F^pK^n=K^n$ for $p\ll0$ and $F^pK^n=0$ for
$p\gg0$. For $p\leq q$ put

$$
 X^{[p,q]}:=F^pK^\bullet/F^qK^\bullet ,
$$

so that $0\to X^{[q,r]}\to X^{[p,r]}\to X^{[p,q]}\to0$ is a short exact
sequence of complexes for $p\leq q\leq r$. Then:

- (a) there is a cohomological spectral sequence [def-sp-spectral-sequence]
  $\bigl(E_r^{p,q},d_r\bigr)_{r\geq1}$ with
  $$
   E_1^{p,q}=H^{p+q}\bigl(X^{[p,p+1]}\bigr)
   =H^{p+q}\bigl(\operatorname{gr}^pK^\bullet\bigr),
   \qquad
   d_r:E_r^{p,q}\longrightarrow E_r^{p+r,q-r+1},
  $$
  the differential $d_1$ being the boundary homomorphism of the long exact
  cohomology sequence of the displayed short exact sequence with $(p,q,r)$
  replaced by $(p,p+1,p+2)$, and with, for every $r\geq1$ and every $N\geq
  r$, $E_r^{p,q}\cong Z_r^{p,q}/B_r^{p,q}$, where
  $$
  \begin{gathered}
  Z_r^{p,q}=\operatorname{im}\bigl(H^{p+q}(X^{[p,p+N]})\to
   H^{p+q}(X^{[p,p+r]})\bigr),\\
   B_r^{p,q}=\operatorname{im}\bigl(H^{p+q}(X^{[p-r+1,p+N]})\to
   H^{p+q}(X^{[p,p+r]})\bigr),
  \end{gathered}
  $$
  and with the identification $\mathcal H(E_r)\cong E_{r+1}$ natural;
- (b) the induced filtration
  $F^pH^n(K^\bullet):=\operatorname{im}\bigl(H^n(F^pK^\bullet)\to
  H^n(K^\bullet)\bigr)$ is finite and separated on each $H^n(K^\bullet)$, and
  there are natural isomorphisms
  $E_\infty^{p,q}\cong\operatorname{gr}^pH^{p+q}(K^\bullet)$ in the sense of
  [def-sp-convergence]: the spectral sequence converges to the cohomology of
  $K^\bullet$;
- (c) the construction is functorial in the pair
  $(K^\bullet,F^\bullet K^\bullet)$;
- (d) first-quadrant variant: if in addition $F^pK^\bullet=K^\bullet$ for
  $p\leq0$ and the graded pieces $\operatorname{gr}^pK^\bullet$ have
  cohomology concentrated in degrees $[p,p+1]$, then $E_r^{p,q}=0$ unless
  $p\geq0$ and $q\geq0$, and the entries stabilize for $r>\max(p,q)+1$.

**Status.** This is the standard spectral sequence of a bounded filtered
complex, proved from the chapter's own exact-couple machinery; the user of an
earlier page formula, [thm-sp-if-e1], has been rewired accordingly.

## Proof

Step 1: the exact couple. The short exact sequences $0\to F^{p+1}K^\bullet\to
F^pK^\bullet\to\operatorname{gr}^pK^\bullet\to0$ have long exact cohomology
sequences, exact by the long exact sequence of a short exact sequence of
complexes ([lem-sp-long-exact-of-triangle]), namely

$$
 \cdots\to H^{p+q}(F^{p+1}K^\bullet)\xrightarrow{\ \alpha\ }
 H^{p+q}(F^pK^\bullet)\xrightarrow{\ g\ }
 H^{p+q}(\operatorname{gr}^pK^\bullet)\xrightarrow{\ f\ }
 H^{p+q+1}(F^{p+1}K^\bullet)\to\cdots .
$$

They assemble into a bigraded exact couple [def-sp-exact-couple] with
$D_1^{p,q}=H^{p+q}(F^pK^\bullet)$ and
$E_1^{p,q}=H^{p+q}(\operatorname{gr}^pK^\bullet)$, the maps $\alpha,g,f$
having bidegrees $(-1,+1)$, $(0,0)$, $(+1,0)$; the exactness required of a
couple is exactly the exactness of these sequences.

Step 2: the pages. The derived couples of [def-sp-exact-couple] produce a
spectral sequence [def-sp-spectral-sequence] whose differentials $d_r=g_r\circ
f_r$ have bidegree $(+r,1-r)$, that is $d_r:E_r^{p,q}\to E_r^{p+r,q-r+1}$,
and whose page identification $\mathcal H(E_r)\cong E_{r+1}$ is the one
recorded in [lem-sp-page-induction]. The identification
$E_1^{p,q}=H^{p+q}(\operatorname{gr}^pK^\bullet)$ is the definition of the
first derived couple, and the differential $d_1$ is by the same definition
the composite $g_1f_1$, i.e. the boundary homomorphism of the long exact
sequence displayed in Step 1 with $(p,q,r)$ replaced by $(p,p+1,p+2)$.

Step 3: the $Z/B$ description. Induction on $r$ shows that $D_r^{p,q}$ is the
image of $H^{p+q}(F^{p+r-1}K^\bullet)$ in $H^{p+q}(X^{[p,p+N]})$ and that
$E_r^{p,q}=g_r(D_r^{p,q})$; unwinding the two maps of the couple gives the
displayed descriptions of $Z_r^{p,q}$ and $B_r^{p,q}$. Here $N\geq r$ may be
taken arbitrarily large: the filtration is bounded, so on the finitely many
degrees that contribute to a fixed total degree $p+q$ one has $F^{p+N}K^n=0$
for $N$ large, and there $F^pK^\bullet=X^{[p,p+N]}$.

Step 4: convergence. Boundedness gives
$F^pH^n(K^\bullet)=H^n(K^\bullet)$ for $p\ll0$ and $F^pH^n(K^\bullet)=0$ for
$p\gg0$, so the induced filtration is finite and separated; for $r>2N$ the
pages $E_r^{p,q}$ stabilize, and the description of Step 3 identifies the
stable value with
$F^pH^{p+q}(K^\bullet)/F^{p+1}H^{p+q}(K^\bullet)$. This is the convergence
statement of [def-sp-convergence], and it is (b).

Step 5: functoriality and the first-quadrant variant. A morphism of filtered
complexes induces a morphism of the exact couples of Step 1, hence a morphism
of spectral sequences by [lem-sp-couple-morphism]; the construction is
natural in the pair $(K^\bullet,F^\bullet K^\bullet)$, which is (c). If
$F^pK^\bullet=K^\bullet$ for $p\leq0$ and $\operatorname{gr}^pK^\bullet$ has
cohomology concentrated in degrees $[p,p+1]$, then
$E_1^{p,q}=H^{p+q}(\operatorname{gr}^pK^\bullet)=0$ unless $p\geq0$ and
$0\leq q\leq1$; the differentials have bidegree $(+r,1-r)$, so the entries
outside the first quadrant stay zero on every page, the page identification
being a passage to subquotients, and no differential enters or leaves a fixed
entry once $r>\max(p,q)+1$, since $p+r>p$ or $q-r+1<q$ forces the target out
of the quadrant. This is (d).
