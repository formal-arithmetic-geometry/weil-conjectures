+++
id = "def-sp-exact-couple"
kind = "definition"
title = "Bigraded exact couples"
order = 509
uses = ["def-sp-abelian"]
+++
Let $\mathcal A$ be an abelian category [def-sp-abelian]. An *exact couple*
$(D,E,\alpha,f,g)$ inside the bigraded objects $D=\bigoplus D^{p,q}$,
$E=\bigoplus E^{p,q}$ consists of maps of bidegrees

$$
 \alpha:D^{p,q}\to D^{p-1,q+1}\quad(-1,+1),\qquad
 f:E^{p,q}\to D^{p+2,q-1}\quad(+2,-1),\qquad
 g:D^{p,q}\to E^{p,q}\quad(0,0)
$$

such that the composite of two consecutive structure maps is zero and at
every $(p,q)$ the following exactness conditions hold (each comparing
subobjects of one single object):

$$
 \ker\!\Bigl(\alpha:D^{p,q}\to D^{p-1,q+1}\Bigr)
  =\operatorname{im}\!\Bigl(f:E^{p-2,q+1}\to D^{p,q}\Bigr),
$$

$$
 \ker\!\Bigl(f:E^{p,q}\to D^{p+2,q-1}\Bigr)
  =\operatorname{im}\!\Bigl(g:D^{p,q}\to E^{p,q}\Bigr),
$$

$$
  \ker\!\Bigl(g:D^{p,q}\to E^{p,q}\Bigr)
   =\operatorname{im}\!\Bigl(\alpha:D^{p+1,q-1}\to D^{p,q}\Bigr).
$$

(The bidegrees are those of the truncation couple of a t-structure
filtration, with the abutment in total degree $p+q$; they are the convention
in which the hypercohomology spectral sequence has $E_2^{p,q}\Rightarrow
\mathcal H^{p+q}$.) Setting $d:=g\circ f:E^{p,q}\to E^{p+2,q-1}$ (bidegree
$(+2,-1)$), the identity $f\circ g=0$ gives $d\circ d=0$, and the *derived
couple* is

$$
 D'^{p,q}:=\operatorname{im}\!\bigl(\alpha:D^{p+1,q-1}\to D^{p,q}\bigr),
 \qquad
 E'^{p,q}:=\frac{\ker\!\bigl(d:E^{p,q}\to E^{p+2,q-1}\bigr)}
                    {\operatorname{im}\!\bigl(d:E^{p-2,q+1}\to E^{p,q}\bigr)},
$$

with

$$
 \alpha':=\alpha|_{D'},\qquad
 f'(x):=f(x)\ \ (x\in\ker d),\qquad
 g'(y):=\overline{g(y')}\ \ (y=\alpha(y')\in D'^{p,q}),
$$

which is well defined because $f(\ker
d)\subseteq\ker g=\operatorname{im}\alpha$, because $d(g(y'))=g\circ f\circ
g\,(y')=0$, and because changing $y'$ by
$\ker\alpha=\operatorname{im}f$ changes $g(y')$ by $\operatorname{im}d$. The
*spectral sequence of the couple* is $E_2=E$, $d_2=d$, $E_3=E'$,
$d_3=g'\circ f'$ (bidegree $(+3,-2)$), and recursively $E_{r+1}=E'_r$, so
that $d_r$ has bidegree $(+r,1-r)$ for $r\geq2$.

(Stacks Project: Definitions 12.21.1 and 12.21.3 (Tags
[011Q](https://stacks.math.columbia.edu/tag/011Q),
[011S](https://stacks.math.columbia.edu/tag/011S)), Lemma 12.21.2 (Tag
[011R](https://stacks.math.columbia.edu/tag/011R)), and the shift-functor
variant Remark 12.21.5 (Tag
[011U](https://stacks.math.columbia.edu/tag/011U)).)
