+++
id = "lem-sc-degree-2g1-very-ample"
kind = "lemma"
title = "Line bundles of large degree are very ample"
order = 718
uses = ["def-sc-ample", "def-sc-curves", "def-sc-genus", "def-sc-pic0", "lem-sc-dim0-finite", "lem-sc-riemann-roch-large-degree", "thm-pqf-finite-iff-proper-finite-fibres"]
+++
Let $C$ be a proper smooth connected curve of
genus $g$ ([def-sc-genus]) over an algebraically closed
field $k$, and $\mathcal M$ a line bundle on $C$ with
$\deg\mathcal M\geq2g+1$ ([def-sc-pic0]). Then
$\mathcal M$ is very ample.

## Proof

Write $d=\deg\mathcal M$. By [lem-sc-riemann-roch-large-degree], every
line bundle $\mathcal N$ on $C$ of degree at least $2g-1$ satisfies
$\dim H^0(C,\mathcal N)=\deg\mathcal N+1-g$. For points $P,Q\in C$
(possibly equal), $\deg$ is a homomorphism with $\deg\mathcal O_C(P)=1$
([def-sc-pic0]), so $\mathcal M$, $\mathcal M(-P)$ and $\mathcal M(-P-Q)$
have degrees $d\geq2g+1$, $d-1\geq2g$ and $d-2\geq2g-1$. Hence

$$
\dim H^0(C,\mathcal M(-P))=\dim H^0(C,\mathcal M)-1,\qquad
\dim H^0(C,\mathcal M(-P-Q))=\dim H^0(C,\mathcal M)-2.
$$

These
dimension drops say exactly that the complete linear system
$|\mathcal M|$ is base point free and separates points and
tangent vectors: the drop for $\mathcal M(-P)$ gives a section
not vanishing at $P$; the drop for $\mathcal M(-P-Q)$ with
$P\neq Q$ gives a section vanishing at $P$ but not at $Q$
(and one vanishing at $Q$ but not at $P$); and with $P=Q$ it
gives a section vanishing at $P$ to order exactly one.

We now prove that these properties make the map
$\varphi:C\to\mathbf P^N$ associated to the complete linear
system $|\mathcal M|$ a closed immersion. A section vanishing
at $P$ but not at $Q$ shows $\varphi(P)\neq\varphi(Q)$. A
section vanishing at $P$ to order exactly one shows that
$d\varphi_P$ is injective (a tangent direction at $P$ is a
first-order deformation of $P$, and such a section separates it
from the trivial deformation), and the injectivity of
$d\varphi_P$ for all $P$ is equivalent to
$\Omega_{C/\mathbf P^N}=0$ (the fibre of
$\Omega_{C/\mathbf P^N}$ at $P$ is the dual of the cokernel of
the tangent map; *reference: Stacks Project, Morphisms of
Schemes: unramified morphisms*), i.e. $\varphi$ is unramified.
An unramified morphism has finite fibres (a scheme of finite type
over a field with vanishing sheaf of differentials is a finite
disjoint union of points: its irreducible components have function
fields with no differentials, hence are algebraic over the base
field, so the dimension is zero and
[lem-sc-dim0-finite] applies). Thus $\varphi$ is proper
(a morphism of proper schemes) with finite fibres, hence finite
([thm-pqf-finite-iff-proper-finite-fibres] of the quasi-finite chapter;
*reference: Stacks Project, Cohomology of Schemes,
[Tag 02OG](https://stacks.math.columbia.edu/tag/02OG): proper and quasi-finite implies finite*).
Finally, $\varphi$ is finite and injective on closed points: its
image $\varphi(C)\subset\mathbf P^N$ is closed, and for
$y=\varphi(P)\in\varphi(C)$ the fibre is the single point $P$
with residue field $k$ ($k$ algebraically closed), so
$(\varphi_*\mathcal O_C)_y\otimes k(y)=k$; by Nakayama's lemma
$\mathcal O_{\mathbf P^N,y}\to(\varphi_*\mathcal O_C)_y$ is
surjective, hence an isomorphism (it is injective because
$\varphi$ is dominant onto $\varphi(C)$), and $\varphi$ is
an isomorphism onto $\varphi(C)$, i.e. a closed immersion.
Hence $\mathcal M$ is very ample.
