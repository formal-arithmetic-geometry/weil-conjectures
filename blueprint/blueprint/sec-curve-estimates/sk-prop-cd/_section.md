+++
id = "sk-prop-cd"
kind = "section"
title = "Vanishing in high degrees"
order = 987
uses = ["sk-def-av-pic", "sk-def-br", "sk-def-curve", "sk-prop-hilbert90", "sk-prop-kummer-exact", "sk-prop-tsen"]
+++
*Proposition (sketch).*

For $C$ as in [sk-def-curve], $n$ prime to $\operatorname{char}k$,
and every sheaf $F$ of $\Z/n$-modules on $C_{\Et}$ (more generally
every torsion sheaf whose torsion is prime to $\operatorname{char}k$):
$H^q(C,F)=0$ for $q\ge3$ (the étale cohomological dimension of a
curve over an algebraically closed field is $\le2$; the sharper
bound $\le1$ for $C$ affine is [sk-prop-cd-affine], and the
$p$-primary bound in characteristic $p$ goes through the
Artin–Schreier sequence). Consequently, for a complex $F$ in
$D^b(C_{\Et},\Z/n)$ with $\mathcal H^i(F)=0$ for $i>b$, one has
$H^q(C,F)=0$ for $q>b+2$; the shift cannot be dropped, since
$F=(\Z/2)[-3]$ on $\Pone$ has $H^3(\Pone,F)=H^0(\Pone,\Z/2)\neq0$.

## Proof

We first treat a single torsion sheaf $F$. The complex form then
follows from the hypercohomology spectral sequence
$E_2^{a,i}=H^a(C,\mathcal H^i(F))\Rightarrow H^{a+i}(C,F)$: its
$E_2$-terms vanish for $a\ge3$ by the sheaf case and for $i>b$ by
hypothesis, so $H^q(C,F)=0$ for $q>b+2$ (the shift $b$ stays in the
bound; it does not become $q\ge3$).
The argument of Blueprint 06b/06c runs at the generic point; it does
*not* pass through [sk-prop-cd-affine], so there is no circularity.

*Step 1 (reduce to a smooth integral curve).* Reduction is a
universal homeomorphism, so it does not change the étale site, and we may
take $C$ reduced. Normalize each of the finitely many irreducible
components in its own function field and let $h:C'\to C$ be the disjoint
union of the normalizations. It is finite and an isomorphism away from a
finite set $S$ of closed points, so the kernel and cokernel of
$F\to h_*h^*F$ live on $S$; a sheaf on a finite set of points over an
algebraically closed field is acyclic, so the two long exact sequences give
$H^q(C,F)\cong H^q(C',h^*F)$ for $q\ge2$, finite direct image being exact.
The one-dimensional components of $C'$ are regular, hence smooth over the
perfect ground field, and the zero-dimensional ones are points. So assume
$C$ smooth and integral.

*Step 2 (push to the generic point).* Let
$\eta:\Spec k(C)\to C$ be the generic point and $M=\eta^*F$. The kernel and
cokernel of $F\to\eta_*M$ have zero generic stalk. Such a sheaf is the
filtered union of its subsheaves vanishing off a finite set of closed
points, hence is again acyclic, and as in Step 1
$H^q(C,F)\cong H^q(C,\eta_*M)$ for $q\ge2$.

*Step 3 (the function field has cohomological dimension $\le1$).*
This is where Tsen enters. By [sk-prop-tsen] every finite extension $E$
of $k(C)$ is again $C_1$, so $\Br(E)=0$ ([sk-def-br]). On $\Spec E$ the
Kummer sequence ([sk-prop-kummer-exact]) together with
$H^1(E,\mathbb G_m)=\Pic(\Spec E)=0$ ([sk-prop-hilbert90]) embeds
$H^2(E,\mu_\ell)$ into $\Br(E)$, so $H^2(G_E,\mathbf F_\ell)=0$ for every
open subgroup $G_E$ of the absolute Galois group. A profinite group with
that property has $\ell$-cohomological dimension $\le1$: a Sylow
filtration reduces finite $\ell$-primary coefficients to $\mathbf F_\ell$,
restriction followed by corestriction is multiplication by a prime-to-$\ell$
index and hence invertible, and dimension shifting through coinduced
modules carries the vanishing of $H^2$ to all $q\ge2$. Therefore
$H^q(L,M)=0$ for $q\ge2$ and every algebraic extension $L$ of $k(C)$.

*Step 4 (the higher direct images of $\eta$).* At a closed point of
the smooth curve the strict local ring is a discrete valuation ring, and
its fraction field is an algebraic extension of $k(C)$, a strict
henselization being a filtered union of étale neighbourhoods. The stalk
of $R^q\eta_*M$ there is the cohomology of that fraction field, so
$R^q\eta_*M=0$ for $q\ge2$ by Step 3. The remaining sheaf $R^1\eta_*M$ has
zero generic restriction, hence is acyclic by Step 2.

*Step 5 (assemble).* The Grothendieck spectral sequence for sections
composed with $\eta_*$ reads
$H^a(C,R^b\eta_*M)\Rightarrow H^{a+b}(k(C),M)$. By Step 4 only $b=0$ and
$b=1$ occur, and the row $b=1$ contributes only at $a=0$; so in total
degree $q\ge3$ no differential meets $H^q(C,\eta_*M)$, which therefore
equals $H^q(k(C),M)=0$ by Step 3. With Step 2 this gives $H^q(C,F)=0$ for
$q\ge3$. The $p$-primary part in characteristic $p$ is the
Artin–Schreier bound, where $H^q(C,\mathcal O_C)$ is computed on the
étale site by descent for quasi-coherent modules.

Uses: [sk-def-br], [sk-def-curve], [sk-prop-hilbert90], [sk-prop-kummer-exact], [sk-prop-tsen]
