+++
id = "sk-d-setup"
kind = "section"
title = "Coefficients and geometric categories"
order = 2266
lean = ["AlgebraicGeometry.ProEtale.GeometricCoefficients"]
+++
*Remark (sketch).*

Fix $q=p^r$, $k=\overline{\mathbf F}_q$, $s=\operatorname{Spec}k$, a prime
$\ell\ne p$, a finite extension $E/\mathbf Q_\ell$ with uniformizer $\varpi$,
and $A=\mathcal O_E/\varpi^n$, $n\ge1$.
A geometric scheme is separated and of finite type over $k$; its structure
map is $a_X:X\to s$. Maps between geometric schemes are $k$-maps, and
unsubscripted products are over $s$.
Dimension is the supremum of lengths of chains of irreducible closed
subsets. Reduction means quotienting the structure sheaf by its nilradical.
A universal homeomorphism is a morphism inducing a homeomorphism after
every base change. These terms are used only in the final reduction steps.
Write $D(X,A)$ for the ordinary derived category of sheaves of $A$-modules
on $X_{\mathrm{pro\acute et}}$, and $D^b_{ctf}(X,A)$ for its bounded
constructible objects of finite Tor-amplitude. For a commutative ring $R$,
$\Perf(R)\subset D(R)$ consists of objects represented by bounded complexes
of finitely generated projective $R$-modules.
