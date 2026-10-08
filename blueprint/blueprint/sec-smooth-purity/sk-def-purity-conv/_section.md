+++
id = "sk-def-purity-conv"
kind = "section"
title = "Purity conventions and the rank-one datum"
order = 1886
uses = ["sk-def-sf-operations"]
lean = ["AlgebraicGeometry.Etale.sectionInvariant", "AlgebraicGeometry.Etale.dualizingComplex", "AlgebraicGeometry.Scheme.Hom.NormalConeData", "AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData"]
+++
*Remark (sketch).*

Finite coefficients $\Lambda=A=A_{E,n}=\mathcal O_E/\varpi^n$ for a finite
extension $E/\mathbf Q_\ell$ with uniformizer $\varpi$, with $\ell$ invertible on
every scheme in sight ($\ell\ne p$ in characteristic $p$); pro-étale sites,
$D^b_{ctf}(T,\Lambda)$ with twists $(-)(m)$, and the constructible exceptional
inverse image $Rf^{!}$ of [sk-def-sf-operations](vi), which exists for every
separated finite-type morphism (no admissibility hypothesis). For $Y$ separated finite type: $\Aaf^1_Y$, zero section
$s:Y\hookrightarrow\Aaf^1_Y$, open complement
$j:\mathbf G_{m,Y}\hookrightarrow\Aaf^1_Y$, global coordinate $t$; the
finite-level twist is $A(1)=\mu_{\ell^N}\otimes_{\Z/\ell^N}A$, where
$N\ge1$ is an integer with $\ell^NA=0$ (for $A=A_{E,n}$ one may take $N=n$,
as $\varpi^n$ divides $\ell^n$; the sheaf
$\mu_{\ell^N}\otimes_{\Z/\ell^N}A=\Z_\ell(1)\otimes_{\Z_\ell}A$ does not depend
on the choice, and when $e=e(E/\mathbf Q_\ell)$ divides $n$ the choice
$N=n/e$ makes $A=\mathcal O_E/\ell^N\cong(\Z/\ell^N)^{ef}$ free over
$\Z/\ell^N$, lem:pur-finite-kummer-level), and the
*Kummer class of $t$* is

$$
\kappa(t)\in H^1(\mathbf G_{m,Y},A(1)),
$$

the boundary of the $A$-coefficient Kummer sequence for $t$
(equivalently the class of the $\mu_{\ell^N}$-torsor
$\mathcal T_t=\Spec\mathcal O[T_0]/(T_0^{\ell^N}-t)$, tensored with $A$),
compatible with base change. For a closed immersion $i:Z\hookrightarrow X$ with ideal sheaf
$\mathcal I_Z$ the normal cone is
$N_{Z/X}=\Spec_Z\bigl(\bigoplus_{r\ge0}\mathcal I_Z^{\,r}/\mathcal I_Z^{\,r+1}\bigr)$;
when $i$ is regular of pure codimension $c$ the conormal sheaf
$\mathcal I_Z/\mathcal I_Z^2$ is locally free of rank $c$ and $N_{Z/X}\to Z$
is a vector bundle of rank $c$ with zero section $z$. For a smooth
$g:V\to B$ with a closed section $s:B\hookrightarrow V$, the *section
invariant* is

$$
\mathcal C(g,s)=Ls^{*}\omega_g=Ls^{*}Rg^{!}\Lambda_B ,
$$

and the deformation to the normal cone *of the section* is

$$
\mathcal D_sV=\operatorname{Bl}_{s(B)\times\{0\}}
\bigl(V\times_B\Aaf^1_B\bigr)\setminus\widetilde{V\times_B\{0\}},
$$

the blow-up minus the strict transform of the closed fibre. It carries
$\widetilde g:\mathcal D_sV\to\Aaf^1_B$ with a section
$\widetilde s:\Aaf^1_B\to\mathcal D_sV$, and the *family object* is
$\mathcal F=L\widetilde s^{*}\omega_{\widetilde g}$.
