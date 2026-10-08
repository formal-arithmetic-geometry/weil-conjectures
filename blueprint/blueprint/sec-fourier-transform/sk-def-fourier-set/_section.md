+++
id = "sk-def-fourier-set"
kind = "section"
title = "The coefficient setting: six operations only"
order = 2669
lean = ["AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible"]
+++
*Remark (sketch).*

Fix a prime $p$, a power $q=p^a$, the fields $k_0=\Fq$ and $k=\bar k_0$, a
prime $\ell\ne p$, and a finite extension $E/\Ql$ with algebraic closure
$\Qlb$. All schemes are separated of finite type over $k_0$. We use:
the bounded constructible derived category $D^b_c(-,E)$ — the adic
category, $\Dbc$ of the pro-étale $E$-sheaves in the sense of
[sk-thm-sf-package] (2) (derived-complete $\mathcal O_E$-complexes of
étale origin, rationalized), *not* the derived category of discrete
sheaves of $E$-modules on the small étale site, on which the base-change
isomorphisms fail — with the six operations $Lf^*,Rf_*,Rf_!,Rf^!,\otimes^L, R\mathcal H om$ in the form of the six-functor package, the
compact-support direct image $Rf_!=Rf_*\circ j_!$ read through a
compactification, ordinary and compact-support cohomology, and the Tate
twists. The additive character $\psi$ of [sk-def-char] takes values in
$\mu_p\subset\Qlb^\times$, so the Artin–Schreier sheaf of [sk-def-as] and
the Fourier kernel $\mathcal K_\psi$ of [sk-def-kernel] are a priori
$\Qlb$-sheaves; we assume throughout that $\mu_p\subset E$, so that $\psi$
is $E$-valued, $\mathcal K_\psi$ is a lisse $E$-sheaf of rank one, and the
tensor product $\otimes^L_E$ in [sk-def-ft] makes sense on $\Dbc(V,E)$.
(Without this assumption the transform is defined at the $\Qlb$-stage, or
over $E(\mu_p)$ after extension of scalars.) No weight, no $L^2$-weight
parameter and no purity notion is used
anywhere in this file; the Tate twist is a coefficient normalization (the
blueprint records its definition among the weight foundations, but no weight
statement of that chapter is used below). (Blueprint def:weil-pbc-qbar-category,
prop:functor-package, def:weil-ordinary-compact-cohomology,
def:wf-tate-twist.)
