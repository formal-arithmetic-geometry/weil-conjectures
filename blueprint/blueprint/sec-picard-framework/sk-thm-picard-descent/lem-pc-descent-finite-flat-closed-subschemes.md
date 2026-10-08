+++
id = "lem-pc-descent-finite-flat-closed-subschemes"
kind = "lemma"
title = "Effective descent of finite flat closed subschemes"
order = 764
uses = ["def-pc-finite-locally-free", "lem-pc-fpqc-descent"]
lean = ["AlgebraicGeometry.isSheaf_fpqc_finiteLocallyFreeSubscheme"]
+++
(Descent, Lemma 35.37.2, Tag
[03I0](https://stacks.math.columbia.edu/tag/03I0), together with the
fpqc-local nature of finite locally free morphisms.) Let $X\to S$ be a
morphism of schemes, $T$ an $S$-scheme, $\{g_i:T_i\to T\}_{i\in I}$ an
fpqc covering of $S$-schemes, and $d\geq0$; write
$X_T:=X\times_ST$, $X_{T_i}:=X\times_ST_i$ and $T_{ii'}:=T_i\times_TT_{i'}$.
Let $Z_i\subseteq X_{T_i}$ be closed subschemes such that each
$Z_i\to T_i$ is finite locally free of degree $d$
([def-pc-finite-locally-free]), and such that for all $i,i'$ the two
pullbacks $Z_i\times_{T_i}T_{ii'}$ and $Z_{i'}\times_{T_{i'}}T_{ii'}$ are
the same closed subscheme of $X_{T_{ii'}}$ (the cartesian identifications;
as a closed subscheme has no nontrivial automorphisms over the ambient
scheme, the cocycle condition is then automatic). Then there is a
unique closed subscheme $Z\subseteq X_T$ with $Z\times_TT_i=Z_i$ as closed
subschemes of $X_{T_i}$ for every $i$, and $Z\to T$ is finite locally
free of degree $d$.

## Proof

*The covering of $X_T$.* The family
$\{h_i:X_{T_i}=X_T\times_TT_i\to X_T\}_{i\in I}$ is the base change of
the fpqc covering $\{T_i\to T\}$, hence an fpqc covering (Topologies,
Lemma 34.9.8, Tag [022D](https://stacks.math.columbia.edu/tag/022D)),
and $X_{T_i}\times_{X_T}X_{T_{i'}}=X_{T_{ii'}}$; write
$p_1,p_2$ for the two projections of $X_{T_{ii'}}$ to $X_{T_i}$ and
$X_{T_{i'}}$.

*Descending the quotients.* Let $\mathcal{I}_i\subseteq\mathcal{O}_{X_{T_i}}$
be the quasi-coherent ideal of $Z_i$ and
$\mathcal{Q}_i:=\mathcal{O}_{X_{T_i}}/\mathcal{I}_i=\mathcal{O}_{Z_i}$. The
projections $p_1,p_2$ are flat (base changes of the flat $T_i\to T$), so
$p_1^*\mathcal{I}_i\to p_1^*\mathcal{O}_{X_{T_i}}=\mathcal{O}_{X_{T_{ii'}}}$
is injective, with image the ideal of the closed subscheme
$p_1^{-1}(Z_i)=Z_i\times_{T_i}T_{ii'}$; similarly for $p_2$. The hypothesis
$p_1^{-1}(Z_i)=p_2^{-1}(Z_{i'})$ says that these two ideals of
$\mathcal{O}_{X_{T_{ii'}}}$ coincide; hence the identity of
$\mathcal{O}_{X_{T_{ii'}}}$ (the canonical descent datum of
$\mathcal{O}_{X_T}$) induces isomorphisms
$\varphi_{ii'}:p_1^*\mathcal{Q}_i\to p_2^*\mathcal{Q}_{i'}$, which satisfy
the cocycle condition on the triple products because they are induced
by identities. Thus $(\mathcal{Q}_i,\varphi_{ii'})$ is a descent datum
of quasi-coherent modules for the covering $\{h_i\}$, and the
surjections $\mathcal{O}_{X_{T_i}}\to\mathcal{Q}_i$ form a morphism of
descent data from $(h_i^*\mathcal{O}_{X_T},\mathrm{can})$. By
part (1) of [lem-pc-fpqc-descent] there are a quasi-coherent
$\mathcal{O}_{X_T}$-module $\mathcal{Q}$ with
$(h_i^*\mathcal{Q},\mathrm{can})\cong(\mathcal{Q}_i,\varphi_{ii'})$ and a
morphism $q:\mathcal{O}_{X_T}\to\mathcal{Q}$ whose pullbacks $h_i^*q$ are
the given surjections. Since $h_i^*$ is exact ($h_i$ is flat),
$h_i^*\operatorname{Coker}(q)=\operatorname{Coker}(h_i^*q)=0$ for all $i$, so
the descent datum of $\operatorname{Coker}(q)$ is isomorphic to that of
$0$ and $\operatorname{Coker}(q)=0$ by part (1) of [lem-pc-fpqc-descent]: $q$ is
surjective. Let $\mathcal{I}:=\operatorname{Ker}(q)$, a quasi-coherent ideal, and
$Z:=V(\mathcal{I})\subseteq X_T$. By exactness of $h_i^*$ again,
$h_i^*\mathcal{I}=\operatorname{Ker}(h_i^*q)=\mathcal{I}_i$ inside
$\mathcal{O}_{X_{T_i}}$, i.e. $Z\times_{X_T}X_{T_i}=Z\times_TT_i=Z_i$.

*Uniqueness.* If $Z'\subseteq X_T$ is another closed subscheme with
$Z'\times_TT_i=Z_i$ for all $i$, then its quotient
$\mathcal{O}_{X_T}\to\mathcal{O}_{Z'}$ pulls back to the same morphism of
descent data $\mathcal{O}_{X_{T_i}}\to\mathcal{Q}_i$; by the full
faithfulness in part (1) of [lem-pc-fpqc-descent] there is an isomorphism
$\mathcal{O}_{Z'}\cong\mathcal{Q}$ under $\mathcal{O}_{X_T}$, so the two
kernels agree and $Z'=Z$.

*A reformulation.* An affine morphism $\pi:Z\to T$ is finite locally
free of degree $d$ ([def-pc-finite-locally-free]) if and only if
$\pi_*\mathcal{O}_Z$ is a finite locally free $\mathcal{O}_T$-module of
rank $d$. The question is local on $T$, so let $T=\operatorname{Spec}(A)$
and $Z=\operatorname{Spec}(C)$. A finite $A$-algebra $C$ is of finite
presentation as an $A$-algebra if and only if it is of finite
presentation as an $A$-module (EGA IV$_1$, (1.4.7)). The morphism $\pi$ is
flat if and only if $C$ is a flat $A$-module, since flatness of a module
can be checked after localising at the primes of $C$. A finitely presented
flat module is finite locally free (Algebra, Lemma 10.78.2). Finally, for
$s\in T$ the fibre is $Z_s=\operatorname{Spec}(C\otimes_A\kappa(s))$, so
$\dim_{\kappa(s)}\Gamma(Z_s,\mathcal{O}_{Z_s})$ is the rank of $C$ at $s$,
and $Z_s$ is finite when this rank is finite. Together these give both
directions.

*$Z\to T$ is finite locally free of degree $d$.* Let $\pi:Z\to T$ and
$\pi_i:Z_i\to T_i$ be the structure morphisms; $\pi_i$ is the base change
of $\pi$ along $g_i$. Each $\pi_i$ is finite, in particular affine, and
being affine is a property of morphisms that is fpqc local on the base
(Descent, Section 35.23; EGA IV$_2$, (2.7.1)); hence $\pi$ is affine and
$Z=\underline{\operatorname{Spec}}_T(\pi_*\mathcal{O}_Z)$ with
$\pi_*\mathcal{O}_Z$ quasi-coherent. For an affine morphism the
formation of $\pi_*\mathcal{O}_Z$ commutes with arbitrary base change
(over affine opens $\operatorname{Spec}(A)\subseteq T$ and
$\operatorname{Spec}(A')\subseteq T_i$ above it, with
$\pi^{-1}\operatorname{Spec}(A)=\operatorname{Spec}(C)$, the base change is
$\operatorname{Spec}(A'\otimes_AC)$ and $A'\otimes_AC$ is the base changed
module), so $g_i^*\pi_*\mathcal{O}_Z\cong\pi_{i*}\mathcal{O}_{Z_i}$, which is
finite locally free of rank $d$ by the hypothesis and the reformulation. By
part (2) of [lem-pc-fpqc-descent] the quasi-coherent $\mathcal{O}_T$-module
$\pi_*\mathcal{O}_Z$ is finite locally free of rank $d$; thus $\pi$ is
affine with $\pi_*\mathcal{O}_Z$ finite locally free of rank $d$, so by the
reformulation $\pi$ is finite locally free of degree $d$.
