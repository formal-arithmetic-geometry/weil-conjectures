+++
id = "lem-sc-cech-spectral"
kind = "lemma"
title = "The Cech-to-cohomology spectral sequence"
order = 600
uses = ["thm-sp-double-complex-spectral-sequences"]
lean = ["CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence"]
+++
Let $X$ be a scheme, $\mathfrak U=\{U_i\to X\}$ an etale covering
(or any covering of a site; we apply the statement below also to the
Zariski site), and $F$ an abelian sheaf on $X_{\Et}$. There is
a convergent spectral sequence

$$
E_2^{pq}=\check H^p(\mathfrak U,\underline H^q(F))
\Longrightarrow H^{p+q}(X_{\Et},F),
$$

where $\underline H^q(F)$ is the presheaf
$V\mapsto H^q(V_{\Et},F)$ and $\check H^p(\mathfrak U,-)$ is
Cech cohomology with respect to the covering $\mathfrak U$.

## Proof

Choose an injective resolution $F\to I^{\bullet}$ and consider the
double complex $C^{pq}:=C^p(\mathfrak U,I^q)$, where
$C^p(\mathfrak U,-)$ is the (alternating) Cech complex of the
covering $\mathfrak U$. Its cohomology in the first direction is
$C^p(\mathfrak U,\underline H^q(F))$, because taking cohomology
commutes with the finite direct products defining the Cech complex;
so the first spectral sequence of the double complex
[thm-sp-double-complex-spectral-sequences] has

$$
E_1^{pq}=C^p(\mathfrak U,\underline H^q(F)),\qquad
E_2^{pq}=\check H^p(\mathfrak U,\underline H^q(F)).
$$

The total complex of $C^{\bullet\bullet}$ computes
$H^{p+q}(X_{\Et},F)$: for each $q$, the complex
$C^{\bullet}(\mathfrak U,I^q)$ is the Cech resolution of the
injective sheaf $I^q$, and an injective sheaf is acyclic for Cech
cohomology with respect to every covering (the Cech complex of a
covering applied to an injective sheaf computes its cohomology,
which vanishes in positive degrees by injectivity), so the natural
map from the complex $F\to I^{\bullet}$ to the total complex is a
quasi-isomorphism, and the total cohomology is the hypercohomology
$H^{p+q}(X_{\Et},F)$. This is the first spectral sequence of
a double complex, which converges to the cohomology of the total
complex by [thm-sp-double-complex-spectral-sequences] (*reference: Stacks Project, Homological
Algebra: spectral sequences of double complexes*).
