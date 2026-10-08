+++
id = "thm-pur-with-support-exactness"
kind = "theorem"
title = "Long exact sequence for cohomology with support"
order = 1926
uses = ["def-pur-support-cohomology", "def-weil-open-closed-recollement", "def-weil-pbc-derived-categories", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-scheme-conventions", "thm-weil-pbc-site-comparison"]
+++
Let $X$ be a scheme, let
$i:Z\hookrightarrow X$ be a closed subscheme with open complement
$j:U\hookrightarrow X$, and let $F$ be a
torsion etale sheaf on the
small etale site of $X$. In the
notation of [def-pur-support-cohomology], there is a long exact
sequence

$$
\cdots\longrightarrow H^q_Z(X,F)\longrightarrow H^q(X,F)
\longrightarrow H^q(U,F)\longrightarrow H^{q+1}_Z(X,F)\longrightarrow\cdots,
$$

functorial in the pair $(X,X\setminus Z)$ and in $F$. The same
statement holds for bounded-below complexes with torsion cohomology in the
derived category of [def-weil-pbc-derived-categories], and on the
pro-etale site of $X$ for finite-torsion coefficients, by the comparison
[thm-weil-pbc-site-comparison]. (Source: Milne, Lectures on Etale
Cohomology, Section 9, Theorem 9.3 and the exactness axiom of the etale site.)

## Proof

Step 1: the derived support object. For a bounded-below complex $F$ (a torsion sheaf placed in degree zero) and
$I^{\bullet}$ a K-injective resolution, the complex of sections with
support in $Z$ is the kernel of the restriction
$\Gamma(X,I^{\bullet})\to\Gamma(U,I^{\bullet})$, which is exact, and the
kernel is the complex computing $R\Gamma_Z(X,\cdot)$ by
[def-pur-support-cohomology]. Step 2: the exactness axiom. For a
torsion sheaf $F$ the sequence of presheaves
$0\to\Gamma_Z(V,F)\to\Gamma(V,F)\to\Gamma(V\cap U,F)\to0$ is exact for
every open $V$ of the finite-type scheme $X$: a section $f$ of
$F$ on $V\cap U$ need not extend, but for the sheaf $F$ the exact
sequence $0\to j_!j^*F\to F\to i_*i^*F\to0$ is exact (the open and
closed counterpart of the recollement, the standard exactness of
support and restriction on the (pro-)etale site,
[def-weil-open-closed-recollement]) and its global-sections
sequence is the sequence of the statement. Step 3: the long exact
sequence. The short exact sequence of complexes

$$
0\longrightarrow\Gamma_Z(X,I^{\bullet})
\longrightarrow\Gamma(X,I^{\bullet})
\longrightarrow\Gamma(U,I^{\bullet})\longrightarrow0
$$

(the exactness at the last arrow holding because $I^{\bullet}$ is
K-injective, hence flabby on the (pro-)etale site: the restriction map
of a flabby resolution is surjective, by Step 2 applied to an
injective resolution and the flabbiness of injective sheaves on a
site) gives, by the zig-zag/snake lemma applied to the exact sequence
of cochain complexes, the long exact sequence of cohomology

$$
\cdots\to H^q_Z(X,F)\to H^q(X,F)\to H^q(U,F)\to H^{q+1}_Z(X,F)\to\cdots,
$$

with the connecting morphism the one of the K-injective
resolution; the functoriality in the pair and in $F$ is the
functoriality of all the maps. Step 4: complexes and the pro-etale
site. For bounded-below complexes with torsion cohomology the same
argument runs with a K-injective resolution (the exactness of the
level (2) sequence for each term and the five-lemma over the
spectral sequence of the double complex), and the finite-torsion case
on the pro-etale site is the transport of the etale statement along
the site comparison [thm-weil-pbc-site-comparison] of the proper-base-change chapter (the sheaves being finite-torsion, the site comparison preserves
the support and the exactness).
