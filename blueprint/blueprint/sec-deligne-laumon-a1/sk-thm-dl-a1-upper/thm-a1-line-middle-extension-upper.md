+++
id = "thm-a1-line-middle-extension-upper"
kind = "theorem"
title = "Deligne–Laumon affine-line estimate for the middle extension"
order = 2806
uses = ["cor-a1-fourier-middle-hc1", "def-weil-frobenius-module-weights", "def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "def-wf-constant-weil-twist", "def-wf-fundamental-representation", "def-wf-middle-extension", "lem-a1-constituent-nonexceptional-comparison", "lem-a1-exceptional-constituents", "lem-a1-extension-bounds", "lem-a1-geometric-constituent-reduction", "lem-a1-middle-extension-endpoints", "lem-a1-spectrum-exact-sequence", "lem-a1-subquotient-extension-bounds", "lem-a1-unramified-nonexceptional", "lem-a1-weight-bound-constant-extension", "p-dl-a1-exact", "prop-a1-curve-boundary-sequence", "rem-dl-a1-conventions"]
lean = ["AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMost_compactlySupportedCohomology_directImage", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.subsingleton_compactlySupportedCohomology_directImage_zero", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isPureOfWeightOver_compactlySupportedCohomology_directImage_two"]
+++
In the conventions of [rem-dl-a1-conventions], let
$j:U_0\hookrightarrow A_0=\mathbf A^1_{k_0}$ be a dense open immersion
and let $\mathcal F$ be a lisse Weil sheaf on $U_0$, punctually
$\iota$-pure of weight $w$ ([def-weil-punctual-weights]) and
unramified at infinity. Then, for the ordinary middle extension
$j_*\mathcal F$ of [def-wf-middle-extension] and the compactly
supported cohomology of [def-weil-ordinary-compact-cohomology], for
every integer $r$

$$
H_c^r(A,j_*\mathcal F)\quad\text{has weights at most }w+r
$$

in the sense of [def-weil-frobenius-module-weights]. More precisely,
$H_c^0(A,j_*\mathcal F)=0$, $H_c^2(A,j_*\mathcal F)$ is $\iota$-pure of
weight $w+2$ (possibly zero), $H_c^r(A,j_*\mathcal F)=0$ for
$r\notin\{0,1,2\}$, and $H_c^1(A,j_*\mathcal F)$ has weights at most
$w+1$.

## Proof

*Degrees other than one.* $A_0$ is a smooth geometrically connected
affine curve, so [lem-a1-middle-extension-endpoints] applied to $j$
gives $H_c^0(A,j_*\mathcal F)=0$, the vanishing outside degrees
$0,1,2$, and the purity of weight $w+2$ of $H_c^2(A,j_*\mathcal F)$.
These are the assertions in all degrees $r\neq1$.

*Step 1: a finite constant extension is harmless.* Let
$k'_0=\mathbf F_{q^m}$ and replace $U_0\subset A_0$ and $\mathcal F$
by their base changes to $k'_0$. The geometric objects $U\subset A$,
the geometric generic stalk with its geometric monodromy, the sheaf
$j_*\mathcal F$ on $A$ and the group $H_c^1(A,j_*\mathcal F)$ do not
change; only the Weil structure is replaced by its $m$-th power, so
the Frobenius on $H_c^1$ becomes $F^m$. The base-changed sheaf is still
lisse, punctually $\iota$-pure of weight $w$ (a closed point over $x$
of degree $e$ over $\kappa(x)$ has local Frobenius $F_x^e$ and norm
$q_x^e$) and unramified at infinity (the inertia at $\infty$ is a
subgroup of the unchanged geometric fundamental group). By
[lem-a1-weight-bound-constant-extension] with $b=w+1$, a bound $w+1$
for $H_c^1(A,j_*\mathcal F)$ over $k'_0$ implies the bound over
$k_0$. We may therefore pass to finite constant extensions freely.

*Step 2: a composition filtration.* By
[lem-a1-geometric-constituent-reduction], after a finite constant
extension $\mathcal F$ has a finite filtration by lisse Weil subsheaves

$$
0=\mathcal F^0\subset\mathcal F^1\subset\cdots\subset\mathcal F^n=\mathcal F
$$

whose graded pieces $\mathcal M_i=\mathcal F^i/\mathcal F^{i-1}$, after
discarding repeated terms, are nonzero, geometrically irreducible and
punctually $\iota$-pure of weight $w$. Each $\mathcal F^i$ is
punctually $\iota$-pure of weight $w$ as well: at a closed point $x$
the stalk $\mathcal F^i_{\bar x}$ is an $F_x$-stable subspace of
$\mathcal F_{\bar x}$, so its eigenvalues are among those of
$\mathcal F_{\bar x}$ by [lem-a1-spectrum-exact-sequence]. Each
$\mathcal M_i$ is unramified at infinity: the inertia group at
$\infty$ acts trivially on $\mathcal F_{\bar\eta}$, hence on its
subquotient $(\mathcal M_i)_{\bar\eta}$
([def-wf-fundamental-representation]).

*Step 3: exactness of the middle extension along the filtration.* For
each $i$ the sequence $0\to\mathcal F^{i-1}\to\mathcal F^i\to
\mathcal M_i\to0$ consists of lisse Weil sheaves on $U_0$ that are all
punctually $\iota$-pure of weight $w$. By [p-dl-a1-exact] (with
$C_0=A_0$),

$$
0\longrightarrow j_*\mathcal F^{i-1}\longrightarrow j_*\mathcal F^i
\longrightarrow j_*\mathcal M_i\longrightarrow0
$$

is an exact sequence of Weil sheaves on $A_0$. Its long exact
sequence of compactly supported cohomology, which is
Frobenius-equivariant because it comes from a triangle of Weil
complexes, contains the exact segment

$$
H_c^1(A,j_*\mathcal F^{i-1})\longrightarrow H_c^1(A,j_*\mathcal F^{i})
\longrightarrow H_c^1(A,j_*\mathcal M_i).
$$

Hence $H_c^1(A,j_*\mathcal F^i)$ is an extension of a
Frobenius-stable subobject of $H_c^1(A,j_*\mathcal M_i)$ by a
Frobenius-stable quotient of $H_c^1(A,j_*\mathcal F^{i-1})$. By
[lem-a1-subquotient-extension-bounds] and [lem-a1-extension-bounds],
induction on $i$ (starting from $H_c^1(A,j_*\mathcal F^0)=0$) shows
that the bound $w+1$ for $H_c^1(A,j_*\mathcal F)$ follows from the
same bound for every $H_c^1(A,j_*\mathcal M_i)$. No splitting of the
filtration is used.

*Step 4: one factor.* Let $\mathcal M=\mathcal M_i$; it is a nonzero
lisse Weil sheaf on $U_0$, geometrically irreducible, punctually
$\iota$-pure of weight $w$ and unramified at infinity. A
geometrically irreducible sheaf is irreducible as a Weil sheaf, since a
Weil-stable subspace of $\mathcal M_{\bar\eta}$ is stable under the
geometric fundamental group.

(a) *$\mathcal M$ geometrically constant.* The geometric fundamental
representation is then trivial and irreducible, so $\mathcal M$ has
rank one and is a constant Weil twist in the sense of
[def-wf-constant-weil-twist]. By [lem-a1-exceptional-constituents]
(the case without Artin–Schreier factor), $H_c^1(U,\mathcal M)$ has
weights at most $w+1$. The boundary sequence
[prop-a1-curve-boundary-sequence] for $j$ gives a
Frobenius-equivariant surjection
$H_c^1(U,\mathcal M)\twoheadrightarrow H_c^1(A,j_*\mathcal M)$, so
$H_c^1(A,j_*\mathcal M)$ has weights at most $w+1$ by
[lem-a1-subquotient-extension-bounds]. (In fact $j_*\mathcal M$ is the
lisse constant twist on $A_0$ and $H_c^1(A,j_*\mathcal M)=0$, as in
Step 1 of the proof of [lem-a1-exceptional-constituents]; only the
bound is needed.)

(b) *$\mathcal M$ not geometrically constant.* Since $\mathcal M$ is
irreducible, unramified at infinity and not geometrically constant,
it is constituent-nonexceptional by
[lem-a1-unramified-nonexceptional]; by part (1) of
[lem-a1-constituent-nonexceptional-comparison] its middle extension
$j_*\mathcal M$ is Fourier-nonexceptional. Thus $\mathcal M$ is an
irreducible lisse Weil sheaf on $U_0$, unramified at infinity,
punctually $\iota$-pure of weight $w$, with irreducible geometric
fundamental representation and Fourier-nonexceptional middle
extension, and [cor-a1-fourier-middle-hc1] shows that
$H_c^1(A,j_*\mathcal M)$ has weights at most $w+1$.

*Conclusion.* By Step 4 every factor satisfies the bound $w+1$; by
Step 3 so does $H_c^1(A,j_*\mathcal F)$ over the extended field, and
by Step 1 over $k_0$. Together with the degrees other than one this
proves the theorem.
