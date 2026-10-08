+++
id = "lemma-weil-pbc-constructible-finite-pushforward"
kind = "lemma"
title = "Constructible sheaves reduce to finite pushforwards"
order = 1132
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-constructible-finite-pushforward-approximation", "lemma-weil-pbc-constructible-approximation"]
+++
If $U$ is quasi-compact and quasi-separated, every constructible torsion
sheaf $C$ admits a monomorphism

$$
C\longrightarrow\bigoplus_{i=1}^r(h_i)_*\underline{M_i},
$$

where each $h_i:V_i\to U$ is finite and finitely presented and each $M_i$ is
a finite abelian group.

## Proof

Write $U=\varprojlim U_\lambda$ with affine transition maps and noetherian,
quasi-compact, quasi-separated $U_\lambda$. The finite stratification of
$C$, its finite stalk groups, all restriction maps, and their equalizer
relations descend to one stage $U_\lambda$. We prove the assertion there by
noetherian induction on a closed complement of a dense stratum. Choose a
dense open $j:V\hookrightarrow U_\lambda$ where $C_\lambda$ is finite
locally constant and a finite etale cover $e:W\to V$ trivializing it. Take
the integral closure of $U_\lambda$ in $e_*\mathcal O_W$ and discard
components disjoint from $V$; this gives a finite map $h:W'\to U_\lambda$
extending $e$. The adjunction unit is a monomorphism on $V$,

$$
C_\lambda|_V\hookrightarrow e_*\underline M
=(h_*\underline M)|_V,
$$

for a finite group $M$.

Let $Z=U_\lambda\setminus V$ with its reduced closed structure. By
induction, $C_\lambda|_Z$ embeds into a finite sum
$\bigoplus_b(h_b)_*\underline{M_b}$ with $h_b$ finite over $Z$; composing
with $Z\hookrightarrow U_\lambda$ keeps the maps finite. Map
$C_\lambda$ to

$$
h_*\underline M\oplus\bigoplus_b(h_b)_*\underline{M_b}
$$

by the dense-open unit in the first component and restriction to $Z$ in the
remaining components. At a geometric point of $V$ the first component is
injective, and at a geometric point of $Z$ the second block is injective, so
the combined map is monic. This is the localization induction, including
the boundary and overlap comparison. Pull the finite diagram and monomorphism
back to $U$. Etale inverse image is exact, and finite direct image commutes
with this pullback by the finite geometric-stalk product formula. This gives
the displayed monomorphism and expands Tag `09Z7`.

## Detailed form

If $U$ is quasi-compact and quasi-separated and $C$ is constructible torsion
on $U_{\Et}$, there is a monomorphism

$$
 C\hookrightarrow\bigoplus_{i=1}^m(h_i)_*\underline{M_i},
$$

where every $h_i:V_i\to U$ is finite and finitely presented and every $M_i$ is
a finite abelian group.

## Proof

Apply [lem-weil-pbc-constructible-finite-pushforward-approximation] to $U$ and
$C$. The finite maps obtained there are finite over the Noetherian
approximation and therefore of finite presentation; their pullbacks remain
finite and finitely presented. Exactness of inverse image and
finite-base-change compatibility of direct image preserve the monomorphism,
giving the displayed map on $U$. This is precisely the descent argument in
Stacks Project, Lemma 59.74.4 (Tag
[09Z7](https://stacks.math.columbia.edu/tag/09Z7)); no composition with a
locally closed stratum is used.
