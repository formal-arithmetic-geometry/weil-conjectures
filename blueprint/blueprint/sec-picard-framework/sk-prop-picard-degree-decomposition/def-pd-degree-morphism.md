+++
id = "def-pd-degree-morphism"
kind = "definition"
title = "The constant integers sheaf and the degree morphism"
order = 843
uses = ["def-pc-fppf-site", "def-pc-geometrically-irreducible", "def-pc-picard-functor", "def-pc-picard-presheaf", "def-pc-smooth-projective-curve", "def-pc-subfunctor", "def-pd-fibrewise-degree", "lem-pd-degree-locally-constant"]
+++
Let $k$ be a field. The *constant sheaf* $\underline{\Z}$ on the fppf
site $(\mathit{Sch}/k)_{fppf}$ of [def-pc-fppf-site] is the sheaf
associated with the constant presheaf $T\mapsto\Z$; its value on $T$ is the
group of locally constant functions $T\to\Z$.

Let now $C$ be a smooth projective
curve over $k$ which is
geometrically integral and let
$\operatorname{Pic}_{C/k}$ be the
Picard functor. The *degree morphism*

$$
\deg:\operatorname{Pic}_{C/k}\longrightarrow\underline{\Z}
$$

is the morphism of fppf sheaves defined as follows: for $T$ over $k$ and a
class in $\operatorname{Pic}_{C/k}(T)$ choose an fppf covering $\{T_i\to T\}$
and invertible $\mathcal{O}_{C_{T_i}}$-modules $\mathcal{L}_i$ representing the
pullbacks of the class along the
Picard presheaf; the locally constant
functions $t\mapsto\deg_{T_i}(\mathcal{L}_i)(t)$ of
[def-pd-fibrewise-degree] agree on the overlaps by
[lem-pd-degree-locally-constant](2–3) and glue to a locally constant
function $T\to\Z$, giving an element of $\underline{\Z}(T)$; the result is
independent of all choices by [lem-pd-degree-locally-constant].
The *degree-zero part* of the Picard functor is the subfunctor

$$
\operatorname{Pic}^0_{C/k}:=\ker(\deg)\subseteq\operatorname{Pic}_{C/k}
$$

in the sense of [def-pc-subfunctor]: its value on $T$ consists of the
classes whose fibrewise degree function is identically zero.
