+++
id = "def-weil-scheme-morphism-properties"
kind = "definition"
title = "Scheme and morphism properties"
order = 410
uses = ["def-weil-finite-type-morphism"]
+++
Let $f:X\to Y$ be a morphism. Write $|Y|$ for the set of closed points of
$Y$, and, for $y\in|Y|$, write $\kappa(y)$ for its residue field. The phrase
of finite type [def-weil-finite-type-morphism] has the preceding meaning. It
is *of finite presentation* if every affine open $V\subseteq Y$ has a finite
affine cover of $f^{-1}(V)$ by $\operatorname{Spec}B$ with $B$ a finitely
presented algebra over the coordinate ring of $V$. A ring is *regular* if
each localization at a prime has Krull dimension equal to the minimal number
of generators of its maximal ideal; a scheme is regular if all its local
rings are regular. The morphism $f$ is *flat* if every induced local-ring map
is flat, and *smooth* if it is locally of finite presentation and flat with
regular geometric fibers. It is a *closed immersion* if it is affine and is
induced locally by a surjective ring homomorphism. It is *separated* if its
diagonal $X\to X\times_YX$ is a closed immersion, and *universally closed* if
every base change of $f$ is a closed map. It is *proper* if it is separated,
of finite type, and universally closed. An *open immersion* identifies its
source with an open subscheme of its target. For $y\in|Y|$, the geometric
fiber is

$$
 X_{\bar y}=X\times_Y\operatorname{Spec}\overline{\kappa(y)},
$$

where $\overline{\kappa(y)}$ is a chosen algebraic closure of $\kappa(y)$. A
*geometric point* of $Y$ is a morphism $\bar y:\operatorname{Spec}\Omega\to
Y$ whose field $\Omega$ is algebraically closed and contains the residue
field of the image point. A scheme of finite type over a field is one whose
structure morphism is of finite type. A morphism is *weakly etale* if it is
flat and its diagonal is flat. A subset of a scheme is *locally closed* if it
is the intersection of an open and a closed subset, and it is *constructible*
if it is a finite union of locally closed subsets. A locally closed
constructible subscheme means a subscheme whose underlying subset is locally
closed and constructible. A sheaf on a locally closed subscheme is locally
constant if it becomes a constant sheaf after pulling back along a covering
family in its pro-etale site; its stalk at a geometric point is the filtered
colimit of its sections over pointed neighborhoods.
