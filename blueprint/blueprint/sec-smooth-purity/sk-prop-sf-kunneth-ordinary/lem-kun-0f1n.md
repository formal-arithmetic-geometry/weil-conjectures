+++
id = "lem-kun-0f1n"
kind = "lemma"
title = "Base change for pushforward tensored with an arbitrary complex"
order = 1779
uses = ["def-kun-derived-tensor", "def-kun-tor-amplitude", "def-kun-truncations", "def-kun-unbounded-exchange", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-kun-0f10", "lem-kun-0f11", "lem-kun-0f1j", "lem-kun-bounded-flat-replacement", "lem-kun-complex-colimit-hocolim", "lem-kun-derived-tensor-direct-sums", "lem-kun-flat-bounded-tor-amplitude", "lem-kun-functor-preserves-hocolim", "lem-kun-hocolim-truncations"]
+++
Let $K$ be a field and $n\ge1$ an integer invertible in $K$.
Consider a commutative diagram

$$
\begin{array}{ccccc}
X&\xleftarrow{\;p\;}&X'&\xleftarrow{\;h\;}&Y\\
\Big\downarrow{}&&\Big\downarrow{\scriptstyle f'}&&\Big\downarrow{\scriptstyle e}\\
\Spec(K)&\longleftarrow&S'&\xleftarrow{\;g\;}&T
\end{array}
$$

of schemes of finite type over $K$ with
$X'=X\times_{\Spec(K)}S'$ and $Y=X'\times_{S'}T$. The canonical
map

$$
p^{-1}E\kunotimes{\kunZn}(f')^{-1}Rg_*F
\longrightarrow
Rh_*\bigl(h^{-1}p^{-1}E\kunotimes{\kunZn}e^{-1}F\bigr)
$$

is an isomorphism for all $E\in D(X_{\Et},\kunZn)$ and
$F\in D(T_{\Et},\kunZn)$. (*Source:* Stacks Project, Tag
[0F1N](https://stacks.math.columbia.edu/tag/0F1N).)

## Proof

We reduce this to [lem-kun-0f1j] using that our functors
commute with direct sums. Recall that the derived tensor product
commutes with direct sums and that (derived) pullback commutes with
direct sums ([lem-kun-derived-tensor-direct-sums],
[def-kun-derived-tensor]); recall that $Rh_*$ and $Rg_*$
commute with direct sums: since $h$ and $g$ are quasi-compact
quasi-separated morphisms of finite type schemes over $K$,
[lem-kun-0f10](1) gives
$\kuncd(h),\kuncd(g)<\infty$, and then
[lem-kun-0f11](1) applies.

To finish the proof we argue as follows. First we write
$E=\operatorname{hocolim}_N\tau_{\le N}E$
([lem-kun-hocolim-truncations]). Since our functors commute
with direct sums, they commute with homotopy colimits
([lem-kun-functor-preserves-hocolim]). Hence it suffices to
prove the lemma for $E$ bounded above. Similarly for $F$ we may
assume $F$ is bounded above.

Choose a bounded-above complex representing $E$ and, using
[lem-kun-bounded-flat-replacement], replace it by a
bounded-above complex $\mathcal E^\bullet$ of flat sheaves of
$\kunZn$-modules. Then
$\mathcal E^\bullet=\varinjlim_N\sigma_{\ge-N}\mathcal E^\bullet$
(stupid truncations, [def-kun-truncations]); the filtered
colimit of complexes is a homotopy colimit
([lem-kun-complex-colimit-hocolim]), and our functors commute
with homotopy colimits, so we may assume
$\mathcal E^\bullet$ is a bounded complex of flat sheaves. In
particular it belongs to $\Dplus(X_{\Et},\kunZn)$ and has tor
amplitude in $[a,\infty)$, where $a$ is its lowest nonzero degree
([lem-kun-flat-bounded-tor-amplitude] and
[def-kun-tor-amplitude]).

For $F$, choose merely a bounded-above complex
$\mathcal F^\bullet$ representing it ([def-weil-pbc-derived-categories]);
no flatness hypothesis on $F$ is needed. Writing
$\mathcal F^\bullet=\varinjlim_N\sigma_{\ge-N}\mathcal F^\bullet$
and using [def-kun-truncations] and
[lem-kun-complex-colimit-hocolim] in the same way reduces to a
bounded complex, hence to an object of
$\Dplus(T_{\Et},\kunZn)$. We have therefore reached exactly the
hypotheses of [lem-kun-0f1j], which proves the canonical map
is an isomorphism.
