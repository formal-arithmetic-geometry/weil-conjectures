+++
id = "lem-pd-degree-locally-constant"
kind = "lemma"
title = "The fibrewise degree is a locally constant function, and is a base-change invariant"
order = 842
uses = ["def-pc-base-change", "def-pc-degree-line-bundle", "def-pc-euler-characteristic", "def-pd-fibrewise-degree", "def-sc-invertible-module", "def-pc-perfect-complex", "lem-pc-degree-base-change", "lem-pc-euler-additive", "lem-pc-flat-complex-derived-pullback", "lem-pc-rf-perfect-base-change", "thm-pc-semicontinuity-base-change"]
+++
In the situation of [def-pd-fibrewise-degree]:

1. the function $t\mapsto\deg_T(\mathcal{L})(t)$ is locally constant on $T$;
1. for every invertible
$\mathcal{O}_T$-module $\mathcal{N}$ one has
$\deg_T(\mathcal{L}\otimes_{\mathcal{O}_{C_T}}f_T^*\mathcal{N}) =\deg_T(\mathcal{L})$, where $f_T:C_T\to T$ is the structure morphism;
1. for every morphism $g:T'\to T$ of $k$-schemes one has
$\deg_{T'}\bigl(g_{C}^*\mathcal{L}\bigr)=\deg_T(\mathcal{L})\circ g$,
where $g_C:C_{T'}\to C_T$ is the
base change of $g$.

## Proof

We work throughout in the situation of [def-pd-fibrewise-degree], so
that the degree is the [def-pc-degree-line-bundle] and $\chi$ is the
[def-pc-euler-characteristic] of the fibre, and fibre products are those
of [def-pc-base-change].

*(1) Local constancy.* Let $f_T:C_T\to T$ be the structure morphism. It
is the base change of the projective morphism $C\to\Spec(k)$, hence
proper, flat and of finite presentation; $\mathcal{L}$ is invertible,
hence of finite presentation and (as $C_T$ is flat over $T$) flat over
$T$. We use the local model from the proof of
[thm-pc-semicontinuity-base-change]. By [lem-pc-rf-perfect-base-change]
the object $E=Rf_{T,*}\mathcal{L}$ is perfect and its formation commutes
with arbitrary base change. Fix $t\in T$. By [def-pc-perfect-complex],
after shrinking to an affine open $U=\Spec(A)\ni t$ (and making the
finitely many projective terms free on a principal open), $E|_U$ is
represented by a bounded complex $K$ with $K^i\cong A^{n_i}$. For
$s\in U$ the terms of $K$ are flat, so by
[lem-pc-flat-complex-derived-pullback] the derived pullback of $E$ along
$\Spec\kappa(s)\to T$ is $K\otimes_A\kappa(s)$, and by the base-change
isomorphism it computes $H^*(C_{\kappa(s)},\mathcal{L}_s)$. Therefore

$$
\chi\bigl(C_{\kappa(s)},\mathcal{L}_s\bigr)
=\sum_i(-1)^i\dim_{\kappa(s)}H^i(K\otimes_A\kappa(s))
=\sum_i(-1)^i\dim_{\kappa(s)}\bigl(K^i\otimes_A\kappa(s)\bigr)
=\sum_i(-1)^in_i ,
$$

the middle equality being the Euler characteristic of a bounded complex
of finite dimensional vector spaces. So $s\mapsto\chi(C_{\kappa(s)},\mathcal{L}_s)$
is constant on $U$, hence locally constant on $T$. The same argument for
$\mathcal{O}_{C_T}$ shows that
$s\mapsto\chi(C_{\kappa(s)},\mathcal{O}_{C_{\kappa(s)}})$ is locally
constant. Subtracting gives (1).

*(2) Twisting by a pullback.* By [lem-pc-degree-base-change](1)
the fibrewise degree is unchanged by extension of the base field, so it
suffices to compute at a point $t$ after base change to $\kappa(t)$. Over the
field $\kappa(t)$ the projection formula in the form of
[lem-pc-degree-base-change](2) gives
$\chi\bigl(C_t,\mathcal{L}_t\otimes f_t^*\mathcal{N}_t\bigr) =\chi\bigl(C_t,\mathcal{L}_t\bigr)$, because
$f_t^*\mathcal{N}_t$ is the pullback of an invertible module on
$\Spec\kappa(t)$ and hence trivial. The asserted equality follows, and
[lem-pc-euler-additive] supplies the additivity of $\chi$ used here.

*(3) Base change.* For $t'\in T'$ with image $t\in T$ the residue field
$\kappa(t')$ is an extension of $\kappa(t)$ and
$(g_C^*\mathcal{L})_{t'}=(\mathcal{L}_t)_{\kappa(t')}$; the equality is
[lem-pc-degree-base-change](1) applied to the field extension
$\kappa(t')\big/\kappa(t)$.
