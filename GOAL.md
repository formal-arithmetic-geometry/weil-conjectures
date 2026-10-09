# GOAL

**Decision of the human (2026-10-09, evening): the whole Weil conjecture is too large a target for now. The target of the run is the single node `thm-weil-pbc-bounded-below` (bounded-below derived proper base change), chapter `sec-proper-base-change`, unit `sk-thm-properbasechange`. Its Lean declarations are `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` and `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring` in `WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Proper.lean` (both branches; on master the first contains a `sorry`, on slopmaster2 neither does, but they may rest on sorries). `thm-weil-final` keeps its node and loses the `target` flag; nodes the new target does not reach stop being items. The text below is the earlier goal, kept for the record.**

Formalize the following result of the Weil-conjectures blueprint (`literature/blueprint/master/blueprint/`, from `github.com/formal-arithmetic-geometry/weil-conjectures`, branch `master`) with no `sorry`.

| Label in the paper | Statement in one line | Lean declaration | Module |
|---|---|---|---|
| `thm-weil-final`, "Weil conjectures for a smooth proper variety" (blueprint order 2939) | For $X_0$ smooth, proper, geometrically connected of pure dimension $d$ over $\mathbf F_q$: the zeta series is rational with its two point-counting descriptions; it factors through unique integral polynomials $P_i$ realized by Frobenius on $H^i(X,\mathbf Q_\ell)$; the reciprocal roots of $P_i$ are $q$-Weil numbers of weight $i$; Betti symmetry and the endpoint factors; the functional equation. | not written in this project | |

The statement, word for word from the blueprint (node `dag/nodes/sec-zeta-weil/thm-weil-final.json`):

> Let $X_0$ be a smooth, proper, geometrically connected scheme of pure
> dimension $d$ over $\Fq$. Put $X=X_0\times_{\Fq}k$, let
> $\mathscr X$ be the resulting smooth-proper datum, and let
> $P_i=P_i(\mathscr X)$ be the canonical factors of
> Definition *Canonical integral cohomological factors*. Then the following
> statements hold.
> 
> 1. The zeta series has both point-counting descriptions
> $$
> Z(X_0,T)=
> \exp\left(\sum_{n\geq1}
> \#X_0(\mathbf F_{q^n})\frac{T^n}{n}\right)
> =\prod_{x\in|X_0|}(1-T^{\deg(x)})^{-1},
> $$
> and belongs to $1+T\mathbf Z[[T]]\cap\mathbf Q(T)$.
> 1. The polynomials $P_i$ are the unique polynomials
> $$
> P_i(T)\in\mathbf Z[T]
> \qquad(0\leq i\leq2d)
> $$
> with $P_i(0)=1$ such that, for every prime $\ell\neq p$,
> $$
> \bigl((\mathbf Z[T]\longrightarrow\Ql[T])(P_i)\bigr)(T)=
> \det(1-TF\mid H^i(X,\Ql)).
> $$
> They give the rational factorization
> $$
> Z(X_0,T)=
> \prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}.
> $$
> 1. Fix an algebraic closure $\overline{\mathbf Q}$ of $\mathbf Q$
> and regard $P_i\in\mathbf Z[T]$ inside
> $\overline{\mathbf Q}[T]$. For every $0\leq i\leq2d$, every
> reciprocal root $\alpha\in\overline{\mathbf Q}$ of $P_i$ is an
> algebraic integer
> and a $q$-Weil number of weight $i$:
> $$
> |\tau(\alpha)|=q^{i/2}
> $$
> for every embedding
> $\tau:\mathbf Q(\alpha)\hookrightarrow\mathbf C$. For every ordinary
> root $\beta\in\overline{\mathbf Q}$ of $P_i$ and every embedding
> $\tau:\mathbf Q(\beta)\hookrightarrow\mathbf C$, one has
> $|\tau(\beta)|=q^{-i/2}$.
> 1. For every $0\leq i\leq2d$, with $b_i=\deg P_i$, and every
> prime $\ell\neq p$,
> $$
> b_i=\dim_{\Ql}H^i(X,\Ql),
> \qquad b_i=b_{2d-i},
> \qquad b_0=b_{2d}=1,
> $$
> independently of $\ell$. Moreover
> $$
> P_0(T)=1-T,
> \qquad
> P_{2d}(T)=1-q^dT.
> $$
> In particular $Z(X_0,T)$ has a pole of order exactly $1$ at $T=1$
> and, if $d\geq1$, a pole of order exactly $1$ at $T=q^{-d}$.
> 1. If
> $$
> D_i=(-1)^{b_i}[T^{b_i}]P_i(T),
> \qquad
> \chi=\sum_{i=0}^{2d}(-1)^ib_i,
> $$
> then $d\chi$ is even and, for every $0\leq i\leq2d$,
> $$
> P_{2d-i}(q^{-d}T^{-1})
> =(-1)^{b_i}T^{-b_i}D_i^{-1}P_i(T),
> $$
> and
> $$
> Z(X_0,q^{-d}T^{-1})
> =\varepsilon q^{d\chi/2}T^\chi Z(X_0,T)
> $$
> for the sign
> $$
> \varepsilon=
> (-1)^\chi q^{-d\chi/2}
> \prod_{i=0}^{2d}D_i^{(-1)^i}
> \in\{1,-1\}.
> $$

In the source repository the blueprint names `AlgebraicGeometry.Scheme.weil_conjectures` for this node (module `WeilConjectures.Statement`, branch `master`, proof `sorry`). The blueprint's own status paragraph says that this declaration states clauses 2, 3 and 5 for a geometrically integral $X_0$, and that `AlgebraicGeometry.Scheme.zetaSeries_rational` states the rationality assertion of clause 1 for a scheme of finite type; no declaration there states the whole node.

Out of scope: not decided.

Completion criterion, both parts:

1. [Lean comparator](https://github.com/leanprover/comparator) accepts the library against `lean/Challenge.lean`: every target is proved with exactly the statement written there, with no axiom beyond `propext`, `Classical.choice`, `Quot.sound`.
2. Every statement in `lean/Challenge.lean`, read with the definitions it uses, means exactly what the statement in the paper means, as the review in `coord/targets-review.md` shows.
