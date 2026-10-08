+++
id = "sbc-thm-etale-local-normal-form"
kind = "theorem"
title = "Etale-local normal form of a smooth morphism"
order = 1400
uses = ["def-exc-jacobian-presentation", "def-sbc-affine-space", "def-sbc-smooth-morphisms", "lem-exc-etale-jacobian-presentation"]
+++
Let $g:Y'\to Y$ be
smooth at $y'\in Y'$. After
replacing $Y,Y'$ by affine neighbourhoods, there are $d\geq0$ and an
etale morphism

$$
e:Y'\longrightarrow\mathbf A^d_Y
$$

such that $g$ is $e$ followed by the projection
$p_d:\mathbf A^d_Y\to Y$ of [def-sbc-affine-space].
(*Stacks Project, Morphisms, [Tag `054L`](https://stacks.math.columbia.edu/tag/054L) = Lemma
29.37.21.*)

## Proof

Choose affine neighbourhoods $Y=\operatorname{Spec}R$ and
$Y'=\operatorname{Spec}C$ of the specified points, small enough
that $g$ is smooth on the latter. We use the ordinary
commutative-algebra infinitesimal criterion: a finitely presented
formally smooth algebra is smooth
([Stacks, Tag 00TN](https://stacks.math.columbia.edu/tag/00TN)),
and near any prime it has a presentation

$$
C=R[x_1,\ldots,x_N]/(F_1,\ldots,F_c),\qquad
\det\left(\frac{\partial F_a}{\partial x_b}\right)_{a,b\leq c}
\in C^\times.
$$

The latter is the standard-presentation lemma of commutative
algebra ([Tag 00TA](https://stacks.math.columbia.edu/tag/00TA)).
Its algebraic mechanism is to choose a basis of the projective
conormal module, then a nonzero minor of its split injection into
the free module of differentials. Localizing at that minor and
using Nakayama on the finitely generated relation ideal gives the
displayed generators; a localization is incorporated by adjoining
one variable and its inverse relation. These operations replace
the source by an affine open containing the selected point.
This is an application of the ring lifting criterion to the local
lifting condition in [def-sbc-smooth-morphisms].

Put $d=N-c$ and regard the last $d$ variables as base
coordinates: let $P=R[x_{c+1},\ldots,x_N]$. The same presentation
is now a $P$-algebra presentation with $c$ variables and $c$
relations, and its square Jacobian determinant is invertible.
It is exactly a presentation of [def-exc-jacobian-presentation].
For clarity, the lifting assertion for this new base can also be
read directly from the equations. Given a square-zero ideal
$J\subset Q$, a $P$-algebra map $C\to Q/J$ determines
arbitrary lifts $q_b$ of the first $c$ variables. Its errors
$F_a(q)$ lie in $J$. A correction $v\in J^c$ must satisfy

$$
(\partial F_a/\partial x_b)(q)\,v_b=-F_a(q).
$$

There is exactly one solution because the determinant is a unit:
it is a unit modulo a nilpotent ideal and hence a unit in $Q$.
Taylor expansion has no higher correction terms since $J^2=0$.
This constructs the unique lift fixing all the base coordinates.
Successive square-zero quotients treat a general nilpotent ideal.
Consequently [lem-exc-etale-jacobian-presentation] makes
$\operatorname{Spec}C\to\operatorname{Spec}P$ etale.
By [def-sbc-affine-space], $\operatorname{Spec}P=\mathbf A^d_Y$.
The composite with its projection is induced by the original
ring homomorphism $R\to C$, and is therefore exactly $g$.
This constructs the required factorization.
