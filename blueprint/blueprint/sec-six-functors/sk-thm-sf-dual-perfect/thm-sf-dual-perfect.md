+++
id = "thm-sf-dual-perfect"
kind = "theorem"
title = "The dual of a perfect complex"
order = 2178
uses = ["cor-pur-adic-and-rational-smooth-dualizing-complexes", "cor-pur-finite-stage-smooth-dualizing-complex", "def-pod-conventions", "def-sf-datum", "def-sf-orientation", "def-weil-derived-pullback-tensor-hom", "lem-sf-hom-finite-projective", "lem-sf-twist-interchange", "prop-sf-dualizable", "prop-sf-dualizable-hom"]
+++
In the Poincare duality conventions of [def-pod-conventions] (an
instance of the setting of [def-sf-datum], with $X$ smooth,
separated of finite type and of pure dimension $d$), let
$K\in D^b_{ctf}(X,\Lambda)$ be perfect over $\Lambda_X$, at any
coefficient stage $\Lambda\in\{A_{E,n},\mathcal O_E,E,\overline{\mathbf Q}_\ell\}$.
The smooth dualizing-complex identification
$\eta_X:\omega_{X,\Lambda}\xrightarrow{\ \sim\ }\Lambda_X(d)[2d]$ of the
purity chapter (the orientation of [def-sf-orientation] for $f=a_X$)
and the twist interchange give a canonical isomorphism

$$
\mathbb D_XK\xrightarrow{\ \sim\ }K^\vee(d)[2d],
$$

natural in $K$, compatible with finite reduction, scalar extension,
shifts, and the canonical evaluation. Moreover $K^\vee$ is perfect, the
canonical map $K\to K^{\vee\vee}$ is an isomorphism, and consequently
$\mathbb D_X$ restricts to an anti-equivalence on the perfect objects,
the biduality $K\to\mathbb D_X\mathbb D_XK$ being, under this
identification, the coefficient-dual biduality $K\to K^{\vee\vee}$.

*Relative form.* The same holds for a smooth separated finite-type
$f:X\to Y$ of pure relative dimension $d$ over an arbitrary base $Y$ of the
setting: with the orientation $\gamma_f:\Lambda_X(d)[2d]\xrightarrow{\sim}
Rf^!\Lambda_Y$ of [def-sf-orientation] and
$\mathbb D_{X/Y}K=R\mathcal Hom_X(K,Rf^!\Lambda_Y)$, the composite of
$R\mathcal Hom_X(K,\gamma_f^{-1})$ with the twist interchange is a natural
isomorphism $\mathbb D_{X/Y}K\xrightarrow{\sim}K^\vee(d)[2d]$ for perfect
$K$, with the same biduality statement; the absolute case is $f=a_X$. The
proof below uses nothing about the base beyond the orientation.

## Proof

Step 1: the definition. By [def-pod-conventions],
$\mathbb D_XK=R\mathcal Hom_X(K,\omega_{X,\Lambda})$ with
$\omega_{X,\Lambda}=Ra_X^!\Lambda$, and
$K^\vee=R\mathcal Hom_X(K,\Lambda_X)$.

Step 2: the smooth purity input. The smooth dualizing-complex
identification of [cor-pur-finite-stage-smooth-dualizing-complex]
(at the finite stage $A=A_{E,n}$) and its transport
[cor-pur-adic-and-rational-smooth-dualizing-complexes] (at the
$\mathcal O_E$-, $E$- and $\overline{\mathbf Q}_\ell$-stages) provide the
canonical orientation

$$
\eta_X:\omega_{X,\Lambda}\xrightarrow{\ \sim\ }\Lambda_X(d)[2d],
$$

which is the case $f=a_X$ of an orientation datum as in
[def-sf-orientation], compatible with finite reduction, scalar
extension, and shifts.

Step 3: substitution and interchange. Substituting $\eta_X$ into the
internal Hom and using the shift of the second variable,

$$
\mathbb D_XK\cong R\mathcal Hom_X\bigl(K,\Lambda_X(d)[2d]\bigr)
\cong\bigl(R\mathcal Hom_X(K,\Lambda_X(d))\bigr)[2d]
\cong K^\vee(d)[2d],
$$

the second isomorphism being the shift axiom of the derived internal Hom
of [def-weil-derived-pullback-tensor-hom], the third being
[lem-sf-twist-interchange] with $m=d$ (its hypothesis is the
perfectness of $K$ over $\Lambda_X$).

Step 4: canonicality and compatibilities. The composite is canonical
because its ingredients are: the orientation is the canonical one of the
purity chapter, and the twist interchange and the shift identification
are canonical maps of the tensor–internal-Hom adjunction (natural in
$K$; on the generators $K=\Lambda_X^r$ they are the coordinate
isomorphisms; the shift index is the constant $2d$). Naturality in $K$
and compatibility with finite reduction, scalar extension and shifts
follow from the corresponding properties of $\eta_X$ recorded in
[cor-pur-finite-stage-smooth-dualizing-complex] and
[cor-pur-adic-and-rational-smooth-dualizing-complexes], and of the
derived tensor and internal Hom recorded in
[def-weil-derived-pullback-tensor-hom]. The compatibility with the
canonical evaluation is the compatibility of the twist interchange with
the tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom]: the evaluation is the counit,
and the interchange carries the counit for $K\otimes^L\Lambda_X(d)$ to
the counit for $K$ tensored with the identity of $\Lambda_X(d)$, after
unwinding $K^\vee(d)\otimes\Lambda_X(d)$ through the associativity and
commutativity coherence of the derived tensor product.

Step 5: biduality and the anti-equivalence. By [prop-sf-dualizable],
$K^\vee$ is perfect and the evaluation $K\otimes^L_{\Lambda_X}K^\vee\to\Lambda_X$
is defined. Choose locally a bounded complex $P^\bullet$ of finite
projective $\Lambda_X$-modules with a quasi-isomorphism $P^\bullet\to K$.
By [prop-sf-dualizable-hom] (with $M=\Lambda_X$) the dual $K^\vee$ is
represented by $P^{\bullet\vee}$, again bounded with finite projective
terms, and applying this once more $K^{\vee\vee}$ is represented by
$P^{\bullet\vee\vee}$; the canonical map $K\to K^{\vee\vee}$ is then
termwise the double-dual map $P^j\to P^{j\vee\vee}$, an isomorphism by
[lem-sf-hom-finite-projective], compatible with the differentials,
so $K\to K^{\vee\vee}$ is an isomorphism (the statement being local on
the site). Applying Step 3 twice,
$\mathbb D_X\mathbb D_XK\cong\bigl(K^\vee(d)[2d]\bigr)^\vee(d)[2d]\cong K^{\vee\vee}$,
where $\bigl(K^\vee(d)[2d]\bigr)^\vee\cong R\mathcal Hom_X(K^\vee,\Lambda_X(-d)[-2d])\cong K^{\vee\vee}(-d)[-2d]$
by the tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom] (moving the invertible twist
$\Lambda_X(d)$ of the first variable to $\Lambda_X(-d)$ in the second)
and [lem-sf-twist-interchange] with $m=-d$ applied to the perfect
complex $K^\vee$; and
under this identification the biduality map is $K\to K^{\vee\vee}$.
Hence $K\mapsto\mathbb D_XK\cong K^\vee(d)[2d]$ preserves perfect
objects and is its own quasi-inverse on them, i.e. an anti-equivalence of
the perfect objects.
