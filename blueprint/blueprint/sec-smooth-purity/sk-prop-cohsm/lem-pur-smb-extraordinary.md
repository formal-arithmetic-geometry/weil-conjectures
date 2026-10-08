+++
id = "lem-pur-smb-extraordinary"
kind = "lemma"
title = "Smooth base change for the exceptional inverse image"
order = 1995
uses = ["cor-sf-ambient-adjoint-discharge", "def-exchange-projection", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-ambient-exceptional-adjoint", "def-weil-exceptional-inverse-image", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "prop-asd-smooth-base-change", "thm-cbc-finite-level-proetale", "thm-sf-ambient-adjoint-class", "thm-weil-pbc-site-comparison"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let

$$
\begin{array}{ccc}
X'&\xrightarrow{\ u\ }&X\\
f'\downarrow&&\downarrow f\\
Y'&\xrightarrow{\ v\ }&Y
\end{array}
$$

be a Cartesian square in which $f$ is
smooth of pure relative dimension
$d$; the
ambient exceptional right
adjoint datum of [def-weil-ambient-exceptional-adjoint] is not assumed,
the right adjoints $Rf^!$, $Rf'^!$ that occur being, on the coefficients
used here, the theorem [cor-sf-ambient-adjoint-discharge]. Let
$K\in D^b_{ctf}(Y,\Lambda)$. The canonical
comparison

$$
Lu^*Rf^!K\xrightarrow{\ \sim\ }Rf'^!Lv^*K
$$

is an isomorphism. The morphism $v$ is arbitrary; its base change
$f'$ is smooth of the same relative dimension.

## Proof

Choose the etale-origin representative of $K$. The comparison
of actual adjoints in [thm-sf-ambient-adjoint-class] identifies
the two exceptional inverse images with the pro-etale realizations
of the corresponding ordinary etale ambient right adjoints.
On those ordinary derived categories, the canonical map is
[prop-asd-smooth-base-change], and is an isomorphism for arbitrary
$v$. Its construction transposes the compact-support base-change
map followed by the counit; it uses the explicit projective-line
adjunction and etale charts, without a chosen smooth orientation.
By [thm-cbc-finite-level-proetale], compact-support base change
transports to the stated site. The adjunction bijections and counits
transport by [thm-sf-ambient-adjoint-class], so the realized map
is precisely the comparison in the statement, not merely an
isomorphism between its source and target.
Finally [thm-weil-pbc-site-comparison] preserves the proved
isomorphism on these etale-origin objects. This argument makes no
assertion about arbitrary pro-etale complexes outside that class.
