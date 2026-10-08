+++
id = "def-trf-dualizing-complex"
kind = "definition"
title = "Dualizing complex and Verdier dual"
order = 2225
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, put $s=\Spec k$, and let $Y$ be a
separated finite-type
$k$-scheme whose
structure morphism
$a_Y:Y\to s$ is
exceptionally admissible in the sense of [def-trf-admissibility] (which
holds for every such $Y$; no ambient datum is assumed). Put

$$
\omega_{Y,A}:=Ra_Y^!A_s,\qquad
D_YM:=R\mathcal Hom_A\bigl(M,\omega_{Y,A}\bigr)
\qquad
\bigl(M\in D^b_{ctf}(Y,A)\bigr),
$$

using the exceptional inverse
image of $a_Y$ and the
derived internal Hom and
tensor; here $D^b_{ctf}(Y,A)$ is the
finite-Tor subcategory of the
bounded constructible
derived category. The *evaluation* is the canonical map

$$
\operatorname{ev}_M:D_YM\otimes_A^LM\longrightarrow\omega_{Y,A}
$$

obtained from the tensor–internal-Hom adjunction: it is the transpose of
the identity of $D_YM$ under the
adjunction isomorphism

$$
\Hom_{D(Y,A)}
\bigl(D_YM\otimes_A^LM,\omega_{Y,A}\bigr)
\cong
\Hom_{D(Y,A)}
\bigl(D_YM,R\mathcal Hom_A(M,\omega_{Y,A})\bigr).
$$

Here $\omega_{Y,A}$ is the *dualizing complex* of $Y$ over $A$
and $D_Y$ the *Verdier dual* functor.
