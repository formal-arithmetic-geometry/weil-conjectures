+++
id = "def-nagata-two-open-final-modification"
kind = "definition"
title = "Final common modification for the two-open construction"
order = 298
uses = ["def-nagata-common-modification", "def-nagata-two-open-intermediate-schemes"]
+++
Apply the common-modification construction to the two open immersions
$U\hookrightarrow W_1$ and $U\hookrightarrow W_2$. Denote its output by

$$
W'_i\longrightarrow W_i,
\qquad
W=\mathsf{CM}(W_1,W_2;U),
$$

with the two constructed open immersions $W'_i\hookrightarrow W$ and their
common open subscheme $U$.

*Implementation note.* There is no separate Lean declaration for this
construction. The proof of `AlgebraicGeometry.HasCompactification.of_two_open_cover`
([thm-nagata-two-open]) obtains it inline, as
`obtain ⟨cm⟩ := nonempty_commonModification ...` applied to the two intermediate
schemes; its type is the structure `AlgebraicGeometry.CommonModification` of
[def-nagata-common-modification].
