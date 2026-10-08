+++
id = "lem-weil-pbc-proper-base-change"
kind = "lemma"
title = "Properness is stable under base change"
order = 906
uses = ["def-weil-pbc-scheme-conventions"]
+++
If $f:X\to Y$ is proper [def-weil-pbc-scheme-conventions] and $g:Y'\to Y$ is
arbitrary, then the base change $f':X\times_YY'\to Y'$ is proper.

## Proof

For $f$ separated or of finite type, the base change $f'$ has the same
property by the corresponding stability of closed diagonals and of finite
generation under base change, in the sense of
[def-weil-pbc-scheme-conventions]; and $f'$ is universally closed because
every base change of $f'$ is a base change of $f$, which is a closed map by
the universal closedness of $f$. Hence $f'$ is proper by
[def-weil-pbc-scheme-conventions].
