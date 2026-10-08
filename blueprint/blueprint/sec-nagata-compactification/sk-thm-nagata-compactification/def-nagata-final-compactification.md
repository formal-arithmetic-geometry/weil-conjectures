+++
id = "def-nagata-final-compactification"
kind = "definition"
title = "Final Nagata compactification candidate"
order = 402
lean = ["AlgebraicGeometry.NagataCompactification"]
uses = ["def-nagata-closed-subscheme-compactification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-final-basechanged-compactification", "def-nagata-final-fp-envelope", "lemma-nagata-final-basechanged-compactification", "lemma-nagata-final-fp-envelope", "prop-nagata-closed-subscheme-compactifiable", "prop-nagata-finite-type-closed-in-fp"]
+++
By [lemma-nagata-final-fp-envelope], [def-nagata-final-basechanged-compactification]
applies to $Y=X_f^{\mathrm{fp}}$; write
$C_f^{\mathrm{fp}}=\mathsf C^{\mathrm{fp}}(X_f^{\mathrm{fp}}/S)
=\bigl(X_f^{\mathrm{fp}}\hookrightarrow
\overline X_f^{\mathrm{fp}}\longrightarrow S\bigr)$. Define

$$
\mathsf C_{\mathrm{Nag}}(f)
=\mathsf{Closed}(i_f^{\mathrm{fp}},C_f^{\mathrm{fp}})
=\bigl(X\xrightarrow{j_f}\overline X_f
\xrightarrow{p_f}S\bigr).
$$
