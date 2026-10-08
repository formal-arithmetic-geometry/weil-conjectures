+++
id = "lem-zl-open-closed-weight"
kind = "lemma"
title = "Open–closed weight devissage"
order = 2815
uses = ["def-weil-complex-weights", "def-weil-open-closed-recollement", "lem-zl-complex-extension", "lem-zl-finite-pushforward", "prop-sf-open-closed-triangle-all-stages"]
+++
Let $j:U_0\hookrightarrow X_0$ be open with closed complement
$i:Z_0\hookrightarrow X_0$. If the two outer terms
$j_!j^*K$ and $i_*i^*K$ of the localization triangle
$j_!j^*K\to K\to i_*i^*K\to$ belong to $D_{\le w}(X_0)$, then so
does $K$.

## Proof

The localization triangle is the open–closed recollement triangle of
[def-weil-open-closed-recollement], which exists for $\Qlb$-Weil complexes by [prop-sf-open-closed-triangle-all-stages]; by hypothesis its two outer
terms lie in $D_{\le w}(X_0)$, so the extension stability of complex
weights [lem-zl-complex-extension] gives $K\in D_{\le w}(X_0)$.
(The closed-immersion term $i_*i^*K$ is a finite-pushforward, hence
has the same weights as $i^*K$ by [lem-zl-finite-pushforward].)
