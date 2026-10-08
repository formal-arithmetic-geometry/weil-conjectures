+++
id = "def-cbc-completed-exchange-map"
kind = "definition"
title = "Completed compact-support exchange map"
order = 1588
uses = ["def-cbc-exchange-map", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-completed-pullback", "def-weil-pbc-scheme-conventions", "lem-cbc-completed-extension-zero-comparison", "thm-weil-pbc-complete-proetale"]
+++
In the situation of [def-cbc-exchange-map], let $(A,I)$
satisfy [def-weil-pbc-adic-coefficient-datum] and let
$K\in D(X_{\Proet},A)$ be derived $I$-complete. For a
compactification $c=(j,p)$ and its base change $c'$, define the
*completed compact-support exchange map*

$$
\Ex^{\mathrm{comp}}_!(K):
Lg^*_{\mathrm{comp}}Rf_!K\longrightarrow Rf'_!Lg'^*_{\mathrm{comp}}K
$$

as the composite of the completed proper-base-change exchange map of
[thm-weil-pbc-complete-proetale] applied to $p$ and
$j_!K$, with the completed extension-by-zero comparison
$Lg'^*_{\mathrm{comp}}j_!K\xrightarrow{\sim}j'_!Lg'^*_{\mathrm{comp}}K$
of [lem-cbc-completed-extension-zero-comparison]; this is the
coefficient-level form of the map of [def-cbc-exchange-map].
