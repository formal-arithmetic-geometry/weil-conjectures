+++
id = "def-per-perverse-subcategories"
kind = "definition"
title = "Perverse subcategories of the first kind"
order = 2739
uses = ["def-per-support-condition", "def-weil-pbc-qbar-category"]
+++
In the setting of [def-per-support-condition], put

$$
\begin{aligned}
{}^pD^{\le0}(X)&:=\bigl\{K:\ \operatorname{SuppCon}(K)\bigr\},\\
{}^pD^{\ge0}(X)&:=\bigl\{K:\ \operatorname{CosuppCon}(K)\bigr\},
\end{aligned}
$$

and, for every $n\in\mathbf Z$,

$$
{}^pD^{\le n}(X):={}^pD^{\le0}(X)[-n],\qquad
{}^pD^{\ge n}(X):={}^pD^{\ge0}(X)[-n].
$$

The *perverse heart candidate* is

$$
\mathrm{Perv}^{\mathrm{cand}}(X):={}^pD^{\le0}(X)\cap{}^pD^{\ge0}(X).
$$
