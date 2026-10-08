+++
id = "lemma-nagata-proper-valuative-criterion-existence-api"
kind = "lemma"
title = "Existence part of the proper valuative criterion"
order = 295
lean = ["AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion"]
uses = ["lemma-nagata-local-domain-valuation-dominates", "lemma-nagata-valuation-intersection"]
+++
Let $f\colon Y\to S$ be proper. For every valuation ring $A$ with
fraction field $K$, every $S$-morphism
$\operatorname{Spec}(K)\to Y$ lying over a morphism
$\operatorname{Spec}(A)\to S$ extends to an $S$-morphism
$\operatorname{Spec}(A)\to Y$.

## Proof

Let $G$ be the closure of the graph of the given generic map in
$Y\times_S\operatorname{Spec}(A)$. Properness of $Y\to S$ makes
$G\to\operatorname{Spec}(A)$ proper, and the generic point of $G$ maps to
the generic point of $\operatorname{Spec}(A)$. Choose an irreducible
component $G_0$ dominating $\operatorname{Spec}(A)$ and replace it by its
reduced induced scheme. At a point over the closed point of
$\operatorname{Spec}(A)$, the local ring of $G_0$ is a local domain $B$
with fraction field $L$ containing $K$. By
[lemma-nagata-local-domain-valuation-dominates], choose a valuation
ring $C\subset L$ dominating $B$. The resulting map
$\operatorname{Spec}(C)\to G_0$ has generic restriction equal to the
prescribed map. Its restriction on $K$ and the map to $A$ agree; the
intersection identity
$K\cap C=A$ (applied to $A\subset K\subset L$) therefore makes the local
homomorphism factor through $A$. This gives a morphism
$\operatorname{Spec}(A)\to G\to Y$ extending the generic map. The
construction is compatible with the structural maps to $S$ by the
definition of the graph closure.
