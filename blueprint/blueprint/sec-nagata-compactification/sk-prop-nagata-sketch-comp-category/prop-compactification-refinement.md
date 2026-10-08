+++
id = "prop-compactification-refinement"
kind = "theorem"
title = "Existence and common refinement"
order = 415
tags = ["latex:proposition"]
uses = ["def-weil-compactifications-refinements", "def-weil-scheme-morphism-properties", "prop-nagata-compactification-category", "thm-nagata-compactification"]
+++
Let $K$ be a field, let $X,Y$ be finite-type $K$-schemes, and let
$f:X\to Y$ be a separated finite-type $K$-morphism. Let
$\operatorname{Comp}(f)$ be the compactification category
([def-weil-compactifications-refinements]) whose objects are factorizations
$X\xrightarrow{j}\overline X\xrightarrow{\bar f}Y$ with $j$ an open
immersion, $\bar f$ proper, and $\bar f j=f$, and whose morphisms are proper
$Y$-morphisms $u:\overline X_1\to\overline X_2$ with $u j_1=j_2$. This
category is nonempty (Nagata's theorem, [thm-nagata-compactification]) and
cofiltered: finitely many objects admit a common refinement, and any two
parallel refinements become equal after a further refinement.

## Proof

The category $\operatorname{Comp}(f)$ of
[def-weil-compactifications-refinements] is nonempty by the
compactification clause of [thm-nagata-compactification]: every
separated finite-type morphism of finite-type schemes over a field
admits a compactification $X\xrightarrow{j}\overline X
\xrightarrow{\bar f}Y$ with $j$ an open immersion and $\bar f$
proper, exactly the objects of $\operatorname{Comp}(f)$. That the
category is cofiltered is [prop-nagata-compactification-category], applied
over the base $Y$: the scheme $Y$ is of finite type over the field $K$,
hence Noetherian, so quasi-compact and quasi-separated, and every open
immersion into the Noetherian scheme $\overline X$ is quasi-compact; so the
category of [prop-nagata-compactification-category] for $f:X\to Y$ is
$\operatorname{Comp}(f)$. Its clause (i) gives a common proper refinement of
any two compactifications, hence by induction of any finite family, and its
clause (ii) says that any two parallel refinements become equal after a
further refinement; its base-change clauses state the functoriality up to
refinement used in [def-weil-compactifications-refinements].
