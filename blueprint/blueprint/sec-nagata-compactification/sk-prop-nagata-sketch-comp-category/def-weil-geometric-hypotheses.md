+++
id = "def-weil-geometric-hypotheses"
kind = "definition"
title = "Geometric hypotheses"
order = 412
uses = ["def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
For the global finite-field datum [def-weil-finite-field-fiber]
$(p,a,q,k_0,k)$, let $Y_0$ be a finite-type
[def-weil-scheme-morphism-properties] $k_0$-scheme. It is *smooth of pure
dimension $d$* if $d\in\mathbf Z_{\geq0}$, the structure morphism $Y_0\to\Spec
k_0$ is a smooth morphism, and every irreducible component of
$Y_0\times_{k_0}k$ has Krull dimension $d$. It is *proper* if its structure
morphism is separated, of finite type, and universally closed, i.e. it is a
proper morphism. It is *geometrically connected* if it is nonempty and
$Y_0\times_{k_0}k'$ is connected for every field extension $k'/k_0$,
equivalently if its geometric fiber $Y_0\times_{k_0}k$ is nonempty and
connected.
