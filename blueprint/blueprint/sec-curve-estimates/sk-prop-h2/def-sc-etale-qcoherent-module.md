+++
id = "def-sc-etale-qcoherent-module"
kind = "definition"
title = "The etale sheaf associated with a quasi-coherent module"
order = 958
uses = ["def-weil-pbc-etale-site", "lem-sc-etale-qcoherent-descent"]
+++
Let $X$ be a scheme and $\mathcal F$ a quasi-coherent
$\mathcal O_X$-module. The associated sheaf $\mathcal F_{\mathrm{et}}$
on the small etale site assigns to
$u:U\to X$ the group $\Gamma(U,u^*\mathcal F)$, with the usual
pullback restrictions. Here $u^*\mathcal F$ is pullback as a module
on a ringed space. That this presheaf is already a sheaf – so that
the assignment defines a sheaf and not merely a presheaf – is the
descent property of quasi-coherent modules,
[lem-sc-etale-qcoherent-descent], and it is not part of the
definition.
