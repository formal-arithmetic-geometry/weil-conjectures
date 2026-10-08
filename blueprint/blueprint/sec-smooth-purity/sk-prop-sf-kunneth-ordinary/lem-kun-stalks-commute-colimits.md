+++
id = "lem-kun-stalks-commute-colimits"
kind = "lemma"
title = "Geometric stalks commute with colimits"
order = 1687
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks", "prop-weil-pbc-geometric-stalks-exact"]
+++
Let $T$ be a scheme and $\bar t$ a geometric point of $T$. The
stalk functor $F\mapsto F_{\bar t}$ of
[def-weil-pbc-geometric-stalks] commutes with arbitrary colimits
of sheaves on $T_{\Et}$; consequently it commutes with colimits of
complexes of sheaves, computed termwise.

## Proof

By [def-weil-pbc-geometric-stalks] the stalk $F_{\bar t}$ is
the filtered colimit of the groups $F(U)$ over pointed etale
neighbourhoods of $\bar t$. Colimits of sheaves are computed as the
sheafification of the objectwise colimit of the underlying presheaves,
and sheafification is left adjoint to the inclusion of sheaves, so
evaluation at a fixed etale object $U$ preserves colimits of sheaves;
a filtered colimit of functors preserving colimits preserves colimits,
whence the stalk functor preserves colimits. The exactness of the
stalk functors recorded in
[prop-weil-pbc-geometric-stalks-exact] is the finite case of the
same statement, and sheaves are those of
[def-weil-pbc-etale-sheaves].
