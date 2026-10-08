+++
id = "lem-kun-stalk-as-pullback"
kind = "lemma"
title = "A stalk is inverse image to a geometric point"
order = 1677
uses = ["def-weil-pbc-etale-site", "def-weil-pbc-geometric-stalks", "def-weil-pbc-inverse-image", "def-weil-pbc-pointed-etale-neighbourhoods", "prop-weil-pbc-geometric-stalks-exact"]
+++
If $\bar t:\Spec(\Omega)\to T$ is a geometric point, the stalk of a
sheaf (or derived object) at $\bar t$ is its inverse image along
$\bar t$.

## Proof

Inverse image along $\bar t:\Spec(\Omega)\to T$ restricts a sheaf to
the site of $\Spec(\Omega)$; the sections over $\Spec(\Omega)$ of
that restriction are the colimit over the pointed etale
neighbourhoods of $\Cref{def-weil-pbc-pointed-etale-neighbourhoods}$,
which is the stalk of [def-weil-pbc-geometric-stalks]. For
derived objects, exactness of
[prop-weil-pbc-geometric-stalks-exact] passes the statement to
complexes.
