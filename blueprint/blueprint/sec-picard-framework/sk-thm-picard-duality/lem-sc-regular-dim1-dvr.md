+++
id = "lem-sc-regular-dim1-dvr"
kind = "lemma"
title = "One-dimensional regular local rings"
order = 693
uses = ["lem-sc-principal-ideal-dvr", "lem-sc-regular-local-domain"]
+++
A regular local ring of dimension one is a discrete valuation ring.

## Proof

A regular local ring of dimension one has
$\dim_R\mathfrak m/\mathfrak m^2=1$, so $\mathfrak m=(t)$ for
some $t$ (Nakayama's lemma: *reference: Stacks Project,
Algebra, Lemma 10.20.1, [Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)*), and $R$ is a domain
([lem-sc-regular-local-domain]). Hence $R$ is a discrete
valuation ring by [lem-sc-principal-ideal-dvr].
