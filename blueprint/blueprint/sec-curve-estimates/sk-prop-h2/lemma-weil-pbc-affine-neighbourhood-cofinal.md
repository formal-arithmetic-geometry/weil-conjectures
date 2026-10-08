+++
id = "lemma-weil-pbc-affine-neighbourhood-cofinal"
kind = "lemma"
title = "Affine pointed neighbourhoods are cofinal"
order = 943
uses = ["def-weil-pbc-pointed-etale-neighbourhoods", "def-weil-pbc-scheme-conventions"]
+++
The full subcategory $\mathcal N^{\mathrm{aff}}_{\bar s}$ of affine pointed
etale neighbourhoods is initial in $\mathcal N_{\bar s}$ and hence cofinal
for the opposite-indexed stalk colimit.

## Proof

Given $(V,\bar v)$, choose an affine open $V_0\subseteq V$ containing the
image of $\bar v$; then $(V_0,\bar v)\to(V,\bar v)$ is a morphism. Given two
affine refinements, their fibre product over $V$ contains the lifted geometric
point; an affine open around that point refines both. These two facts give
nonemptiness and connectedness of every comma category required for
initiality.

## Detailed form

The full subcategory of affine [def-weil-pbc-scheme-conventions] pointed
etale neighborhoods is initial in $\mathcal N_{\bar s}$ of
[def-weil-pbc-pointed-etale-neighbourhoods], hence cofinal for the
opposite-indexed stalk colimit.

## Proof

Given $(V,\bar v)$, an affine open $V_0\subseteq V$ containing the image of
$\bar v$ gives a morphism $(V_0,\bar v)\to(V,\bar v)$; given two affine
refinements, an affine open of their fibre product around the lifted point
refines both. These two facts are exactly the nonemptiness and connectedness
of the comma categories required for initiality in the sense of
[def-weil-pbc-pointed-etale-neighbourhoods].
