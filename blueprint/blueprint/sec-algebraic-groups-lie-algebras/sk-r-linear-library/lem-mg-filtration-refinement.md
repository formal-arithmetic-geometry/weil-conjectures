+++
id = "lem-mg-filtration-refinement"
kind = "lemma"
title = "Refining a finite filtration"
order = 2544
uses = ["def-mg-weil-composition-series", "lem-mg-composition-series-exists", "lem-mg-jordan-holder"]
+++
Let $0=M_0\subseteq M_1\subseteq\cdots\subseteq M_s=M$ be a finite
filtration by Weil subrepresentations. In the terminology of
[def-mg-weil-composition-series], the composition-factor multiset of
$M$ is the disjoint union of the composition-factor multisets of the
quotients $M_i/M_{i-1}$.

## Proof

For every index with $M_i/M_{i-1}\ne0$, choose a composition series,
using [lem-mg-composition-series-exists]; indices with zero quotient
contribute no factors. Pull the chosen terms back to $M_i$
and concatenate the resulting chains. This refines the displayed
filtration to a composition series in the sense of
[def-mg-weil-composition-series], and its factors are precisely the
factors of the successive quotients. Independence of all choices follows
from [lem-mg-jordan-holder].
