+++
id = "lem-pur-lisse-uniqueness"
kind = "lemma"
title = "Uniqueness for lisse sheaf maps"
order = 1960
uses = ["def-pur-conventions", "def-weil-derived-cohomology-sheaves", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-a1-components", "lem-pur-lisse-morphism-rigidity", "thm-pur-td-criterion"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $j:\mathbf G_{m,B}\hookrightarrow\mathbf A^1_B$. If $L$ and
$M$ are finite locally constant $\Lambda$-sheaves on
$\mathbf A^1_B$, then two sheaf morphisms $L\to M$ which agree after
restriction by $j^*$ agree everywhere. Likewise, two maps between
finite locally constant sheaves on $\mathbf G_{m,B}$ agree if they
agree after restriction to the section $1:B\to\mathbf G_{m,B}$.

## Proof

By [lem-pur-lisse-morphism-rigidity](1) the sheaf
$\mathcal Hom(L,M)$ is finite locally constant on the source, and by
[lem-pur-lisse-morphism-rigidity](2) a morphism between finite
locally constant sheaves vanishes as soon as it vanishes at one
geometric point of every connected component of that source. Apply
this to the difference of the two morphisms. For the first assertion
the difference vanishes on $\mathbf G_{m,B}$, and every connected
component of $\mathbf A^1_B$ meets $\mathbf G_{m,B}$ by
[lem-pur-a1-components](2); for the second assertion the
difference is a morphism on $\mathbf G_{m,B}$ whose stalk vanishes at
the unit section, and every connected component of
$\mathbf G_{m,B}$ meets the image of that section by
[lem-pur-a1-components](3). This is ordinary faithfulness for
morphisms of sheaves, not the false derived-category faithfulness
excluded in the remark after [thm-pur-td-criterion].
