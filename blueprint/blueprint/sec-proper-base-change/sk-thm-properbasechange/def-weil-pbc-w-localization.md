+++
id = "def-weil-pbc-w-localization"
kind = "definition"
title = "The affine w-localization"
order = 1222
uses = ["def-weil-pbc-ind-etale-algebra", "def-weil-pbc-w-local"]
+++
For a ring $A$, consider finite partitions $\mathcal P$ of
$\operatorname{Spec}A$ into nonempty constructible
[def-weil-pbc-w-local] sets. For each part $E$, choose $f_E\in A$ with
$E\subset D(f_E)$. Refining a partition and multiplying its denominators
gives a directed system of algebras $\prod_{E\in\mathcal P}A_{f_E}$. Define

$$
 A^w=\varinjlim_{(\mathcal P,(f_E))}
          \prod_{E\in\mathcal P}A_{f_E}.
$$

The transition maps are the componentwise localization maps; common
refinements use intersections of parts and products of denominators. This
specifies an ind-Zariski [def-weil-pbc-ind-etale-algebra] algebra, without
asserting its geometric properties in the definition.
