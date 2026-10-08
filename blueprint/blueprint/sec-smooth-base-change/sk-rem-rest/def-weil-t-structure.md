+++
id = "def-weil-t-structure"
kind = "definition"
title = "t-structure"
order = 1424
+++
A *t-structure* on a triangulated category $\mathcal T$ is a pair $(\mathcal
T^{\le0},\mathcal T^{\ge0})$ of strictly full subcategories such that

1. $\mathcal T^{\le0}[1]\subseteq\mathcal T^{\le0}$ and $\mathcal
   T^{\ge0}[-1]\subseteq\mathcal T^{\ge0}$;
2. $\Hom_{\mathcal T}(A,B[-1])=0$ for all $A\in\mathcal T^{\le0}$ and
   $B\in\mathcal T^{\ge0}$;
3. every $K\in\mathcal T$ occurs in a distinguished triangle $A\to K\to
   B[-1]\to A[1]$ with $A\in\mathcal T^{\le0}$ and $B\in\mathcal T^{\ge0}$.

Write $\mathcal T^{\le n}=\mathcal T^{\le0}[-n]$ and $\mathcal T^{\ge
n}=\mathcal T^{\ge0}[-n]$. The *heart* is $\mathcal T^{\le0}\cap\mathcal
T^{\ge0}$, and the t-structure is *bounded* if every object of $\mathcal T$
lies in $\mathcal T^{\le n}\cap\mathcal T^{\ge m}$ for some $m\le n$. A
bounded t-structure carries truncation functors $\tau^{\le n},\tau^{\ge
n}:\mathcal T\to\mathcal T$ and distinguished truncation triangles

$$
 \tau^{\le n}K\longrightarrow K\longrightarrow
 \tau^{\ge n+1}K\longrightarrow\tau^{\le n}K[1],
$$

characterized by $\tau^{\le n}K\in\mathcal T^{\le n}$ and $\tau^{\ge
n+1}K\in\mathcal T^{\ge n+1}$.

(*Source note:* no Stacks Project entry states this form: Stacks defines no
t-structure on a triangulated category. Its nearest entries are the
truncation of a complex of an abelian category, Homological Algebra, Section
12.15 (Tag [0118](https://stacks.math.columbia.edu/tag/0118)), where the
canonical truncations $\tau_{\le n}$, $\tau_{\ge n}$ of a (co)chain complex
are defined with the properties $H^i(\tau_{\le n}A^\bullet)=H^i(A^\bullet)$
for $i\le n$ and $0$ for $i>n$, and the canonical distinguished triangle
$\tau_{\le a}K^\bullet\to K^\bullet\to\tau_{\ge a+1}K^\bullet\to (\tau_{\le
a}K^\bullet)[1]$ of Remark 13.12.4 (Tag
[08J5](https://stacks.math.columbia.edu/tag/08J5), in $D(\mathcal A)$ for an
abelian $\mathcal A$). Difference: those entries truncate complexes of one
fixed abelian category inside $D(\mathcal A)$; they state no t-structure
axioms on an abstract triangulated category, no heart, no boundedness, and no
truncation functors on such a category — pages checked for a counterpart: the
tables of contents of Chapters 12, 13 and 21 and Sections 12.4, 12.5, 12.15,
13.11, 13.12 and 13.34, and the table of contents of Chapter 61. The
blueprint adds the axiom list together with the truncation functors
$\tau^{\le n},\tau^{\ge n}$ and their triangles, the structure on which the
integral and rational coefficient categories of this manuscript rest.)
