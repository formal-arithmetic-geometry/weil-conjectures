+++
id = "lem-pc-projective-proper"
kind = "lemma"
title = "Projective morphisms are proper"
order = 757
uses = ["def-pc-base-change", "def-pc-morphism-conventions", "def-pc-projective-morphism", "def-pc-smooth-projective-curve", "lem-pc-proper-base-change"]
+++
A projective morphism of schemes is proper. In particular a
smooth projective curve
over a field is proper over it, and its base changes along field
extensions are proper.

## Proof

A projective morphism $f:X\to S$ factors as
$X\xrightarrow{i}\mathbf P^n_S\xrightarrow{\pi}S$ with $i$ a closed
immersion. Closed immersions are proper (Morphisms of Schemes, Lemma
29.42.6, Tag [01W5](https://stacks.math.columbia.edu/tag/01W5)),
$\pi$ is proper, and properness is stable under composition. For
$\pi$: the structure morphism $\mathbf P^n_S\to S$ is of finite type
and separated (standard: $\mathbf P^n_S$ is a Proj, separated over
$S$), and it is universally closed: by the valuative criterion for
properness (Morphisms of Schemes, Section 29.43, Tag
[0BX4](https://stacks.math.columbia.edu/tag/0BX4): $f$ proper
$\Leftrightarrow$ $f$ is separated, finite type and the valuative
criterion holds) it suffices to lift: let $V$ be a valuation ring with
fraction field $K$, let $\operatorname{Spec} V\to S$ and
$\operatorname{Spec} K\to\mathbf P^n_S$ be morphisms over $S$, and suppose the
diagram commutes after composing with $\operatorname{Spec} K\to\operatorname{Spec} V$. The
$K$-point of $\mathbf P^n$ is $[a_0:\cdots:a_n]$ with $a_i\in K$;
clearing denominators we may assume all $a_i\in V$ and at least one
$v(a_i)=0$ for the valuation $v$ of $V$ (divide by the $a_j$ of
minimal valuation); then $[a_0:\cdots:a_n]$ is a $V$-point of
$\mathbf P^n_V$: the corresponding lift $\operatorname{Spec} V\to\mathbf P^n_{\operatorname{Spec} V}$ exists (the explicit affine chart where some $a_j$ is a unit
gives the inhomogeneous coordinates in $V$), and it is unique (the
same construction is forced). Hence $\pi$ is proper. Compositions:
if $g:X\to Y$ and $f:Y\to Z$ are proper, then $f\circ g$ is proper:
it is separated and of finite type (compositions of separated and
finite type morphisms are so), and a universally closed morphism
composed with a universally closed one is universally closed (a base
change of the composite is the composite of the base changes, and
closed maps compose). Therefore $f$ is proper. The last sentence
follows from [lem-pc-proper-base-change] applied along
$\operatorname{Spec}(K)\to\operatorname{Spec}(k)$.
