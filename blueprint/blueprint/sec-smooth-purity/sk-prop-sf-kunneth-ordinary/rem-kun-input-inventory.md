+++
id = "rem-kun-input-inventory"
kind = "remark"
title = "Inventory of the imported inputs of this chapter"
order = 1782
uses = ["lem-kun-0f14a", "lem-kun-0f14b", "lem-kun-0f1h", "lem-kun-0f1i", "lem-kun-0f1j", "lem-kun-0f1n", "thm-kun-0f1p"]
+++
The Kunneth-specific arguments of this chapter are decomposed in full:
the Kunneth map and its comparison with the cup product
([def-kun-kunneth-map], *The Kunneth map via the relative cup product*,
[lem-kun-kunneth-map-agrees]), the one-proper-factor formula
([lem-kun-0f14a], [lem-kun-0f14b]), the closed-point
statements, the open-immersion base change [lem-kun-0f1h], the
field base change [lem-kun-0f1i], the projection-formula variant
[lem-kun-0f1j] and its unbounded form [lem-kun-0f1n], and
the final theorem [thm-kun-0f1p]. The statements listed below are
the *imported general inputs* that these proofs quote; each is a
decomposed statement with a Stacks reference, and each is used only
where no earlier chapter of this blueprint supplies it.

1. *Limits:* the base change along limits of cartesian squares
[lem-kun-0ezt]
(Tag [0EZT](https://stacks.math.columbia.edu/tag/0EZT)) and the
descent of a sheaf on an affine inverse limit
[lem-kun-descent-limit]
(Tag [0EYN](https://stacks.math.columbia.edu/tag/0EYN)). The
descent of a quasi-compact open in an affine limit is proved in this
chapter as [lem-kun-descent-limit-open] (the affine case of Tag
[01ZM](https://stacks.math.columbia.edu/tag/01ZM)); the ambient-foundations chapter
proves the continuity
thm:weil-pbc-etale-cohomology-continuity and the smooth-base-change chapter the
higher-direct-image limit formula
[sbc-lem-higher-direct-image-limit], which are the cases quoted in
the proofs above; the two statements listed here are the limit
statements that are not among those.
1. *Constructibility:* the constructible generation
[lem-kun-03sa]
(Tag [03SA](https://stacks.math.columbia.edu/tag/03SA)). The
approximation with controlled support that the proofs above quote is
proved in this chapter as [lem-kun-cp-approximation], in the case of
the set of closed points of a scheme of finite type over a separably
closed field; the weak
Serre property is lem:weil-pbc-constructible-serre of the proper-base-change chapter and the finite-pushforward statement is
[fin4-thm-finite-morphisms-constructible] of the smooth-base-change chapter, both
proved there and quoted above.
1. *Base change:* the integral-normal base produced by a failure of
base change [lem-kun-0f1d]
(Tag [0F1D](https://stacks.math.columbia.edu/tag/0F1D)), the base
change for flat finitely presented morphisms with geometrically reduced
fibres [lem-kun-0eys]
(Tag [0EYS](https://stacks.math.columbia.edu/tag/0EYS)) and the
strict henselization as a limit of smaller-dimensional finite type
algebras [lem-kun-0f0u]
(Tag [0F0U](https://stacks.math.columbia.edu/tag/0F0U)). The
commutation of direct images with field extensions [lem-kun-0f1c] is
*proved* in this chapter from the limit form of smooth base change
[lem-kun-0f09] and the topological invariance of etale cohomology
(thm:weil-pbc-universal-homeomorphism-invariance), with the algebraic
input [lem-kun-fg-separable-smooth] (Tag [07BV](https://stacks.math.columbia.edu/tag/07BV)). The
vanishing at a separably closed field [lem-kun-0ezp], the unbounded
proper base change over $\kunZn$ [lem-kun-0f0c] and the two
projection formulas [lem-kun-0f0g], [lem-kun-0f0f] are
*proved* in this chapter, their Stacks tags being
[0EZP](https://stacks.math.columbia.edu/tag/0EZP),
[0F0C](https://stacks.math.columbia.edu/tag/0F0C),
[0F0G](https://stacks.math.columbia.edu/tag/0F0G) and
[0F0F](https://stacks.math.columbia.edu/tag/0F0F). the proper-base-change chapter
proves proper base change for torsion sheaves
(thm:weil-pbc-finite-torsion,
thm:weil-pbc-bounded-below) and the smooth-base-change chapter the classical
smooth base change ([sbc-thm-smooth-base-change],
[sbc-thm-bounded-below-derived-smooth-base-change]), which are the
instances quoted in the proofs above; the projection formula at all
coefficient stages is the interface
fix-prop-projection-formula of the framework chapter, proved in the
six-functor chapter of this manuscript, which is placed *after*
the present chapter and can therefore not be quoted here.
1. *Algebra:* the algebra statement that a *finitely generated* separable field extension is a filtered colimit of finitely generated smooth subalgebras, [lem-kun-fg-separable-smooth] (Tag [07BV](https://stacks.math.columbia.edu/tag/07BV)). The general separable case, and the algebraic case, are proved in this chapter as [lem-kun-separable-smooth-colimit] and [lem-kun-algebraic-separable-smooth]; the finitely generated statement is the only ingredient of the proof of [lem-kun-0f1c] that is not already available in this manuscript.
1. *Cohomological dimension:* the finite-dimensionality
statement [lem-kun-0f10]
(Tags [0F10](https://stacks.math.columbia.edu/tag/0F10),
[0F0P](https://stacks.math.columbia.edu/tag/0F0P)) and the
tensor products with a constant complex [lem-kun-0f12],
[lem-kun-0f0e]
(Tags [0F12](https://stacks.math.columbia.edu/tag/0F12),
[0F0E](https://stacks.math.columbia.edu/tag/0F0E)). The
homological algebra used by the two projection-formula variants is
*proved* in this chapter: the tor-amplitude criterion
[lem-kun-0f1m] follows from the functorial flat replacement
[lem-kun-bounded-flat-replacement], the K-flat criteria
[lem-kun-kflat-criteria], the flatness criterion
[lem-kun-tor-cokernel-flat] and the flat K-flat resolutions
[lem-kun-flat-resolution-existence], itself proved from the
truncation telescope [lem-kun-hocolim-truncations]; likewise the
direct-sum statement [lem-kun-0f11] is proved from the
filtered-colimit theorem
lem:weil-pbc-direct-image-filtered-colimit of the ambient-foundations chapter by a
hypercohomology comparison, so that no homological-algebra statement
of this chapter is imported any more. For
schemes of finite type over a separably closed field the
cohomological-dimension bounds of the Jacobian chapter
(lem:sc-cohomological-dimension) and the finiteness chain of
the constructibility chapter ([sbc-thm-finiteness-finite-type]) give the curve and
proper instances; the general dimension statement above is quoted from
the Stacks project.

The eight imported statements listed above are the residue of the reduction
performed in this chapter. For each of them the Stacks proof reduces to a
development which is not yet part of this manuscript, and the reductions are
recorded above in the source notes: the limit statements
[lem-kun-0ezt] and [lem-kun-descent-limit] need the descent of
finitely presented and etale morphisms along affine limits (Stacks Tags 0EYL
and 0EXJ, with the algebra of finitely presented descent, whose first step is proved in this chapter as [lem-kun-fp-algebra-descent]); the constructible
generation [lem-kun-03sa] needs the finitely presented presentations of
Modules on Sites, Lemma 18.30.7 (Tag 093C) together with the constructibility
of representable sheaves, Lemma 59.73.1 (Tag 03S8); the base-change statements
[lem-kun-0f1d] and [lem-kun-0eys] need the witness diagram of Tag
0F08 with Tag 0F0B, respectively the local factorization of Tag 0EZX with the
section lemma Tag 0EY5; [lem-kun-0f0u] needs the dimension theory of
quasi-finite algebras over a polynomial ring on top of Noether normalization;
and [lem-kun-0f10] needs the Mayer–Vietoris sequences (Tags 0EYK and
0A50) together with the affine bounds of Tags 0F0X and 0F0V. The purely
algebraic input [lem-kun-fg-separable-smooth] needs the theory of
separating transcendence bases and generic smoothness of finitely generated
separable extensions.
No other statement of this chapter is left without proof: the
proved-but-unquoted statements of the blueprint replace the
corresponding Stacks inputs wherever the chapter order allows.
