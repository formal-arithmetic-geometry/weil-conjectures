+++
id = "def-weil-pbc-tower-preservation"
kind = "definition"
title = "Tower preservation condition"
order = 1353
uses = ["def-weil-pbc-bounded-constructible-tower", "def-weil-pbc-finite-level-amplification"]
+++
For such a cartesian square $\square$, write $\mathrm{TOW}(\square)$ if the
levelwise tower functors of [def-weil-pbc-finite-level-amplification] carry
every uniformly bounded constructible tower to a tower of the same kind,
with local finite-locally-constant models compatible with the amplitude
containments of [def-weil-pbc-finite-level-amplification].

*Source note:* no Stacks Project entry states this predicate: that direct
images and pullbacks of a bounded constructible tower remain one is the
tower-level form of the constructibility and amplitude conditions of Lemma
59.92.2 ([Tag 095U](https://stacks.math.columbia.edu/tag/095U)), Theorem
63.14.5 ([Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)), Definition
61.29.1 ([Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)) and
Proposition 61.29.7 ([Tag 09C7](https://stacks.math.columbia.edu/tag/09C7)),
which are stated for a single complex on a Noetherian scheme; the closest
tower-level entry is Lemma 61.29.2 ([Tag
09C2](https://stacks.math.columbia.edu/tag/09C2)), which bounds the
reduction tower of one constructible object but does not carry it through a
functor. The blueprint adds the preservation predicate
$\mathrm{TOW}(\square)$ together with the local finite-locally-constant
models.
