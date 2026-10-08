+++
id = "rmk-openclosed-universes"
kind = "remark"
title = "Universes"
order = 1000
+++
Schemes live in a universe $u$ and the coefficient category $\mathcal A$ is
large relative to it: $\mathcal A$ has morphisms in $\mathrm{Type}\,(u+1)$
and is concrete over $\mathrm{Type}\,(u+1)$, so that the forgetful functor
reflects isomorphisms and preserves filtered colimits at that universe. The
same concreteness is also what makes the second hypothesis on $\mathcal A$,
namely sheafification of $\mathcal A$-valued presheaves on the small étale
sites (`CategoryTheory.HasSmallSiteSheafify`, carried by every statement
involving $f^*$ or $j_!$), available in Lean: it implies it through Mathlib's
plus construction. The two are not the same hypothesis — sheafification is
the weaker one, and holds for every Grothendieck abelian $\mathcal A$ of size
$u+1$. For $\mathcal A=\mathrm{Mod}_\Lambda$ both are inferred. The geometric points of $\et X$, on the
other hand, have fibres in $\mathrm{Type}\,u$. These two universes do not
meet, and the standard conservativity statement for a family of points is
stated at a single universe.
[lemma-openclosed-point-ulift] is what repairs the mismatch; every
stalk argument in this section is understood to take place after that
repair. The concreteness hypotheses on $\mathcal A$ — those coming from
stalks, as opposed to the sheafification hypothesis carried throughout — are
therefore carried by [prop-openclosed-lowerstar-fully-faithful]. This is
expected rather than a defect: conservativity is a statement about
stalks, and stalks are sets.
