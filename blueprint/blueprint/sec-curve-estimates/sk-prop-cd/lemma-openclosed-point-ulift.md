+++
id = "lemma-openclosed-point-ulift"
kind = "lemma"
title = "Raising a point a universe"
order = 990
lean = ["AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale", "CategoryTheory.GrothendieckTopology.Point.ulift"]
uses = ["def-kun-separably-closed"]
+++
Let $(\mathcal C,J)$ be a site and let $p$ be a point of it: a stalk functor
$\shv{\mathcal C}\to\mathrm{Type}\,w$ that preserves finite limits and all
colimits. Then composing the fibre functor with the universe-raising
equivalence $\mathrm{Type}\,w\to\mathrm{Type}\,\max(w,w')$ is again a point of
$(\mathcal C,J)$, and its stalks are the old ones up to that equivalence.

Applied to $\et X$: the raised family of geometric points of $\et X$ is a
conservative family of points at the universe of the coefficients. Concretely,
a morphism of sheaves on $\et X$ with values in $\mathcal A$ is an
isomorphism as soon as it is an isomorphism on the stalk at every geometric
point of $X$.

## Proof

Universe raising is an equivalence of categories which preserves and reflects
all limits and colimits, so composing with it preserves every property in the
definition of a point. The stalk functors of the raised point are the old
ones followed by an equivalence, hence detect exactly the same
isomorphisms.

For the second statement, conservativity of a family of points is checked
against a covering-sieve criterion: a family is conservative as soon as every
sieve $S$ on an object $V$ whose associated subobject of the sheaf represented
by $V$ has full stalk at every point of the family is a covering sieve. That
criterion mentions no fibre universe, so the proof of
conservativity for the geometric points of $\et X$ at the universe of schemes
transcribes verbatim to the raised family. What is used about $\et X$ is
that for a scheme $V$ étale over $X$ and a point $v\in V$ there is a
geometric point of $X$ through which $v$ is visible; this is the existence of
enough geometric points on the small étale site.
