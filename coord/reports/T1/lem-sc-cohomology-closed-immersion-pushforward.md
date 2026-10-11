## Worker report

The module states `TopCat.cohomology_closed_immersion_pushforward` for a continuous
map `i : Z ⟶ X` whose underlying map is a closed embedding, an abelian sheaf `F`
on `Z`, and `p : ℕ`. It asserts existence of the cohomology isomorphism between
`H' F p ⊤` and `H' (TopCat.Sheaf.pushforward AddCommGrpCat i).obj F p ⊤`.
`TopCat.Sheaf.pushforward` renders the direct image, whose sections are the
presheaf pushforward and hence are `F(i⁻¹ U)` on each open `U`.

The hypotheses render as follows:

* `i : Z ⟶ X` is a continuous map of topological spaces.
* `hi : Topology.IsClosedEmbedding i` says that `i` is a homeomorphism onto a
  closed subspace, matching the closed immersion hypothesis.
* `F : TopCat.Sheaf AddCommGrpCat Z` is an abelian sheaf on `Z`.
* `p : ℕ` is the nonnegative cohomological degree.

The conclusion uses `CategoryTheory.Sheaf.H'` on the sites
`(Opens Z, Opens.grothendieckTopology Z)` and
`(Opens X, Opens.grothendieckTopology X)`, evaluated at `⊤`; `HasExt.standard`
chooses the Ext implementation used by Mathlib. `Nonempty (A ≅ B)` renders the
claimed natural cohomology comparison at the fixed sheaf and degree.

Dependency declaration used: `def-sc-topological-abelian-cohomology` records
Mathlib's `CategoryTheory.Sheaf.H'` in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.

Edge cases checked: `p = 0` gives the global-sections comparison; the empty
closed subspace is allowed by `IsClosedEmbedding`; and no nonemptiness or
separation assumptions on `Z` or `X` are introduced.

Searches made: the node's recorded LeanSearch query found no closed-immersion
cohomology declaration; its LeanFinder query found only generic sheaf
pushforward and exact-functor primitives; its Mathlib/project grep found no
cohomology comparison theorem. I additionally searched for direct-image and
closed-embedding declarations and used Mathlib's `TopCat.Sheaf.pushforward`.

## Second reading by T1

The node introduces a continuous map `i : Z ⟶ X`, the hypothesis that `i` is a
homeomorphism onto a closed subset, an abelian sheaf `F` on `Z`, and an integer
degree `p >= 0`.  These render respectively as `(i : Z ⟶ X)`,
`(hi : Topology.IsClosedEmbedding i)`, `(F : TopCat.Sheaf AddCommGrpCat Z)`,
and `(p : ℕ)`.  No separation, nonemptiness, Noetherian, or characteristic
hypothesis is present.  The conclusion's direct image is
`TopCat.Sheaf.pushforward AddCommGrpCat i`, and its two cohomology terms are
the recorded Mathlib `CategoryTheory.Sheaf.H'` specialized to `Opens Z` and
`Opens X`, with `HasExt.standard` and argument `⊤`; the Lean conclusion is
exactly `Nonempty (H' F p ⊤ ≅ H' (i_*F) p ⊤)`.

I read Stacks Cohomology Lemma 02UV: it assumes a closed immersion of
topological spaces and an arbitrary abelian sheaf and states
`H^p(Z,F)=H^p(X,i_*F)`.  `Topology.IsClosedEmbedding` is precisely the stated
topological closed-immersion condition, and the pushforward supplies the
section formula `(i_*F)(U)=F(i^{-1}U)`.  The source's comparison is canonical;
the separate citer `lem-sc-closed-pushforward-boundary-naturality` names its
delta-functor comparison when compatibility with connecting maps is needed.
Thus the fixed-object `Nonempty` is the appropriate Lean rendering here and
does not add or remove a hypothesis or cohomology clause.

Edge cases checked: `p = 0` gives the global-sections comparison; `Z = ∅` and
the empty ambient space are allowed; `i = 𝟙 X` is allowed; and there is no
excluded universe case because `Z` and `X` share universe `u` and `p` is any
natural number.

Searches independently rerun: `msearch.py` LeanSearch (service unavailable,
recorded as such), LeanFinder for closed-immersion cohomology (only generic
restriction/pushforward primitives), grep of Mathlib and `WeilConjectures`
(no matching comparison), and direct searches for pushforward and closed
embedding declarations.  `CategoryTheory.Sheaf.H'` is Mathlib's existing
cohomology object, so no duplicate definition was introduced.  The module
compiled cleanly with `lcompile.py`; no statement or source correction was
needed.
