## Worker report

The delivery states `AlgebraicGeometry.Scheme.isIso_phEtale_derivedUnit` in
`Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison`. The statement is unchanged.
The same module supplies the concrete helpers for the geometric morphism that the node
introduces. No new independent notion, new node, or dependency replacement is needed.
All theorem proofs are `sorry`; definition data come from existing constructions.

Source read: `literature/stacks-project/etale-cohomology.tex`, section-ph-etale
(Tag 0DDV), including the construction of epsilon, pi, and a, and
lemma-cohomological-descent-etale-ph (Tag 0DE5), its whole statement and proof.
The tags were checked against `literature/stacks-project/tags/tags`.
No repair note for this item exists in the shared checkout.

Clause-by-clause rendering:

* Any scheme T: `(T : Scheme.{u})`, without separation, finiteness, characteristic,
  noetherian, or nonemptiness assumptions.
* The original small etale site is literally `T.Etale` and `T.smallEtaleTopology`.
* The big ph site is the recorded `Scheme.phSiteModel.{u,w} T` with
  `Scheme.phModelTopology.{u,w} T`. These are the `AsSmall` presentation of `Over T`
  and the topology transported from the recorded Zariski/proper-surjective ph topology.
* The size convention: `u w` are explicit universe variables; coefficients lie in
  `AddCommGrpCat.{max w (u+1)}`. The original etale site retains objects in `u+1`
  and morphisms in `u`. The ph presentation has both in `max w (u+1)`.
  The explicitly bound `HasDerivedCategory.{max (w+1) (u+2)}` instances fix the
  common localization size; standard localizations exist at this size. They do not
  restrict T or its coefficients. Sheafification on the original etale site is
  supplied by the existing essentially-small-site transport theorem, as a named instance.
* The inclusion is actual data: `phEtaleInclusion T = Etale.forget T ⋙ AsSmall.up`.
  It sends each etale T-scheme and each T-map to that same scheme and map, transported
  through the presentation equivalence. Its finite-limit preservation and flatness
  instances are obtained from existing Mathlib constructions.
* The clause that the inclusion induces a geometric morphism is recorded by the
  named continuity theorem `phEtaleInclusion_isContinuous` and the named theorem
  `phEtaleInverse_leftExact`. Both are clauses of this node's specified morphism,
  have `sorry` proofs and complete source/proof docstrings, and are listed in
  `lean.declarations`. No unrecorded independent theorem is introduced.
  `phEtaleGeometricMorphism` fills the recorded `GeometricMorphism` structure with
  Mathlib's actual sheaf pullback, continuous restriction, their canonical adjunction,
  and the named left-exactness proof. Its data are not chosen from a `sorry` existence.
* Abelian inverse/direct images are the same site functor's existing Mathlib
  `sheafPullback` and `sheafPushforwardContinuous` constructions. Their adjunction
  is exactly `sheafAdjunctionContinuous`. This identifies the abelian functors with
  those induced by the displayed set-valued morphism, through the common canonical
  site construction. No arbitrary functor, adjunction, or map is a hypothesis.
* K in D+: `K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat...)`.
  Mathlib's Plus is the full bounded-below subcategory of the derived category;
  its bound may be any integer and there is no bound above.
* Torsion of every cohomology sheaf: `hK : ∀ q : ℤ, (...homologyFunctor ... q).obj K
  |>.IsTorsion`, written with ordinary parentheses in the module. The existing
  `CategoryTheory.Sheaf.IsTorsion` quantifies over a section and a covering sieve,
  then requires each restriction to have finite additive order. This is exactly local
  annihilation by a positive integer, with no common annihilator. It does not assert
  torsion of the whole group of sections over each object.
* The specified ordinary derived unit is
  `(phEtaleAbelianAdjunction.{u,w} T).derivedPlus.unit.app K`.
  `Adjunction.derivedPlus` is the canonical adjunction from exact levelwise inverse
  image to the ordinary bounded-below right-derived direct image. Its source docstring
  and `derivedPlus_unit_app_fac` characterize the unit by the original unit followed
  by the right-derived-functor comparison. Thus it is the actual eta in the node.
* The conclusion is `IsIso` of that morphism. Since Plus is a full subcategory,
  this is the same isomorphism assertion in the ambient derived category.

Dependency declarations opened and used:

* `Sheaf.AlgebraicGeometry.PhSchemeSite`: `Scheme.phTopology`, `phSiteModel`,
  `phModelTopology`, `PhSheaf`; read their complete definitions and docstrings.
* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtaleTopology`;
  also read `Etale.forget`, `Etale.mk`, and finite-limit preservation in Morphisms.Etale.
* `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  the sheaf portion of this dependency remains Mathlib's `Sheaf`, used here.
* `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`, and its
  actual fields `inverse`, `direct`, `adj`, `leftExact`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; also Plus and its cohomology functors from Mathlib.
* The universe-convention node has no mathematical definiendum; explicit levels and
  the recorded presentation play its role.

Existing APIs reused instead of copied:
`Functor.sheafPullback`, `Functor.sheafPushforwardContinuous`,
`Functor.sheafAdjunctionContinuous`, `hasSheafifyEssentiallySmallSite`,
`Adjunction.derivedPlus`, and `CategoryTheory.Sheaf.IsTorsion`.
The last predicate is in the public upstream module
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` and is also
recorded among the declarations of `def-weil-pbc-etale-sheaves`; no new torsion
predicate is defined. The source of each API was read, including the generic
universe and exactness assumptions of `derivedPlus`.

Proof-dependency imports are retained as plain imports:
`RingedSiteKInjectiveResolutionsOfUniverses`, upstream `PlusHomology`, and
`DerivedCategory.AdjointFunctors`. Their declarations and proof docstrings were read.
The enough-injectives leaf is supplied by Mathlib's Grothendieck-category API,
imported explicitly. The proof dependencies with no recorded module in the base
(big/small etale retraction, ph/big-etale acyclicity, derived composition normalization,
and the torsion representative) are described in the five-step proof docstring;
no invented module names are imported.

Edge cases checked mathematically against the source and the signature:

* Empty T is allowed: no nonempty or geometric-point assumptions appear.
* Zero K is allowed, with torsion cohomology trivially, and the canonical unit is
  an isomorphism on the zero object.
* A sheaf placed in any degree and a complex bounded below at a negative degree are
  allowed; Plus does not mean complexes concentrated in nonnegative degrees.
* Complexes unbounded above and torsion sheaves with unbounded orders are allowed.
  For example an infinite disjoint union can have a section whose restrictions have
  unbounded finite orders; `IsTorsion` still permits it.
* No integer n, no invertibility condition, no uniform cohomological bound, and no
  hypothesis of termwise torsion on a chosen representative have been added.
* Independent `w` permits larger coefficient and site-presentation sizes; no equality
  between the small site's object and morphism universes has been imposed.

Searches for an existing statement or canonical ph comparison:

* `msearch.py ... leanfinder` with "The derived adjunction unit from a bounded below
  torsion etale complex to its pullback and derived pushforward on the big ph site
  is an isomorphism": 8 generic sheaf-of-modules adjunction hits, no ph theorem.
* `msearch.py ... leansearch` with "For a scheme the derived adjunction unit from
  torsion etale sheaves to pullback and derived pushforward on the big ph site is
  invertible": 8 generic derived-adjunction and module-adjunction hits, no ph theorem.
* `msearch.py ... loogle` with `Functor.sheafAdjunctionContinuous,
  Adjunction.derivedPlus`: no hits, unknown-identifier parser diagnostic. A follow-up
  query `"ph"` returned 12 irrelevant core name matches (e.g. Char.isAlpha).
* `msearch.py ... grep` with `phTopology|phEtale|etalePh|torsion.*comparison`: 0 hits
  in Mathlib. Direct `rg` for phTopology/phEtale/etalePh/cohomologicalDescent in
  upstream WeilConjectures and shared lean/Sheaf found only the recorded PhSchemeSite.
* Direct `rg` of the item's id in upstream WeilConjectures found nothing.
  The proposed declaration names were also searched in Mathlib, upstream,
  shared lean/Sheaf and dag/lean_names_upstream.json; no collision.
* Broader searches for derived adjunctions and torsion located the reused upstream
  `Adjunction.derivedPlus` and `Sheaf.IsTorsion`. The latter's full definition was
  read to rule out the stronger condition that all section groups are torsion.

Validation: the prescribed `scompile.py` compiled the sandbox and named library
module successfully with no errors or warnings (5.0 s and 5.8 s). No direct compiler
or global build was run. The final source-tag correction is checked again by delivery.
There is no statement dispute or statement correction.

## Second reading by Q135

This is the worker's explicit second pass; the dispatcher's independent maintainer
review remains separate. I reopened the node and the final module and checked the
scheme, both sites, actual inclusion, geometric morphism, abelian functors, D+ input,
local torsion in every degree, and the actual derived unit against each clause above.
The main result has only T, localization-size instances, K, and the stated torsion
hypothesis. Its conclusion concerns the canonical unit, not an existential
isomorphism or an arbitrary comparison arrow.

The first compile exposed site-universe API gaps. The final text retains the
original etale category and the recorded ph presentation; it uses the existing
sheafification transport, named continuity/left-exactness clauses, and canonical
adjunction constructions rather than adding hypotheses about exactness or existence.
A source-tag typo was found on this pass and corrected from 0DDH to 0DDV using the
Stacks tags table. All helper declarations carry this node's source and blueprint id;
all three postponed theorem bodies are `sorry`. No independent notion was duplicated
and no dependency record needed repair.
