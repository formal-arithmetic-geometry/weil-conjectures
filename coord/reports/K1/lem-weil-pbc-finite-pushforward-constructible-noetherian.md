## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian`.
Its sole proof is `sorry`; no new definitions or dependency modules are needed.
The node statement and dependencies are unchanged.

Hypothesis and conclusion correspondence:

- Schemes U and V: `{U V : Scheme.{u}}`, with explicit universe `u`.
- U is Noetherian: `[IsNoetherian U]`, Mathlib's locally Noetherian and compact scheme.
- The morphism h: V → U is finite: `(h : V ⟶ U) [IsFinite h]`, Mathlib's affine
  morphism with finite ring maps over affine opens.
- E is an abelian etale sheaf on V:
  `(E : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- E is constructible: `hE : IsConstructibleEtaleSheafOfSets
  ((sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)`.
  This uses precisely the recorded definition from def-weil-pbc-etale-sheaves:
  a finite constructible locally closed stratification with finite locally constant
  underlying set sheaf on every stratum. Forgetting the abelian group structure only
  expresses the dependency's prescribed set-valued predicate on an abelian sheaf.
- h_*E is constructible on U: the same predicate on the underlying set sheaf of
  `(Etale.lowerStar AddCommGrpCat.{u + 1} h).obj E`, using U.smallEtaleTopology.
  The direct image is the dependency's objectwise base-change pushforward, not a
  derived functor or a different pushforward.

Dependency declarations read and used:

- def-weil-pbc-direct-image: `AlgebraicGeometry.Etale.lowerStar`, module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. Its full declaration and
  objectwise formula were read; `rightDerivedLowerStarPlus` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` was also read
  but is irrelevant to this underived statement and is not imported.
- def-weil-pbc-etale-sheaves: `AlgebraicGeometry.Scheme.IsConstructibleEtaleSheafOfSets`,
  module `Sheaf.AlgebraicGeometry.EtaleSheaves`, together with its definitions of
  locally constant, finite locally constant, and etaleSetPullback. These definitions
  include finiteness of geometric stalks and the recorded stratification.
- def-weil-pbc-scheme-conventions: a convention record, no declaration or module of
  its own; use `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsFinite` from Mathlib.
- `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`;
  `CategoryTheory.sheafCompose` and `CategoryTheory.forget AddCommGrpCat` express
  the underlying set sheaf without making a private constructibility definition.

Edge cases checked before writing: the empty source or target and the zero sheaf
are allowed; finite maps need not be surjective, etale, or flat; neither scheme is
assumed reduced or integral. No separate Noetherian hypothesis is imposed on V
(it follows from finiteness over U), no dimension bound is imposed, and no
coefficient ring or characteristic is fixed. The universe convention is the
recorded etale sheaf definition's Scheme.{u} and AddCommGrpCat.{u+1}; u is arbitrary.

Searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: "finite pushforward preserves constructible abelian etale sheaves on
  Noetherian schemes". Eight hits concern constructible topological images/preimages,
  local Noetherianity, module finite type, or general sheaf composition; no match.
- Loogle: "AlgebraicGeometry.IsFinite, CategoryTheory.Sheaf". Zero hits.
- Mathlib grep: "constructible.*finite|finite.*constructible". Thirteen hits about
  topological constructible subsets and finite presentation; none about sheaf pushforward.
- LeanSearch: "finite direct image of constructible etale abelian sheaf is constructible".
  Service unavailable (Internal Server Error), recorded as unavailable.
- rg in WeilConjectures and lean/Sheaf for finite/constructible combinations and lowerStar:
  found finite-pushforward embeddings and closed-immersion constructibility, no exact
  theorem. The source's IsConstructibleSheaf module convention uses finitely generated
  module stalks and is not substituted for the dependency's finite-set-stalk definition.
- rg of the item id in WeilConjectures: no hits. rg of the proposed declaration name
  in dag/lean_names_upstream.json, WeilConjectures, and lean/Sheaf: no collision.

Source checked: https://stacks.math.columbia.edu/tag/095R, Lemma 59.73.9.
Its finite finitely presented statement implies this Noetherian-base special case,
where a finite morphism is finitely presented. The local blueprint literature file
named by the node is absent from this checkout; the node preserves the blueprint
statement and complete three-step Noetherian-induction proof. That proof is copied
in natural language into the theorem docstring, including all its named proof inputs.
No statement dispute or correction is needed.

Validation: scompile.py compiled the single module on the server in 1.9 seconds,
exit code 0, with no warnings. Delivery dry run is the final mechanical validation.

## Second reading by K1

I independently read the node statement, its Stacks source (Tag 095R, Lemma 59.73.9),
all three statement dependencies, and the Lean module. The source states the result for a
finite and finitely presented morphism and constructible sheaves of sets, abelian groups,
or modules. The node is the abelian-group, Noetherian-target specialization: over a
Noetherian target, a finite morphism is finitely presented, so no hypothesis is lost.

Object and hypothesis correspondence, in node order:

- The Noetherian scheme (U) is rendered by `{U : Scheme.{u}} [IsNoetherian U]`.
  `IsNoetherian` is Mathlib's locally Noetherian plus compact scheme class.
- The finite morphism (h:V\to U) is rendered by `{V : Scheme.{u}} (h : V ⟶ U)
  [IsFinite h]`; `IsFinite` is Mathlib's finite scheme morphism predicate. The
  source's finite-presentation assumption follows in this Noetherian case.
- The constructible abelian etale sheaf (E) is rendered by
  `(E : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})` and
  `hE : IsConstructibleEtaleSheafOfSets ((sheafCompose V.smallEtaleTopology
  (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)`. This is exactly the
  dependency's finite locally constant-on-constructible-strata predicate applied to
  the underlying sheaf of sets; no private constructibility notion is introduced.
- The direct image (h_*E) is rendered by
  `((Etale.lowerStar AddCommGrpCat.{u + 1} h).obj E)`, the dependency declaration's
  objectwise base-change pushforward, and its underlying set sheaf is formed with
  `sheafCompose U.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})`.

The conclusion is exactly the node's single clause:
`IsConstructibleEtaleSheafOfSets` for that underlying direct image on
`U.smallEtaleTopology`; quantifiers and dependency order are unchanged. No mismatch was
found and no Lean or node statement change was needed.

Edge cases were checked explicitly: empty (U) or (V), the zero abelian sheaf, and a
non-surjective finite morphism are all admitted; no reduced, integral, separated,
etale, flat, dimension, characteristic, or coefficient-ring assumption is present.
The universe (u) is arbitrary and the sheaf value universe is exactly `u + 1` as in the
set-valued dependency. The empty index/stratification case is handled by the existential
constructibility definition, and no (n=0) or nonzero-object assumption is imposed.

Searches were rechecked with `msearch.py` (LeanFinder and Loogle queries for finite
pushforward/constructible etale sheaves), `rg` over Mathlib, `WeilConjectures/`, and the
repository's `lean/Sheaf`; no existing declaration states this theorem. The only related
source declaration is the different `IsConstructibleSheaf` module theorem, so it cannot
replace the node's constructible-subset definition. The imported dependency declarations
were opened and their signatures agree with the uses above. The module compiles cleanly
with `scompile.py`; no warnings were emitted.
