## Worker report

The module states Stacks Project Varieties Tag 09NI, lemma-points-in-affine,
as `AlgebraicGeometry.exists_isAffineOpen_of_affine_source_stalkMap_isIso`.
Its sole theorem has proof `sorry`; no definition is introduced. The accepted
Q100 stage-1 split is preserved. Q100 supplied no Lean record: the previous
worker's unchanged-item rejection was a stage-1/stage-2 handoff error, not a
reason to reopen the split. The live stage-2 queue names this item.

Exact correspondence with the node and the source:

- Schemes and their morphism: `{T X : Scheme.{u}} (f : T ⟶ X)`.
- Component generic points T⁰ and X⁰: Mathlib `genericPoints T` and
  `genericPoints X`, defined as points whose singleton closure belongs to
  `irreducibleComponents`. This is exactly the node's generic-point notion;
  `IsGenericPoint x Z` is `closure {x} = Z`.
- Affine source: `[IsAffine T]`. Mathlib's canonical affinization is an
  isomorphism precisely for schemes isomorphic to a spectrum.
- Quasi-separated target: `[QuasiSeparatedSpace X]`. Mathlib's
  `quasiSeparated_iff_quasiSeparatedSpace` identifies this with the node's
  quasi-compact diagonal of the structure morphism to Spec ℤ.
- Finitely many target generic points: `(hfinite : (genericPoints X).Finite)`.
- Images of source generic points are target generic points:
  `(hgeneric : Set.MapsTo f (genericPoints T) (genericPoints X))`.
- Injectivity of the induced generic-point map:
  `(hinjective : Set.InjOn f (genericPoints T))`, together with `hgeneric`.
- Finitely many selected points: `(m : ℕ) (t : Fin m → T)`. Their images
  x_j are `f (t j)`, with no added distinctness condition.
- The induced local-ring maps are isomorphisms:
  `(hstalk : ∀ j : Fin m, IsIso (f.stalkMap (t j)))`. `Scheme.Hom.stalkMap`
  has source `X.presheaf.stalk (f (t j))` and target `T.presheaf.stalk (t j)`.
  This specifies the actual induced map, rather than an arbitrary ring
  isomorphism between its endpoints.
- A common affine open subscheme: `∃ U : X.Opens, IsAffineOpen U`.
  Mathlib defines `IsAffineOpen U` as `IsAffine U` for the open subscheme.
- It contains every image point: `∀ j : Fin m, f (t j) ∈ U`.

Dependency declarations read in their source files and imported publicly:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, `Spec.map`,
  and the canonical `Scheme.Hom.stalkMap`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoints`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (the dependency
  is a Mathlib leaf with an exact mathlib_match, requiring no new lean record).
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, `IsAffineOpen`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`
  and its equivalence with the absolute `QuasiSeparatedSpace` condition.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, the recorded general module-stalk
  dependency. The structure-ring stalks and their induced maps here are the
  existing Mathlib scheme stalks; no second stalk construction is made.

The available proof-dependency modules are imported privately. Four Q100
proof dependencies still have no Lean record or Mathlib match, so there is
no module to import for them: lem-trf-qcqs-relative-finite-presentation-approximation,
lem-trf-reduced-affine-injective-factor-stalk-comparison,
lem-trf-finite-type-stalk-isomorphism-open-neighbourhood, and
lem-trf-separated-local-isomorphism-generic-injectivity. They are not needed
to state this theorem. Their roles remain explicit in its seven-step proof
docstring and in the unchanged DAG proof.

Edge cases checked before accepting the draft: m = 0 permits the empty
open, which is affine (Spec of the zero ring). An empty source consequently
allows no nonempty selected family and forces no nonemptiness assumption on
the target. An empty target is also allowed. Repeated selected points are
allowed. No reducedness, Noetherianity, separatedness, finite-type condition,
or extra injectivity on all points has been added. For f the identity of an
affine scheme with finitely many generic points, its whole space supplies
the conclusion. All variables and the scheme universe are explicitly bound.
A common universe for two schemes is the existing Scheme category convention;
no auxiliary indexing universe restricts the finite family.

Searches (2026-10-23), through the prescribed msearch.py wrapper:

- LeanFinder: “An affine source with stalk isomorphisms at finitely many
  points mapping injectively on generic points to a quasi-separated scheme
  with finitely many generic points gives a common affine neighbourhood of
  the images”. Eight hits, including `spread_out_of_isGermInjective'`,
  `reduce_to_affine_nbhd`, and `stalkMap_injective_of_isAffine`. These concern
  spreading out or individual affine neighbourhoods and do not state this
  finite-set criterion.
- Loogle: `AlgebraicGeometry.IsAffineOpen, AlgebraicGeometry.Scheme.Hom.stalkMap`.
  Four hits: `IsAffineOpen.stalkMap_injective`, `IsAffineOpen.arrowStalkMapIso`,
  and two formally smooth stalk lemmas. None is the present theorem.
- Mathlib grep: `(affine.*stalk.*[Ii]so|09NI|points.*affine)` in
  AlgebraicGeometry. Hits include the affine stalk-map localization
  comparison and unrelated elliptic-curve point statements; no match.
- LeanSearch: “Affine common open neighbourhood for finitely many points
  under a morphism from an affine scheme injective on generic points inducing
  stalk isomorphisms”. Eight hits, including
  `exists_isAffineOpen_mem_and_subset` and the single-point affine-cover
  statements; none asserts a common neighbourhood for this finite family.
- rg in both project roots `lean/WeilConjectures` and `lean/Sheaf`:
  `(affine.*stalk.*[Ii]so|affine.source.*[Nn]eigh|09NI|exists_isAffineOpen_of_affine_source)`.
  No matching theorem; only unrelated affine stalk comparisons and
  neighbourhood constructions. The exact blueprint id also has no hit in
  either Lean root. The full wrapper outputs are retained in searches.jsonl.

No statement dispute or statement correction. The source's x_r in the
conclusion is its evident indexing typo for the introduced x_1,…,x_m;
the existing DAG already states the intended family correctly.

## Second reading by Q134

A separate second pass compared the full node statement, the final signature,
and the original Stacks source. The five numbered Stacks assumptions match
IsAffine, QuasiSeparatedSpace, hfinite, hgeneric plus hinjective, and hstalk,
respectively. The finite family has no injectivity or nonemptiness restriction.
The conclusion is existence of one affine open containing all images, with no
extra local-isomorphism assertion. The stalk map has the required contravariant
direction and uses the given f. The generic-point set uses maximal irreducible
closures, not all scheme points. The only proof is sorry and its docstring
records all seven accepted proof steps. No mismatch was found and no change
to the accepted split was necessary. This second pass was performed by the
same worker because the dispatcher explicitly prohibits starting other agents.
