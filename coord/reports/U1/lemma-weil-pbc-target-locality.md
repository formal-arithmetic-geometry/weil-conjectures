## Worker report

The module `Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality` states all of
lemma-weil-pbc-target-locality in two named theorems, both with `sorry` proofs:
`AlgebraicGeometry.Etale.derivedBaseChange_target_locality` (a) and
`AlgebraicGeometry.Etale.hasTorsionAbelianBaseChange_of_etale_cover` (b).
No definitions, extra nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes and proper f: `{X Y : Scheme.{u}}`, `(f : X ⟶ Y)`, `[IsProper f]`.
  Part (a) also binds `X' Y'`, `g`, `f'`, `g'`, and `sq : IsPullback g' f' f g`.
- Arbitrary etale covering: `I : Type w`, `V : I → Scheme.{u}`,
  `j : ∀ i, V i ⟶ Y`, `[∀ i, AlgebraicGeometry.Etale (j i)]`, and
  `_hcover : ∀ y : Y, ∃ (i : I) (v : V i), (j i).base v = y`.
  This is pointwise joint surjectivity, with no finiteness or nonemptiness imposed.
- X_i and its projections: `Xi`, `fi`, `jXi`, and
  `_sqj : ∀ i, IsPullback (jXi i) (fi i) f (j i)`.
- Y'_i and its projections: `Yi'`, `k`, `gi`, and
  `_sqY : ∀ i, IsPullback (k i) (gi i) g (j i)`.
- X'_i and its projections: `Xi'`, `kXi`, `fi'`, and
  `_sqk : ∀ i, IsPullback (kXi i) (fi' i) f' (k i)`.
- Induced g'_i: `gi'`, with its X-component fixed by
  `_hcomponent : ∀ i, gi' i ≫ jXi i = kXi i ≫ g'`, and its V_i-component
  fixed by `sqᵢ : ∀ i, CommSq (gi' i) (fi' i) (fi i) (gi i)`.
  The latter's equality is `gi' i ≫ fi i = fi' i ≫ gi i`.
  These are the two component equations in the node, not independent additional
  geometric assumptions: existence follows from `_sqj` and the other commuting faces,
  and uniqueness follows from the fibre-product universal property. Similarly the
  three IsPullback witnesses express precisely the constructions in the node.
  The statement works for any chosen fibre products; it specializes to `pullback`
  with `pullback.fst`/`pullback.snd` and the unique induced map. `IsPullback` gives the
  canonical unique identification with the chosen `pullback`, compatible with both
  projections, so it retains the identification data of the cartesian-square node.
- F: `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`. It is arbitrary in (a),
  with no torsion hypothesis. `DerivedCategory.Plus.singleFunctor ... 0` places it
  in degree zero.
- Cartesian localized square: the first conjunct in (a) is
  `∀ i, IsPullback (gi' i) (fi' i) (fi i) (gi i)`.
- Individual equivalence: the second conjunct says `IsIso` of the image under
  `(upperStar AddCommGrpCat (k i)).mapDerivedCategoryPlus.map` of the original
  exchange component iff `IsIso` of the localized exchange component.
  The latter is evaluated at the degree-zero complex of
  `(upperStar AddCommGrpCat (jXi i)).obj F`, precisely j_X,i^{-1} F.
- Global equivalence: the third conjunct in (a) says `IsIso` of the original
  exchange component iff `∀ i, IsIso` of the same localized components.
  Both assertions use the specified `derivedBaseChangeMapPlus`, not an arbitrary
  isomorphism between its source and target. Its codomain is the bounded below
  derived category of abelian sheaves on `Yi' i`, respectively on `Y'`.
- Properness in (b): the first conjunct is `∀ i, IsProper (fi i)`.
- PBC descent in (b): the second conjunct is
  `(∀ i, HasTorsionAbelianBaseChange (fi i)) → HasTorsionAbelianBaseChange f`.
  The predicate quantifies over all cartesian squares and torsion abelian sheaves
  in degree zero, exactly as the recorded dependency node prescribes.
  There is no assertion of its converse.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift` signatures read. In the module their
  universal property is expressed with Mathlib `CategoryTheory.IsPullback`.
- `WeilConjectures.SixFunctors.BaseChange.Square`: `Etale.squareUpperStarIso` read
  with its docstring: it takes `CommSq` and uses only the commutativity equality.
  Hence the existing square encoding is usable directly as `sq.toCommSq` and `sqᵢ i`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to
  `Scheme.smallEtaleTopology` and `AddCommGrpCat.{u + 1}` as its node records.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`, read with its full docstring.
  Applied to the recorded `Etale.upperStar` to give the exact derived inverse image.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, read with full signature and
  docstring; specializes its general coefficient category to abelian groups.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: read in full. Its abelian category
  convention is `DerivedCategory` / `DerivedCategory.Plus` of these same sheaf
  categories; no coefficient-module encoding or torsion-cohomology predicate is
  substituted for abelian sheaves.
- `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange`:
  `AlgebraicGeometry.Etale.HasTorsionAbelianBaseChange`, read in full and used in (b).
  This import supplies the existing exchange and inverse-image declarations.
  The second import supplies properness. No unused imports or private notions.

Edge cases checked before writing:

- An empty index set is allowed. The covering hypothesis then forces Y empty;
  all schemes mapping to Y, and all their base changes, are empty, so the global
  criterion and PBC descent remain correct. No `Nonempty I` is introduced.
- Empty members of a nonempty cover and empty X or Y' are allowed: all the relevant
  categories/maps and pullback universal properties still exist.
- F may be zero, nontorsion, or torsion in (a); no vanishing or torsion assumption
  was inserted. In (b) the torsion condition is internal to the recorded PBC predicate.
- The covering index universe w is arbitrary; this is a covering family, not a
  scheme limit indexed by an independent universe. All schemes and test squares
  remain in u, matching the library's scheme and PBC universes.
- Etale maps need not be open immersions. Both projection component equations
  specify the induced map without demanding that arbitrary sheaves on Xi descend.
  In particular the unasserted converse of (b) has not slipped into the Lean.

Searches for an existing statement (2026-10-11):

- msearch.py `leanfinder`: "Derived proper base change exchange morphism is an
  isomorphism if and only if after an etale covering of the target". Eight hits,
  including stability of etale/local-isomorphism morphisms under base change and
  ring-map etale properties. None states this cohomological exchange criterion.
- msearch.py `loogle`: "AlgebraicGeometry.Etale.derivedBaseChangeMapPlus, IsIso".
  Zero hits; service does not know the project identifier.
- msearch.py `grep`: "HasTorsionAbelianBaseChange|derivedBaseChangeMapPlus|properBaseChange"
  in Mathlib/AlgebraicGeometry. Zero hits.
- msearch.py `leansearch`: "proper base change is etale local on the target".
  UNAVAILABLE: Internal Server Error. No mathematical verdict assigned to this search.
- rg of WeilConjectures and lean/Sheaf for the item id, targetLocality,
  target_locality, and HasTorsionAbelianBaseChange: no existing locality statement;
  existing PBC predicate and its users only. Further conceptual inspection of
  SixFunctors/BaseChange and Etale/BaseChangeTheorems found no matching declaration.
- rg of dag/lean_names_upstream.json, Mathlib, WeilConjectures and lean/Sheaf for
  `derivedBaseChange_target_locality` and
  `hasTorsionAbelianBaseChange_of_etale_cover`: no name collisions.

Sources: the local literature checkout is absent on this machine. Read the official
Stacks pages https://stacks.math.columbia.edu/tag/0EZR,
https://stacks.math.columbia.edu/tag/0D6G and
https://stacks.math.columbia.edu/tag/0A4F. They give the covering-local exchange
criterion, derived localization, and reduction to an affine target respectively.
The detailed six-step proof in the DAG is carried in the two theorem docstrings.
No node fault or disputed statement was found.

Validation: scompile.py compiled the module on the server in 2.0 s, exit 0,
with no warnings. Every universe and variable is explicitly bound.
The independent second reading is left to the second reader.

## Second reading by U1

Independent audit on 2026-10-11; I did not write the statement. Read the repository
node, sandbox module and node copy, and all nine statement-dependency nodes and
recorded declaration signatures. No new nodes, dependency modules or
`statement_change` are present. The node's mathematical statement is sound and
is rendered without a change of meaning.

Object, hypothesis and conclusion checklist (each verdict: matches):

1. Schemes X,Y and proper f: `{X Y : Scheme.{u}}`, `f : X ⟶ Y`,
   `[IsProper f]` in both declarations. Read Mathlib's `IsProper`, extending
   separatedness, universal closedness and locally finite type; universal
   closedness supplies quasi-compactness, hence the node's finite type.
2. Etale covering of Y: `I : Type w`, `V : I → Scheme.{u}`, `j`,
   `[∀ i, AlgebraicGeometry.Etale (j i)]`, and `_hcover`'s pointwise joint
   surjectivity. Read the affine-local etale class in Mathlib. Neither finite
   covering nor open immersions are assumed.
3. X_i with projections f_i and j_X,i: `Xi`, `fi`, `jXi`, `_sqj`.
   `IsPullback (jXi i) (fi i) f (j i)` is the fibre-product universal property,
   not an extra geometric restriction. Read `pullback`, its projections and
   `IsPullback` in Mathlib, including `isoPullback` and its projection equations.
   Thus these witnesses retain exactly the unique projection-compatible chosen
   identification with the recorded fibre product; no private notion is used.
4. In (a), arbitrary g and original cartesian square: `X' Y'`, `g`, `f'`,
   `g'`, `sq : IsPullback g' f' f g`. No properness assumption on f' is added.
   Read `Etale.squareUpperStarIso`: only `CommSq.w` enters its definition, as
   the cartesian-square and exchange nodes specify.
5. Y'_i = Y' ×_Y V_i, with k_i and g_i: `Yi'`, `k`, `gi`, `_sqY`.
   The order `IsPullback (k i) (gi i) g (j i)` has the correct two projections.
6. X'_i = X' ×_{Y'} Y'_i, with k_X,i and f'_i: `Xi'`, `kXi`, `fi'`,
   `_sqk : ∀ i, IsPullback (kXi i) (fi' i) f' (k i)`.
7. Induced g'_i: `gi'`, `_hcomponent`, `sqᵢ`. The first component equation is
   `gi' i ≫ jXi i = kXi i ≫ g'`; `sqᵢ.w` is the second component equation
   `gi' i ≫ fi i = fi' i ≫ gi i`. By `_sqj` these uniquely determine the
   induced map. `sqᵢ` assumes commutativity only, not the cartesianness concluded.
8. Arbitrary abelian sheaf F: `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
   `DerivedCategory.Plus.singleFunctor ... 0` places F in degree zero.
   No torsion condition in (a). Read `DerivedCategories.lean`'s abelian and
   bounded-below conventions and the recorded Mathlib sheaf category.
9. Localized square cartesian: first conjunct of (a),
   `∀ i, IsPullback (gi' i) (fi' i) (fi i) (gi i)`.
10. Individual restriction equivalence: second conjunct of (a), for every i,
    `IsIso` of `mapDerivedCategoryPlus.map` under `upperStar ... (k i)` of
    the original `derivedBaseChangeMapPlus ... sq.toCommSq` component iff
    `IsIso` of `derivedBaseChangeMapPlus ... (sqᵢ i)` at the degree-zero
    sheaf `(upperStar ... (jXi i)).obj F`. Read `mapDerivedCategoryPlus`
    (restriction of the exact induced derived functor) and the full derived
    exchange signature/docstring. These are the specified exchange maps,
    not arbitrary isomorphisms of objects, with codomain on Y'_i as required.
11. Global equivalence: third conjunct of (a), original exchange component
    `IsIso ↔ ∀ i, IsIso` of those same localized components. The parentheses
    keep both iff clauses separate inside the threefold conjunction.
12. Part (b), properness of every f_i: first conjunct
    `∀ i, IsProper (fi i)`. PBC descent: second conjunct
    `(∀ i, HasTorsionAbelianBaseChange (fi i)) → HasTorsionAbelianBaseChange f`.
    Read `TorsionAbelianBaseChange.lean` in full: it quantifies over every
    cartesian test square and torsion abelian sheaf in degree zero, and asks
    invertibility of the recorded specified exchange map. No converse is added.

Sources: the local Stacks checkout is absent. Independently read the official
Stacks pages [0EZR](https://stacks.math.columbia.edu/tag/0EZR),
[0D6G](https://stacks.math.columbia.edu/tag/0D6G), and the first proof paragraph
of [0A4F](https://stacks.math.columbia.edu/tag/0A4F), plus the raw Stacks
`etale-cohomology.tex` block `lemma-base-change-local` and
`sites-cohomology.tex` block `lemma-restrict-direct-image-open` from
https://raw.githubusercontent.com/stacks/stacks-project/master/ .
0EZR has arbitrary schemes and etale coverings; no standing Noetherian,
separated, finite-cover, field or characteristic assumption is needed.
0D6G supplies derived localization, and 0A4F uses target-cover descent.

Edge cases: `I` may be empty (then `_hcover` forces Y empty), or its members
may be empty. Empty X, Y' and their fibre products are included. Zero F and
nontorsion F remain allowed in (a); torsion is only within PBC in (b).
There is no n parameter or positive-degree restriction: degree zero is
explicitly permitted, and the derived isomorphism concerns all cohomology
degrees. No characteristic restriction occurs. The scheme universe u is
arbitrary and matches the dependencies' test-square convention; w is an
arbitrary covering-index universe, not a limit-index universe. No new
smallness or nonemptiness instance is imposed.

Independent searches, with different keywords:

- `msearch.py ... leanfinder` query "restriction to etale covering detects
  invertibility of derived base change natural transformation": eight hits
  about etale ring maps and stability under base change; no matching theorem.
- `msearch.py ... loogle` query `Sheaf.isIso_iff_of_coversTop`: zero hits,
  unknown identifier in that service; no match established by this service.
- `msearch.py ... grep` query `baseChange.*cover|baseChange.*local|coversTop`:
  25 hits in Mathlib, none giving this derived exchange statement.
- Independent `rg` through source SixFunctors and project AlgebraicGeometry
  for covering/locality and base-change words found
  `SmoothBaseChange/Locality.lean`. Opened its declarations:
  `isIso_baseChange_app_of_etale_cover` uses `ModuleCat Λ`, a different cover
  diagram and only a one-way implication; `BaseChangeProperty.of_etale_cover`
  is a degree-q module-sheaf predicate. Neither renders this node's full
  abelian-sheaf conjunction, including individual iff, cartesianness,
  properness and torsion-PBC descent. They may be useful in stage 3 but do
  not justify `existing: true`. No duplicate statement was found.

Mismatch and repair: the node copy's `lean.statement` was a whitespace-flattened
signature, not the signature verbatim. Replaced it with the exact multiline
main declaration signature from the file. The Lean mathematical statement,
module and all other node fields were correct and left unchanged. No hollow
definitions, hidden local notation/instances, unbound universes/variables or
extra proved theorem occur. Both theorem proofs are solely `sorry`; their
source docstrings carry the node's proof steps and dependency IDs.

Validation: `scompile.py U1 lemma-weil-pbc-target-locality` with the absolute
module path compiled on the server in 2.7 s, exit 0, no warnings. The first
relative-path invocation failed to locate the file from the repository cwd;
using its absolute sandbox path resolved this without changing the tool.
