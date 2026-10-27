## Worker report

The module `Sheaf.AlgebraicGeometry.SubsetMaximalGeneralization` states
`AlgebraicGeometry.Scheme.exists_maximal_generalization_in_subset`, with its proof
postponed by `sorry`. No definition or extra node is introduced. The item node is
unchanged except for its `lean` record.

Clause-by-clause correspondence:

- A scheme U: `(U : Scheme.{u})`; the universe `u` is declared explicitly.
- Quasi-compact: `[CompactSpace U]`, exactly the recorded dependency notion,
  with no separation axiom. Mathlib's class explicitly excludes a Hausdorff requirement.
- Locally Noetherian: `[IsLocallyNoetherian U]`. Together with compactness this is
  precisely Mathlib's `IsNoetherian U`, whose class extends those two classes.
  The recorded affine-cover equivalence justifies the node's cover formulation.
- Every arbitrary subset: `(T : Set U)`. There is no closedness, constructibility,
  finiteness, or stability assumption on T.
- Every point of that subset: `(t : U) (ht : t ∈ T)`.
- A point m in T: `∃ m ∈ T`.
- The point m generalizes t: `t ∈ closure ({m} : Set U)`.
- No proper generalization in T: `∀ s ∈ T, m ∈ closure ({s} : Set U) → s = m`.
  The closure is taken in U, not in a different ambient space. Equality has the
  orientation s = m requested by the node. This quantifier ranges over all T.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` in
  `Mathlib.AlgebraicGeometry.Scheme`, including its locally affine locally ringed
  space definition and `Scheme.Hom` signature.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace` in
  `Mathlib.Topology.Defs.Filter` (compactness of the whole space).
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian` in
  `Mathlib.AlgebraicGeometry.Noetherian`; read also its recorded
  `isLocallyNoetherian_of_affine_cover`, `isLocallyNoetherian_iff_of_iSup_eq_top`,
  `isLocallyNoetherian_iff_of_affine_openCover`,
  `isLocallyNoetherian_of_isOpenImmersion`, and
  `LocallyOfFiniteType.isLocallyNoetherian`.

The already stated proof dependencies are imported non-publicly:

- `lem-weil-pbc-affine-open-stalk-localization`: the Mathlib declarations
  `AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`,
  `IsAffineOpen.isOpenImmersion_fromSpec`, `IsAffineOpen.fromSpec_primeIdealOf`,
  `IsAffineOpen.isLocalization_stalk` in `Mathlib.AlgebraicGeometry.AffineScheme`,
  the open-immersion stalk-map isomorphism instance in
  `Mathlib.AlgebraicGeometry.OpenImmersion`, and `Scheme.Hom.germ_stalkMap`
  in the publicly imported `Mathlib.AlgebraicGeometry.Scheme`.
- `lem-weil-pbc-localization-noetherian`: `IsLocalization.isNoetherianRing`
  in `Mathlib.RingTheory.Localization.Submodule`.
- `lem-weil-pbc-noetherian-local-finite-krull-dimension`: the local Noetherian
  ring `FiniteRingKrullDim` instance in `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`.
- `lem-sc-scheme-stalk-dimension-generalization-chains`:
  `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` in
  `Mathlib.AlgebraicGeometry.Properties`.

The theorem docstring reproduces all four steps of the supplied proof: finite
stalk dimensions, strict decrease on proper generalization, a least dimension
among generalizations of t in T, and the transitivity/minimality contradiction.

Source checked: `literature/stacks-project/properties.tex`,
`lemma-maximal-points`, Tag 0G2R, assertion (b) and its proof. Its undefined T'
in the definition of T_0 is already explicitly resolved as T by the item node;
no new statement correction is necessary.

Edge cases checked before writing: for the empty scheme there is no t; for
T empty the membership hypothesis is impossible. For a singleton T, take m=t;
reflexive closure gives the conclusion. For zero-dimensional or discrete
schemes, m=t works. T may omit generic points of U: maximality is only within
T, so no missing generic point is required to belong to T. A Noetherian scheme
need not have a globally finite dimension; the proof only uses the finite
local dimension at each point. No uniform bound has entered the statement.
No additional structure, universe equality, or nonemptiness assumption is used.

Searches actually run using the prescribed msearch.py (group Q105, this item):

- `leanfinder`: "Every point of an arbitrary subset of a Noetherian scheme has
  a generalization in that subset with no proper generalization in the subset".
  Eight hits: scheme quasi-sobriety, NoetherianSpace, finite irreducible
  components, local Noetherian quasi-separatedness, local Noetherian opens,
  `IsGenericPoint.specializes`, `StableUnderGeneralization`, and the integral
  scheme OrderTop instance. None asserts the arbitrary-subset statement.
- `loogle`: `Specializes, Maximal` returned OK, zero hits.
- Mathlib `grep`: `[Mm]aximal.*[Gg]enerali|[Gg]enerali.*[Mm]aximal|[Ww]ell[Ff]ounded.*[Ss]pecializ`
  returned OK, 14 hits, concerning maximal chains, generalized eigenspaces,
  generic order API comments, and unrelated maximal ideals; no exact match.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `maximal_generalization|subset_maximal|[Mm]aximal.*[Gg]enerali|[Gg]enerali.*[Mm]aximal`.
  This found `IsClosed.exists_maximal_specializes` in
  `WeilConjectures.Mathlib.Topology.KrullDimension`; its complete signature and
  docstring were read. It requires `IsClosed Z`, so cannot replace this theorem
  for arbitrary T. Its finite-set companion has the same closedness limitation.
  The other hits concern unrelated maximal ideals, eigenspaces, or isomorphism opens.
- `rg` on `lean/WeilConjectures` for the item id returned no hits.
- `rg` on Mathlib, both project Lean roots, and `dag/lean_names_upstream.json`
  for `exists_maximal_generalization_in_subset` returned no hits.

The example `Sheaf.CategoryTheory.CompactObject` is now withdrawn locally;
its node points at `WeilConjectures.CategoryTheory.CompactObject`. That actual
module was read for the required module and docstring conventions.

## Second reading by Q105

A separate self-review pass re-read the node and final Lean signature. No
other worker was started, as the dispatch brief forbids starting agents.
The three dependency notions match the actual Scheme, CompactSpace and
IsLocallyNoetherian declarations. Both Noetherian conditions are present.
The binders cover arbitrary T and every t in T. The existential includes
membership of m in T and the closure relation in the correct direction;
the final universal implication rules out precisely proper generalizations
of m in T. No closedness premise from the nearby upstream theorem was
imported into the statement. All variables and the sole universe are
explicitly bound. The four proof steps and every stated proof-dependency
module are present. No mismatch or statement correction was found.

Validation: the module is checked through scompile.py, then deliver2.py
--no-push performs server preflight and compilation before the final delivery.
