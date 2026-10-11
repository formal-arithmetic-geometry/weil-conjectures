## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleStratificationLocalGluing` states
`AlgebraicGeometry.Scheme.exists_constructible_stratification_finite_etale_of_affine_local`.
Its only proof is `sorry`. No definitions or auxiliary theorems are introduced.

Hypothesis and clause correspondence:

- X is a scheme: `{X : Scheme.{u}}`; X is quasi-compact and quasi-separated:
  `[CompactSpace X] [QuasiSeparatedSpace X]`.
- U is a scheme: `{U : Scheme.{u}}`; U is quasi-compact and quasi-separated:
  `[CompactSpace U] [QuasiSeparatedSpace U]`.
- The specified morphism is `j : U ⟶ X`; its étaleness is `[Etale j]`.
- There exists a finite affine open covering: the premise `hlocal` existentially
  quantifies `n : ℕ` and `W : Fin n → X.Opens`, with
  `∀ a : Fin n, IsAffineOpen (W a)` and
  `(⋃ a : Fin n, (W a : Set X)) = Set.univ`.
- For every chart there exists a finite partition by locally closed subschemes:
  `∀ a : Fin n, ∃ S : LocallyClosedStratification (W a), ...`.
  The recorded dependency's structure extends `Topology.Stratification`, so its
  `stratum`, `isLocallyClosed_stratum`, `iUnion_stratum_eq_univ`, and
  `pairwise_disjoint_stratum` supply exactly the locally closed partition.
  Its `domain`, `immersion`, `isImmersion`, and `range_immersion` supply arbitrary
  scheme structures on the parts, immersed into the chart with those images.
- Constructibility of each local part, in its chart, is
  `∀ b : Fin S.n, Topology.IsConstructible (S.stratum b)`.
- The map from each local stratum to X is
  `S.immersion b ≫ (W a).ι`. Its specified base change of j is exactly
  `pullback.snd j (S.immersion b ≫ (W a).ι)`. The hypothesis requires both
  `IsFinite` and `Etale` of this map for every b. This is U ×_X W_{a,b},
  with target W_{a,b}, rather than a pullback over U or a merely abstract
  finite étale scheme.
- The conclusion existentially quantifies `S : LocallyClosedStratification X`,
  again giving a finite disjoint locally closed partition with scheme representatives.
  It requires `∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)` in X.
- Every global pullback is finite étale: for each i the conclusion requires
  `IsFinite (pullback.snd j (S.immersion i)) ∧
  Etale (pullback.snd j (S.immersion i))`.
- All fibre products use the chosen categorical `pullback`, as requested.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention-only record, with
  no declaration/module. Its instructions are followed: qcqs schemes use the
  topological instances; locally closed constructible subschemes use immersions,
  locally closed images, and Mathlib constructibility. Nothing is privately redefined.
- `def-weil-constructible-subset`: `Topology.IsConstructible`,
  `Mathlib.Topology.Constructible`. Read its Boolean-subalgebra definition and docstring.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. Read their signatures
  and docstrings, including the projection's target.
- Added the already landed node `def-constructible-stratification` to `stmt_deps`:
  `AlgebraicGeometry.Scheme.LocallyClosedStratification`,
  `Sheaf.AlgebraicGeometry.LocallyClosedStratification`. Read this structure and its
  parent `Topology.Stratification` from `WeilConjectures.Topology.Stratification`.
  This is a citation to an existing notion, not a new definition node.
- The statement also cites `def-weil-etale-morphism` and
  `def-weil-pbc-finite-etale-category` in its original text. Read their Mathlib
  matches: `AlgebraicGeometry.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`
  and `MorphismProperty.Over` in `Mathlib.CategoryTheory.MorphismProperty.Comma`.
  Here only the finite étale property of a morphism is needed, rendered by
  `IsFinite ∧ Etale`, as prescribed by the category node's match. Read
  `IsFinite` in `Mathlib.AlgebraicGeometry.Morphisms.Finite` as well.

Edge cases checked before writing:

- Empty X admits an empty covering (n = 0) and an empty global partition.
- A chart can be empty and its partition can have zero parts; `Fin S.n` imposes
  no nonemptiness requirement. Empty parts are also permitted, as in the node.
- Empty U is permitted. No surjectivity of j is imposed.
- Schemes and all stratum representatives have explicit arbitrary universe u;
  Fin n represents every finite family, without a bound on its cardinality.
- No Noetherian, reduced, separated, or affine hypothesis is imposed on X, U,
  or the strata. Constructibility is retained explicitly because local closedness
  alone does not imply it on a general qcqs scheme.
- The global conclusion does not falsely demand that arbitrary scheme structures
  on refined subsets factor through the local subschemes. The docstring follows
  the node's fibre-product replacement argument, including nonreduced cases.

Searches actually made (remote service logs are in `searches.jsonl`):

- `msearch.py leansearch`: "Glue finite constructible locally closed stratifications
  from finite affine open covers with finite etale base changes". Service unavailable
  (Internal Server Error); no claim of a negative search result from this service.
- `msearch.py leanfinder`: "Finite constructible stratification of schemes local on
  a finite affine open cover finite etale morphisms". Eight hits, including
  `Scheme.exists_isOpenCover_and_isAffine`, finite affine subcovers, and
  `of_affine_open_cover`; none states this gluing theorem.
- `msearch.py loogle`: `AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite`.
  One hit, `exists_etale_isCompl_of_quasiFiniteAt`; different statement.
- `msearch.py grep`: `stratifi|constructible.*cover` in Mathlib/AlgebraicGeometry.
  No hits.
- `rg` for `stratification|Stratification|stratified|Stratified` in the project's
  `lean/Sheaf` and the source's `WeilConjectures/AlgebraicGeometry`: existing
  stratification type and constructible-sheaf usages, no matching theorem.
- `rg` for this exact node id throughout `WeilConjectures`: no hits.
- Read upstream declaration mapping `dag/lean_names_upstream.json` and searched
  source `WeilConjectures/ConstructibleSheaf`; its `Scheme.Stratification` includes
  constructibility, while the dependency's recorded `LocallyClosedStratification`
  plus explicit constructibility is the required reusable interface. No duplicate
  definition was written.
- Searched the proposed theorem name in Mathlib, WeilConjectures, lean/Sheaf,
  and the upstream name mapping: no existing declaration.

Source check and node faults:

The local checkout does not contain `literature/stacks-project/etale-cohomology.tex`.
Read the named lemma and its full proof directly from the official source:
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex
(label `lemma-etale-stratified-finite`). It states the qcqs étale stratification
result and reduces the general base to an affine one in its proof. That reduction
is the source of this helper. The node's tag `03S9` is a citation typo: the official
Stacks tag page says it does not exist. The module therefore cites the verified
lemma label and locality reduction, rather than repeating the faulty tag. No
mathematical statement correction is needed, and the node's source field is
preserved. There is no STATEMENT-DISPUTED claim.

Validation: server `scompile.py` returned exit code 0, compiled in 1.8 seconds,
with no errors or warnings. All universes and variables are explicit.

## Second reading by K1

I read the node statement, its source place, and the Lean declaration independently.
The correspondence is exact item by item:

- The base scheme is the explicit `{X U : Scheme.{u}}`; `[CompactSpace X]` and
  `[QuasiSeparatedSpace X]` render that X is quasi-compact and quasi-separated, and
  the corresponding two instances for U render the same hypotheses on U.
- `j : U ⟶ X` is the named morphism and `[Etale j]` is precisely its étaleness.
- The finite affine cover is the existential `∃ n (W : Fin n → X.Opens)`, with
  `∀ a, IsAffineOpen (W a)` and `(⋃ a, (W a : Set X)) = Set.univ`.
- For each chart, `∃ S : LocallyClosedStratification (W a)` supplies a finite
  disjoint locally closed partition together with scheme representatives and
  immersion maps; `∀ b, Topology.IsConstructible (S.stratum b)` adds the required
  constructibility clause. The two map properties are quantified over every
  `b : Fin S.n` and are exactly
  `IsFinite (pullback.snd j (S.immersion b ≫ (W a).ι)) ∧ Etale (...)`, so the
  pullback has target the local stratum as in the node.
- The conclusion is `∃ S : LocallyClosedStratification X`; its constructibility
  clause is quantified over every `i : Fin S.n`, and its final clause requires,
  for every i, both `IsFinite (pullback.snd j (S.immersion i))` and `Etale (...)`.
  Thus all pullbacks are categorical `pullback.snd`, with no replacement by a
  different fibre-product notion.

No hypothesis, object, quantifier, or conclusion clause was missing or stronger.
The existing `LocallyClosedStratification` declaration is the dependency node's
notion (finite topological partition plus scheme immersions and image equality),
while constructibility is explicitly supplied as required by this node. `Etale`
and `IsFinite` are the recorded Mathlib notions and are used directly.

Edge cases checked: `Fin 0` allows the empty cover and empty stratification (with
union equality forcing a nonempty scheme to have a nonempty cover); empty charts,
empty strata, and empty U are not excluded; no surjectivity of j, Noetherian,
reduced, separated, or characteristic assumption is introduced; and the explicit
universe `u` and finite-index types do not discard any case in the node.

Searches were repeated by concept and declaration name in Mathlib, the source
repository, and `lean/Sheaf`, using LeanSearch/LeanFinder/Loogle and `rg`.
No existing theorem states this gluing result, and no duplicate definition was
introduced. The source lemma and locality reduction were checked against the
Stacks source; the node's cited tag is a source citation typo, but this does not
alter the mathematical statement. The module compiled cleanly with
`scompile.py`; no repair to the worker's Lean or node statement was necessary.
