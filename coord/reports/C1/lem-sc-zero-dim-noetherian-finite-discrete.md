## Worker report

The module `Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete` states
`AlgebraicGeometry.finite_and_clopen_singletons_of_topologicalKrullDim_le_zero`.
Its only proof is `sorry`; no definition or other theorem is introduced.
The node is copied unchanged except for `lean`; no new nodes, dependency modules,
or statement correction are needed.

Hypothesis and conclusion correspondence:

- “Let Y be a scheme”: `(Y : Scheme.{u})`, using the scheme's existing underlying
  topological space through the coercion to its carrier.
- “Noetherian”: `[IsLocallyNoetherian Y] [CompactSpace Y]`. These are exactly the
  locally Noetherian and quasi-compact conditions cited by the node. Mathlib's
  `AlgebraicGeometry.IsNoetherian` extends precisely these two classes; separate
  binders directly use the dependency declarations without adding assumptions.
- “Underlying topological space has Krull dimension dim Y ≤ 0”:
  `(hdim : topologicalKrullDim Y ≤ 0)`. The dimension takes values in `WithBot ℕ∞`,
  so the bound includes dimension −∞ and does not demand nonemptiness.
- “Finite discrete space”: `Finite Y` and the singleton-open assertion below.
  All singletons being open is equivalent to the discrete topology, since every
  subset is the union of its singletons. No stronger topological condition is used.
- “Every point is closed”: `∀ y : Y, IsClosed ({y} : Set Y) ∧ ...`.
- “Every singleton is open”: the same universal quantifier's
  `... ∧ IsOpen ({y} : Set Y)`.
- “Includes Y = ∅”: no `Nonempty`/`Nontrivial` binder, arbitrary universe `u`;
  the empty carrier is finite and the quantified singleton conditions are vacuous.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib match `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, in `Mathlib.AlgebraicGeometry.Scheme`.
  Read both full declarations/docstrings; only `Scheme` is needed here.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`, from
  `Mathlib.AlgebraicGeometry.Noetherian`. Its every-affine-open ring condition
  is the equivalent Mathlib presentation recorded by the dependency node.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`, from
  `Mathlib.Topology.Defs.Filter` (available through Noetherian). It means compactness
  of the underlying space without a Hausdorff requirement.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`, from
  `Mathlib.Topology.KrullDimension`, the Krull dimension of `IrreducibleCloseds`.

Source checked: https://stacks.math.columbia.edu/tag/0AAX, Lemma 28.10.5.
The local `literature/stacks-project/properties.tex` is absent on this machine, so
I opened the official Stacks page. Its proof gives discreteness for locally
Noetherian dimension-zero schemes; the node's quasi-compact hypothesis makes the
space finite. The empty case is explicitly included by the node. The module's
proof docstring follows all three recorded DAG proof steps, including their
named dependencies and the sober-to-T0 argument; it does not substitute the
Stacks Artinian-ring proof for the recorded topological route.

Edge cases checked before writing: the empty scheme (dimension −∞, finite empty
carrier); Spec k (one closed/open point); Spec(k × k) (two closed/open points);
Spec(k[ε]/ε²) (one point with nilpotents, so reducedness must not be assumed).
An infinite disjoint union of field spectra is locally Noetherian and dimension
zero but not quasi-compact: it explains why the compactness binder is necessary
for finiteness. Spec k[t] shows local Noetherianity and compactness alone do not
force discreteness. There is no separatedness or field hypothesis in the file.

Searches for an existing exact statement and declaration-name collision:

- `msearch.py ... leansearch "Noetherian scheme dimension zero finite discrete"`:
  service unavailable, HTTP 500; no results and no mathematical verdict drawn.
- `msearch.py ... leanfinder "A Noetherian scheme of topological Krull dimension
  at most zero has a finite discrete underlying space"`: 8 hits, including
  `IsLocallyArtinian.of_topologicalKrullDim_le_zero`,
  `IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology`, and
  `IsArtinianScheme.finite`. Read the full Artinian module: none states the
  node's combined conclusion under exactly its hypotheses.
- `msearch.py ... loogle "IsLocallyNoetherian, topologicalKrullDim"`: 0 hits;
  unknown identifier `IsLocallyNoetherian` in that search service.
- `msearch.py ... grep 'finite.*discrete|topologicalKrullDim.*le_zero'
  AlgebraicGeometry`: 16 hits, consisting of the Artinian component results,
  finite-discrete affineness, and statements about morphism fibres; no exact match.
- `rg -n 'finite.*discrete|topologicalKrullDim.*zero|lem-sc-zero-dim-noetherian-finite-discrete'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures lean/Sheaf`: the source has
  `finite_and_discreteTopology_of_isFinite`, which requires a finite morphism
  over a field, and `IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`,
  which concerns a closed subset of a Noetherian T0 space and does not give
  openness. Neither is this node's exact statement. Existing Sheaf modules
  concern finite-over-field closed subschemes or affineness from an already
  finite discrete scheme; no duplicate statement.
- `grep -rn 'lem-sc-zero-dim-noetherian-finite-discrete'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- `rg -n 'finite_and_clopen_singletons_of_topologicalKrullDim_le_zero|[Nn]oetherian.*[Ff]inite.*[Dd]iscrete'
  Mathlib WeilConjectures lean/Sheaf dag/lean_names_upstream.json`: no name collision;
  two unrelated lines in `Topology/NoetherianSpace.lean`.

Validation: `scompile.py C1 lem-sc-zero-dim-noetherian-finite-discrete
<module path>` compiled cleanly on the server in 1.6 s (exit code 0).
Every universe and variable is explicitly bound. No node faults or disputed
statement were found. The independent second reading is left to the dispatcher’s
second worker, as required.

## Second reading by C1

Independent reading of the node copy, the full module, and all four statement
 dependency nodes found no mismatch. No Lean or node field was changed; this
section records the review and the independent searches.

The source was read directly in Stacks `properties.tex`, fetched from the official
Stacks GitHub source into `scratchpad/properties-source.tex`, lines 1197–1228
and 1286–1300. Section Dimension defines scheme dimension as that of the
underlying topological space; there is no ambient base, field, characteristic,
separatedness, or reducedness assumption. Lemma 0AAX assumes local Noetherianity
and dimension zero and concludes a disjoint union of Artinian local spectra;
its proof explicitly gives discreteness. The node specializes to quasi-compact
schemes, giving finiteness by the singleton open cover, and explicitly extends
to the empty scheme. This is consistent with the source and the node's intent.

Object, hypothesis, and conclusion checklist (H3):

- Object Y, an arbitrary scheme: `(Y : Scheme.{u})`. Verdict: exact.
  Read `Scheme` in Mathlib.AlgebraicGeometry.Scheme: it extends
  LocallyRingedSpace with local affine neighbourhoods, and its CoeSort is the
  underlying carrier. `Scheme.Hom` was also read; no morphism is required here.
- Noetherian scheme: `[IsLocallyNoetherian Y] [CompactSpace Y]`. Verdict: exact.
  Read pqf-def-locnoeth's recorded Mathlib class and the affine-cover equivalence
  `isLocallyNoetherian_iff_of_affine_openCover`, including its signature.
  The every-affine-open class is equivalent to the node's affine-cover notion.
  Read `IsNoetherian`: its two parent classes are exactly these two binders.
- Quasi-compact underlying space: `CompactSpace Y`. Verdict: exact.
  Read def-weil-pbc-quasi-compact-scheme and its match in Topology.Defs.Filter:
  its field is compactness of univ, explicitly without a separation condition.
- Dimension bound on the underlying space: `hdim : topologicalKrullDim Y ≤ 0`.
  Verdict: exact. Read def-kun-topological-krull-dimension and the actual
  Mathlib definition: `krullDim (IrreducibleCloseds T) : WithBot ℕ∞`.
  Thus the dimension notion and the bound, including minus infinity, agree.
- Finite underlying space: `Finite Y`. Verdict: exact; no chosen enumeration
  or extra structure is demanded.
- Every point closed: `∀ y : Y, IsClosed ({y} : Set Y)`. Verdict: exact.
- Every singleton open: under the same quantifier,
  `IsOpen ({y} : Set Y)`. Verdict: exact. The full conclusion is
  `Finite Y ∧ ∀ y : Y, IsClosed ({y} : Set Y) ∧ IsOpen ({y} : Set Y)`.
  Open singletons make every subset open by union, so this states discreteness
  without weakening it or adding an extra conclusion.
- Empty scheme included: no Nonempty or Nontrivial binder. Verdict: exact.
  Its dimension is bottom, its carrier is finite, and the singleton clauses
  are vacuous. Arbitrary explicit universe u is bound and is unrestricted.

Edge cases: Spec of a field (any characteristic), Spec(k × k), and
Spec(k[ε]/ε²) all satisfy the intended finite discrete conclusion. Nilpotents
are allowed. Spec of the zero ring is empty and is included. An infinite
coproduct of field spectra lacks compactness and is correctly excluded;
Spec k[t] lacks the dimension bound. There is no index set or n binder to
restrict, and no extra field, reducedness, separation, or finiteness hypothesis.

Independent H4 searches used different wording from the worker:

- LeanFinder: "A quasi compact locally Noetherian scheme with no strict
  specialization chains has finitely many isolated points" returned eight
  results: finite irreducible components, quasi-separatedness, Noetherian
  compactness and equivalence, and Artinian finiteness/discreteness results.
- Loogle: `topologicalKrullDim, Finite` returned zero hits.
- LeanSearch: "A compact locally Noetherian scheme of dimension at most zero
  is a finite set of isolated closed points" returned HTTP 500, recorded as
  unavailable without a mathematical verdict.
- msearch grep: `IsArtinianScheme|clopen_singleton|finite_of.*KrullDim`
  in AlgebraicGeometry returned nine related component/fibre results.
- Direct rg of Mathlib, WeilConjectures, lean/Sheaf, and upstream name records
  checked dimension-zero, isolated/clopen singleton, finite-discrete, and the
  proposed full declaration name. No collision or exact combined statement.

Opened the entire Mathlib Artinian module: dimension bound gives locally
Artinian, its instance gives discrete topology, and Artinian plus compactness
provides finiteness. None of those declarations states this node's whole
conclusion with its hypotheses. Opened upstream
`finite_and_discreteTopology_of_isFinite`: it instead assumes a finite morphism
to the spectrum of a field. Opened upstream
`IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`: it
concerns a closed subset of a Noetherian T0 space and concludes finite closed
points, without openness. Neither can serve as an exact existing declaration.
The nearby Sheaf finite-discrete affineness and finite-over-field results also
have different hypotheses and conclusions. No missing notion, new definition
node, or unusable dependency module was found (H12/H13); no statement correction
or citer review is needed.

H5/H6/H8/H9: the only declaration is the named theorem with proof `sorry`;
there is no definition or proved helper. Both imports are used for the scheme's
Noetherian classes and dimension. Namespace, explicit universe, name, line
lengths, source and blueprint docstrings conform. The declaration docstring
contains all three DAG proof steps, including the sober-to-T0 justification,
the whole-space application of the closed-subset lemma, and complements as
finite unions of closed singletons. The node's lean.statement is verbatim the
file signature up to `:=`.

Validation: second-reader scompile compiled the unchanged module cleanly
in 1.7 seconds (exit 0), with no errors or warnings. No mathematical mismatch
or repair was necessary; only this second-reading section was appended.

## Reviewer fix (R-zdn1132)

The node's conclusion "|Y| is a finite discrete space" is now stated with the
shared notion `DiscreteTopology Y` (one definition per notion, H4/H12), as the
consumer lem-sc-zero-dim-noetherian-affine's landed
`FiniteDiscreteSeparatedAffine` takes `[Finite Y] [DiscreteTopology Y]`. The
conclusion is `Finite Y ∧ DiscreteTopology Y`; the node's elaborating clauses
(every point closed, every singleton open) are `isClosed_discrete` /
`isOpen_discrete`. The declaration is renamed
`AlgebraicGeometry.finite_and_discreteTopology_of_topologicalKrullDim_le_zero`.
Hypotheses unchanged: `[IsLocallyNoetherian Y] [CompactSpace Y]` (neither is
inferable for an arbitrary scheme), `topologicalKrullDim Y ≤ 0` per the cited
def-kun-topological-krull-dimension, no Nonempty binder (empty scheme included).
