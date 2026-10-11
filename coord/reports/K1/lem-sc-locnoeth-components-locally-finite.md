## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite` states
`AlgebraicGeometry.exists_open_finite_irreducibleComponents`. Its only theorem has proof
`sorry`; it introduces no definitions. The copied node changes only its `lean` field.

Hypothesis and conclusion correspondence:

- “Let X be a scheme”: `(X : Scheme.{u})`, with `universe u` explicit and unrestricted.
- “Locally Noetherian”: `[IsLocallyNoetherian X]`, the recorded declaration of
  `pqf-def-locnoeth`. No global Noetherian or quasi-compact hypothesis is imposed.
- “Every point x in X”: `(x : X)` is an arbitrary point of the underlying space.
- “Has an open neighbourhood U”: `∃ U : X.Opens, x ∈ U ∧ ...`. The bundled open carries
  openness, and membership makes it a neighbourhood of this same point.
- “Only finitely many irreducible components of X meet U”:
  `{Z : Set X | Z ∈ irreducibleComponents X ∧ (Z ∩ (U : Set X)).Nonempty}.Finite`.
  Membership selects exactly the components of X, intersection nonemptiness says they
  meet U, and `Set.Finite` counts the selected components, not points or components of U.
- “The family is locally finite”: the preceding pointwise open-neighbourhood clause is
  exactly the node's explicit meaning. No separate local-finiteness predicate is defined.

Dependencies read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (lines 56–59). Its every-affine-open formulation
  agrees with the node's affine-cover formulation by the recorded
  `isLocallyNoetherian_of_affine_cover` (103–105),
  `isLocallyNoetherian_iff_of_iSup_eq_top` (124–128), and
  `isLocallyNoetherian_iff_of_affine_openCover` (131–135). Read these signatures and
  docstrings. The class is usable directly, without a dependency module.
- `def-weil-irreducible-components` is a Mathlib leaf with `mathlib_match` declaration
  `irreducibleComponents` in `Mathlib.Topology.Irreducible` (107–108), imported transitively
  by `Mathlib.AlgebraicGeometry.Noetherian`. Its definition is `{s | Maximal IsIrreducible s}`.
  Read its docstring, `IsIrreducible` (52–53), and the closed-cover equivalence
  `isPreirreducible_iff_isClosed_union_isClosed` (301–304), verifying the same notion.

Source checked: the local literature copy of `topology.tex` is absent on this machine.
Read https://stacks.math.columbia.edu/tag/0052 (Lemma 5.9.2), especially assertion (2)
on finiteness of components of a Noetherian space. The node applies this to affine
Noetherian neighbourhoods; its component-restriction injection supplies the passage back
to X. The theorem docstring reproduces every node proof step, naming each supporting node.

Edge cases checked before writing:

- Empty scheme: there is no point x, so the universal statement is vacuous, as intended.
- An irreducible scheme: there is one component; no extra nonemptiness assumption is needed.
- An infinite disjoint union of Noetherian affine schemes: neighbourhoods may meet only one
  component while the total component set is infinite. The signature requires only local
  finiteness and does not accidentally assert global finiteness.
- Intersecting components: all components meeting U are counted, including those that meet
  away from x; merely counting components containing x would be weaker and is not used.
- No restriction on dimension, characteristic, separatedness, or universe is introduced.

Searches actually run via `/home/ubuntu/weil-launcher/msearch.py K1
lem-sc-locnoeth-components-locally-finite`:

- leanfinder, “The irreducible components of a locally Noetherian scheme are locally finite”:
  eight hits, including `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`,
  `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`, and the locally Noetherian
  class; none states local finiteness under only the locally Noetherian hypothesis.
- loogle, `LocallyFinite, irreducibleComponents`: zero hits.
- grep, `LocallyFinite.*irreducible|irreducible.*LocallyFinite|locallyFinite.*irreducible|irreducible.*locallyFinite`:
  zero hits in Mathlib.
- leansearch, the same plain-language query as leanfinder: unavailable, Internal Server
  Error. This is not recorded as a negative mathematical search result.

Direct source searches:

- `rg -n 'locallyFinite|LocallyFinite|irreducibleComponents'` in the source and project's
  AlgebraicGeometry directories: component finiteness uses, component bijections, generic
  stalks, and group-scheme local arguments; no exact theorem.
- `grep -rn 'lem-sc-locnoeth-components-locally-finite'` over source `WeilConjectures`: no hits.
- `rg` over all source `WeilConjectures` and project `lean/Sheaf` for `LocallyFinite`,
  `locallyFinite`, and local-finiteness/component wording: unrelated adic locally finite
  functions and local finiteness of partitions of unity; no exact component theorem.
- `rg` for `exists_open_finite_irreducibleComponents` in Mathlib, source `WeilConjectures`,
  `dag/lean_names_upstream.json`, and project `lean/Sheaf`: no hits, so the name is fresh.
- Read Mathlib `Topology/LocallyFinite.lean:29–30`: it uses arbitrary neighbourhoods and
  finite sets of indices. The explicit open-neighbourhood clause in this delivery renders
  the node's own expanded statement without defining a duplicate notion.

Validation: `scompile.py K1 lem-sc-locnoeth-components-locally-finite <module>` compiled
cleanly on the server (1.6 seconds, exit code 0), with no warnings. Delivery dry run follows.
No statement correction, disputed statement, new nodes, or dependency modules are needed.

## Second reading by K1

I independently read the copied node and the Lean declaration
`AlgebraicGeometry.exists_open_finite_irreducibleComponents` in
`Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite`.
The item-by-item correspondence is:

- The node's scheme object `X` is Lean `(X : Scheme.{u})`; the explicit universe is
  unrestricted and introduces no extra structure.
- The node's locally Noetherian hypothesis `[pqf-def-locnoeth]` is Lean
  `[IsLocallyNoetherian X]`, the recorded Mathlib realization of that notion. No
  quasi-compactness, Noetherian, separatedness, finite type, or field hypothesis is added.
- The node's arbitrary point `x ∈ X` is Lean `(x : X)`.
- The node's open neighbourhood `U` is Lean `∃ U : X.Opens, x ∈ U`; `X.Opens` supplies
  openness and the membership conjunct makes it a neighbourhood of the same point.
- The node's final finiteness clause is Lean
  `{Z : Set X | Z ∈ irreducibleComponents X ∧ (Z ∩ (U : Set X)).Nonempty}.Finite`.
  Thus it quantifies exactly components of `X`, selects precisely those meeting `U`, and
  asserts their set is finite. The quantifier order and all clauses agree with the node.

The definition dependency is the Mathlib `irreducibleComponents` set of maximal
`IsIrreducible` subsets, which is the recorded realization of the node's irreducible
components. The locally Noetherian dependency is Mathlib's
`AlgebraicGeometry.IsLocallyNoetherian`; its affine-open-cover equivalence gives the
source notion. No dependency module or private duplicate was needed.

Edge cases checked: the empty scheme is vacuous because it has no point; an irreducible
scheme and a zero-dimensional scheme require no extra nonemptiness or dimension
hypothesis; infinitely many globally disjoint components are allowed because the claim is
pointwise local; intersecting components are counted whenever they meet `U`; and no
characteristic, separatedness, or universe case is excluded.

Searches were reviewed in the worker report and repeated with `rg`/`msearch.py` over
Mathlib, `WeilConjectures`, and `lean/Sheaf`; no exact local-finiteness theorem or duplicate
statement was found. The Mathlib irreducible-components declaration is the sole existing
notion used. The source is Stacks Tag 0052 (Topology, Lemma 5.9.2), whose affine
Noetherian-neighbourhood argument matches the proof steps in the declaration docstring.

No mismatch was found, so no Lean or node statement change was required. The module
compiled cleanly with `scompile.py`; its only proof is the required `sorry`.
