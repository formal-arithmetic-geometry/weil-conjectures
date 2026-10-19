## Worker report

This repair replaces the saved packet's five local predicates with a single theorem,
`AlgebraicGeometry.valuation_component_factorization`, in
`lean/Sheaf/TraceFormula/ValuationComponentFactorization.lean`. Its proof is `sorry`.
The theorem now imports and uses the published `EtaModification` and
`Scheme.IsPureDimension`; it introduces no definitions, auxiliary nodes or axioms.

The node's natural-language statement is unchanged. The sandbox node was rebased by
copying the current read-only node and applying only its Lean record and the three
permitted landed statement dependencies: `def-trf-modification`,
`def-weil-pure-dimension`, and `def-pc-scheme-fibre`. These nodes supply the exact
published notions used by the repaired signature. All other node fields are retained.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| V is a valuation subring of K with fraction field K | `(V : ValuationSubring K)`; its `mem_or_inv_mem'` is exactly the valuation condition, and Mathlib supplies `IsFractionRing V K` for the subtype inclusion |
| The prime ideals form a finite chain | `[Finite (PrimeSpectrum V)]` supplies finiteness; comparability follows from the valuation-ring structure, rather than an extra universally satisfied chain hypothesis |
| S = Spec V and eta = Spec K | All four structure maps target `Spec (CommRingCat.of V)`; every generic fibre uses `Spec.map (CommRingCat.ofHom V.toSubring.subtype)` |
| C, X, Y, W are S-schemes | `(C X Y W : Scheme.{u})` with `cC`, `cX`, `cY`, `cW` |
| Each is flat | First conjunct of each of `hC`, `hX`, `hY`, `hW`: `Flat cC`, etc. |
| Each is finitely presented | The next three conjuncts are `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` of its structure map |
| Each is reduced | `IsReduced C`, `IsReduced X`, `IsReduced Y`, `IsReduced W` |
| Each has pure relative dimension one | The final conjunct is `∀ s : Spec (CommRingCat.of V), (cC.fiber s).IsPureDimension 1`, and similarly for the other three schemes |
| All four generic fibres are smooth | `hCη`, `hXη`, `hYη`, `hWη` assert `Smooth (pullback.snd ... canonicalGenericMap)` |
| The four maps have the specified sources and targets | `(f : X ⟶ C) (g : Y ⟶ C) (a : W ⟶ X) (b : W ⟶ Y)` |
| These are S-morphisms | `hfc`, `hgc`, `hac`, `hbc` identify each composite with the corresponding structure map |
| fa = gb | `hfa : a ≫ f = b ≫ g` |
| All four maps are eta-modifications | `hf`, `hg`, `ha`, `hb` use the existing `EtaModification canonicalGenericMap map targetStructureMap` |
| Proper, generically invertible, and invertible between schematically dense opens | The published `EtaModification` is `SchemeModification` together with invertibility of the actual `Over.pullback` map; `SchemeModification` supplies properness and invertibility over an open whose inverse image is also schematically dense |
| Y is eta-normal | `hYn` quantifies every scheme `Z` and map `p : Z ⟶ Y`, with `IsFinite p → EtaModification canonicalGenericMap p cY → IsIso p` |
| For every base point and irreducible component of W_s | `hcontract` quantifies `s` and `Z : Set (cW.fiber s)` with `Z ∈ irreducibleComponents (cW.fiber s)` |
| Contracted by b_s implies contracted by a_s | `Set.Subsingleton` of the image under `w ↦ b (cW.fiberι s w)` implies the analogous assertion for `a` |
| A unique C-morphism h with hb = a | `∃! h : Y ⟶ X, b ≫ h = a ∧ h ≫ f = g` |

In the contraction clause the image is viewed in Y or X through the corresponding
fibre inclusion. This is exactly point contraction on the scheme-theoretic fibre:
Mathlib's `Scheme.Hom.fiberHomeo` and the `IsPreimmersion` instance on `fiberι`
identify it with the topological fibre, so the target fibre inclusion is injective.
The image of an irreducible component is nonempty; hence `Set.Subsingleton` means
one point here, and does not weaken contraction to allow an empty component.
The equation `h ≫ f = g` expresses the C-morphism condition; together with the
existing base compatibility it also makes h an S-morphism.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the dependency also records
  `IsSepClosure`, but no choice of separable closure is needed in this statement).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (with the node's explicit finite
  presentation comparison requiring quasi-compactness and quasi-separatedness).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, used
  by the imported modification definition.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, used by the imported
  pure-dimension definition.
- `Sheaf.TraceFormula.Modification`: `AlgebraicGeometry.SchemeModification` and
  `AlgebraicGeometry.EtaModification`; the latter uses the actual generic pullback.
- `Sheaf.TraceFormula.SchematicallyDenseOpen`:
  `AlgebraicGeometry.SchematicallyDenseOpen`, read in full and reused transitively
  through the modification module; its restriction on every open is injective.
- `Sheaf.AlgebraicGeometry.PureDimension`:
  `AlgebraicGeometry.Scheme.IsPureDimension`, read in full.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, and `fiberHomeo`, read in full.
- Mathlib's `Field`, `ValuationSubring`, and its `IsFractionRing` instance provide
  the field, embedded valuation ring, and canonical fraction-field map.

The already stated proof dependencies are imported without `public`, except those
already needed for the statement. The current node
`lem-trf-proper-curve-image-positive-fibre-component` has neither a Lean record
nor a Mathlib match, so it has no module to import yet. No private theorem is
substituted for that future proof input. The docstring follows all ten current
DAG proof steps, including ideal-theoretic closure, proper surjectivity, the
field-level component argument, finiteness, eta-normality, and uniqueness.

Source check: the local Temkin PDF is absent, but the author's
[PDF](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf) was opened
and Proposition 4.2.3 on printed p. 27, its graph proof, and Proposition 3.5.2
on printed p. 20 were read. The latter defines eta-normality by finite
eta-modifications. The DAG deliberately uses the common-model version with this
property in place of normality; the signature follows that unchanged DAG
statement. No claim is made that this common-model signature is the literal
wording of Proposition 4.2.3.

Searches for an existing theorem and notions:

- `msearch.py ... leanfinder "proper birational modifications of relative curves
  factor by inclusion of contracted fibre components"`: eight hits, including
  normalization maps and rational-map representatives; none asserts this global
  component criterion.
- `msearch.py ... loogle '"AlgebraicGeometry.EtaModification"'`: zero hits in
  the remote search index. This does not override the positive project-source
  search: the published canonical declaration was found and used.
- `msearch.py ... grep 'component.?factor|contracted.*component|eta.?normal'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `WeilConjectures`, `lean/Sheaf/TraceFormula` and
  `lean/Sheaf/AlgebraicGeometry` for `component.?factor`,
  `contracted.*component`, the theorem name and the blueprint id found only
  unrelated evaluation-component factorization and contracted-component comments;
  no existing declaration of this theorem.
- Project searches for `EtaModification`, `SchematicallyDenseOpen` and
  `IsPureDimension` found the published definition modules listed above.
  The already published `IsEtaNormal` interface in
  `Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal` was also read: it
  quantifies finite generic modifications using the integral base's function field.
  Here the same condition is expanded inline using the specified K and the
  canonical `EtaModification`; no competing named eta-normality predicate is added.
- The added dependency nodes were read in full for their statements and Lean
  records. No new definition search or new node is necessary.

Edge cases checked: V = K (one prime and identity generic map); empty schemes and
empty fibres (pure dimension is componentwise and vacuous for an empty fibre);
a fibre with both a one-dimensional and an isolated zero-dimensional component
(excluded by pure dimension); a special fibre component contained in a larger
irreducible subset of W (still quantified as a component of W_s); disconnected
and reducible curves; nonseparated curves; and positive characteristic without
assuming K perfect. No Noetherian, proper-over-S, nonempty, integral-curve or
characteristic-zero restriction is added. All universes and variables are bound,
and both automatic-implicit options are explicitly disabled.

## Second reading by Q09

The independent reading at returned immutable head `e909afd02bdc` is preserved in
`/home/ubuntu/weil-launcher-nt/reviews-stage2/Q09__lem-trf-valuation-component-factorization__e909afd02bdc/review.md`.
It found H4 (duplicate schematic-density and eta-modification notions) and H11/H1
(the earlier report did not contain a substantive second-reading record).
The earlier independent reading at `3b588b21e2fa` also supplied a canonical
`EtaModification` interface fix. I reopened those actual reviews, the current
node, every statement dependency, the published notion modules and the entire
repaired file, and performed the following separate clause check. This is an
explicit repair self-check; it does not claim that a new agent independently
reviewed this revised signature. The dispatcher instruction forbids starting
another agent, and the maintainer independently reviews the delivered head.

The field clause now binds the actual subring V of K, not an abstract ring plus
an arbitrary map `iη`. Mathlib's fraction-field instance supplies exactly the
inclusion, and finite prime spectrum together with the valuation condition is
exactly a finite chain. Each of the four curve clauses was checked separately:
flatness, local finite presentation, quasi-compactness, quasi-separatedness,
reducedness and componentwise fibre dimension one are present in `hC`, `hX`,
`hY`, `hW`. Each of the four smooth generic-fibre clauses uses that same canonical
inclusion. Every map has the correct direction; `hfc`, `hgc`, `hac`, `hbc` give
its base compatibility; `hfa` gives the common C-map. All four modification
hypotheses, including those on f and g, are now present. The eta-normal clause
quantifies arbitrary finite eta-modifications, not just reduced or flat sources.
The contraction clause ranges over components of W_s itself. The unique witness
is a map from Y to X satisfying both the factorization and C-linearity equations.
The table above records the exact Lean for every clause of this check.

Mismatches found and repaired, rather than merely acknowledged:

1. H4: removed all five local definitions (`SchematicallyDense`, the duplicate
   `EtaModification`, `EtaNormal`, `ReducedSCurve`, `ContractsComponents`).
   Imported the published modification and pure-dimension definitions; the two
   remaining hypothesis descriptions are written directly in the theorem.
2. The saved signature omitted the eta-modification hypotheses on f and g;
   added `hf` and `hg`, as required by the unchanged node.
3. The saved curve predicate supplied only local finite presentation;
   added quasi-compactness and quasi-separatedness to render finite presentation.
4. Total fibre dimension one did not imply pure dimension one and excluded empty
   fibres; replaced it by the published componentwise `IsPureDimension`.
5. The saved maximality test ranged over irreducible subsets of W, not of W_s;
   replaced it by membership in `irreducibleComponents (cW.fiber s)`.
6. The unconstrained `iη` could be a different spectrum map; replaced it throughout
   by the subtype inclusion's spectrum map. Removed the redundant chain hypothesis
   by using the actual Mathlib valuation subring with finite prime spectrum.
7. H11/H1: replaced the obsolete packet-shape-only repair report with this actual
   clause check, search results, edge-case checks, provenance and correction list.

The edge checks above were repeated against the final signature, especially the
empty-fibre, mixed-dimension and vertical-component cases. None requires a node
statement correction or a new definition node. No STATEMENT-DISPUTED issue remains.

## Validation

The saved packet first passed `deliver2.py --no-push` as requested (temporary
commit `074d961013`), establishing its mechanical baseline. The mathematical
repairs above are substantive changes from returned head `e909afd02bdc` and that
saved packet. The repaired complete module passed the prescribed `scompile.py`
check in both the sandbox and library overlay, with no errors or warnings
(library compile: 27.0 seconds). The exact node signature was compared with the
file, all Lean lines are within 100 characters, there is exactly one `sorry`, and
only `lean` and the three added `stmt_deps` differ from the current base node.
