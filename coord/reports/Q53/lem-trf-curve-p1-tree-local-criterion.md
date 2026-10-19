## Worker report

The delivery states `AlgebraicGeometry.curve_p1_tree_local_criterion` with `sorry` and
supplies three missing local definitions, each with its own DAG definition node.
No mathematical statement was corrected and no theorem was proved.

Source read: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
§1.2 (printed p. 2), Lemma 4.4.2 and its local-to-projective reduction (pp. 30–31),
and Appendix B, the definition before Corollary B.2, that corollary and its graph
count, and the marked exceptional-tree definition (pp. 56–58). The PDF was opened
at https://arxiv.org/pdf/0707.3953v3; no local PDF was available. The source's graph
criterion counts one edge for each node. Its proof computes the cycle number as
`e - v + 1`, so the finite connected graph is a tree precisely when `e + 1 = v`.
The node's eight-step proof is preserved, step by step, in the theorem docstring.

Hypotheses and conclusion, clause by clause:

* `k : Type u`, `[Field k]`, `[IsAlgClosed k]` give the algebraically closed field.
  All schemes and the field live in the same arbitrary universe `u`; nothing is
  restricted to a fixed small universe.
* `P' P : MultipointedCurve (Spec (.of k))` are the recorded multipointed curves.
  Their `X`, `D`, `x`, `d`, `i` are respectively curve, marking, structure maps and
  closed inclusion. The structure retains flatness, finite presentation, pure
  relative dimensions one and zero, and allows an empty marking.
* `[IsProper P'.x] [IsProper P.x]` express properness over the given field, while
  `[IsReduced P'.X] [IsReduced P.X]` express reduced underlying schemes.
* `[IsFinite P'.d] [IsFinite P.d]` impose finiteness on both marking schemes.
* `f`, `fD` are the two maps; `hf`, `hfD` make both maps maps over the specified
  base, and `hmark` is exactly the commuting marking square. `[IsProper f]` and
  `[Surjective f]` give the proper surjective curve map.
* `hgenus` uses the signed expression `1 - Scheme.Modules.eulerChar k O_X` on
  each side. Each over-structure is explicitly `⟨P.x⟩` or `⟨P'.x⟩`; `O_X` is
  the actual `SheafOfModules.unit X.ringCatSheaf`. No connectedness of the entire
  curves, and no replacement of arithmetic genus by `dim H¹`, is assumed.
* `x : P.X` with `hx : IsClosed {x}` represents the rational point. This is an
  equivalent encoding: `pointEquivClosedPoint P.x` in Mathlib's
  `AlgebraicGeometry.AlgClosed.Basic` identifies closed points and `k`-points
  for a locally finite type scheme over an algebraically closed field. Properness
  supplies that finite type condition. It changes no mathematical hypothesis.
* `f.fiber x` is the recorded scheme-theoretic fibre over the residue field of
  that point. `residueFieldIsoBase P.x x hx` identifies its field canonically
  with `k`; thus it is the fibre over the corresponding rational point. The map
  to `Spec k` used everywhere is `f.fiberι x ≫ P'.x`, preserving the original
  scalar structure and the complete scheme structure of the fibre.
* `[ConnectedSpace (f.fiber x)]` gives both nonemptiness and connectedness;
  `hpure` is exactly pure dimension one. No reduction is substituted for it.
* `hoff` says the canonical base change of `f` to the open complement of `x`
  is an isomorphism. Its source is the complement of the support of the fibre,
  so this is the stipulated isomorphism on the two complements.
* `hsemi` applies `MultipointedPair.IsSemistableAt` to every actual fibre point,
  through `f.fiberι x`. It uses the recorded `MultipointedPair.ofCurve` and
  global `IsSemistable` on a canonical restricted pair, including its marking.
* `hlength` equates the local marking length of the target at `x` with
  `(Set.range P'.i ∩ Set.range (f.fiberι x)).encard`. The definition takes the
  dimension of the actual marking stalk as a vector space using its canonical
  local scalar map; a sum over marking points over `x` has at most one term.
  The empty marking gives zero. The length is cast to `ℕ∞` for comparison with
  the set cardinality, which is finite under the finite-marking hypotheses.
* The left side of the conclusion is exactly semistability of the target pair
  at `x`, using the same local predicate as the source hypothesis.
* `IsProjectiveLineTree (f.fiberι x ≫ P'.x)` requires reducedness of this very
  fibre, its connectedness, scalar-compatible nodal completions at all closed
  nonsmooth points, and a closed embedding of `ProjectiveLine (Spec k)` onto
  each irreducible component over `k`. Since these embedded components are
  reduced, they are precisely the reduced component subschemes. The definition
  explicitly requires finite component and node sets and the tree edge count.
* For the graph clause, `curveNodes p` is the actual set of closed nonsmooth
  points. For a nodal curve there is one graph edge per such point, including a
  self-node. Connectedness of the curve gives connectedness of its incidence
  multigraph. Finiteness and `encard nodes + 1 = encard components` say precisely
  that this graph has no cycles. This criterion does not simplify parallel
  edges or omit loops. A self-nodal component also cannot be isomorphic to the
  projective line, as required by the separate component clause.
* The final inequality uses
  `Set.range (f.fiberι x) ∩ closure (Set.range (f.fiberι x))ᶜ` for the boundary,
  exactly support intersected with the closure of its complement in `P'.X`.
  The other summand is the same marking intersection as in `hlength`. The
  inequality is in `ℕ∞`, so it enforces actual finiteness and the bound two.
  Over the algebraically closed field all marking, node and boundary points
  under consideration are distinct `k`-points; no scheme length replaces a
  cardinality in these counts.

Recorded dependency declarations read and reused:

* `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
* `Sheaf.AlgebraicGeometry.SemistableMultipointedPair`:
  `MultipointedPair`, `ofCurve`, `IsSemistable`. Its complete definition includes
  multipointedness, etale marking, marking in the smooth locus and geometric nodes.
* `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`, the equality
  of dimensions of all topological irreducible components.
* `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`: `Scheme.Modules.eulerChar`.
* `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace` and its
  `ProjectiveLine` abbreviation with the canonical base map.
* Mathlib `AlgebraicGeometry.Properties`: `IsReduced`;
  `AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`;
  `Morphisms.Proper`: `IsProper`;
  `Morphisms.Finite`: `IsFinite`;
  `Morphisms.UnderlyingMap`: `Surjective`;
  `Morphisms.Smooth`: `Smooth`; `Topology.Irreducible`: `irreducibleComponents`;
  `Topology.Connected.Basic`: `ConnectedSpace`; `FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`; `Algebra.Field.Defs`: `Field`.
* The scalar-compatible node predicate is the existing
  `Orgogozo.IsOrdinaryDoublePoint` and the existing local scalar map is
  `Orgogozo.localScalar`, in `Sheaf.Paper.OrgogozoInductionData`. Its ring is
  `MvPowerSeries (Fin 2) k` modulo `(u*v)`, and its source is the maximal-ideal
  `AdicCompletion` of the actual stalk. The Mathlib completion and power-series
  definitions in the original dependency records were read, not redefined.

The theorem imports the stated proof dependencies
`Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero`,
`Sheaf.TraceFormula.GenusZeroSmoothProperLine`,
`WeilConjectures.AlgebraicGeometry.Regular`,
`Mathlib.RingTheory.Etale.Field` (the Mathlib leaf
`Algebra.Etale.iff_exists_algEquiv_prod`), and
`Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme` without `public`.
The normalization-genus, nodal-subcurve-boundary, normalization-branches,
and ordinary-point-delta-branches nodes have no recorded
Lean modules in the shared DAG; their natural-language proof roles remain in
its docstring. No import cycle is introduced.

Edge cases checked before writing:

* Empty markings produce an empty index type in `localMarkingLength`, hence
  length zero and cardinality zero; the restriction construction also permits
  empty markings. A nonreduced marking of length two is not mistaken for its
  one-point support or for the length-one fibre of its closed immersion.
* The empty fibre is excluded by `ConnectedSpace`, exactly as the node requires.
  Whole source or target connectedness is not added: disjoint components away
  from the fibre are allowed. Signed Euler characteristics handle these cases.
* A single projective line with no nodes has one vertex and zero edges and
  satisfies the tree count. A nodal rational self-loop fails the projective-line
  component condition and the edge count; two parallel nodes joining two
  projective lines give two edges and two vertices, and fail the tree count.
* A cycle of three projective lines likewise fails `e + 1 = v`. A rational chain
  has `e = v - 1` and passes. No choice of a simple graph loses an edge.
* Boundary/marking combinations `(1,0)`, `(1,1)`, `(2,0)` give precisely the
  numerical cases of the source proof. Infinite boundary counts cannot pass
  the bound. The proof derives a nonempty boundary; none is added as a hypothesis.
* All characteristics of algebraically closed fields, including characteristic
  two, are allowed. There is no characteristic restriction in the node model.
* Reducedness appears in the conclusion for the actual scheme-theoretic fibre;
  it is never assumed as an extra hypothesis or obtained by changing the object.

Searches actually run:

* `msearch.py leanfinder`: "Proper contraction of marked curves equal arithmetic
  genera exceptional projective line tree semistable point" returned unrelated
  Weierstrass reduction/nonsingularity results and relative smoothness, no match.
* `msearch.py loogle`: `"ProjectiveLine", "tree"` returned zero hits.
* `msearch.py grep`: `semistable|projective.*tree|incidenceGraph` in
  `Mathlib/AlgebraicGeometry` returned zero hits.
* `msearch.py leansearch`: "Nodal projective line tree incidence multigraph and
  semistability at a marked curve point" returned generic `Graph.Inc` and
  unrelated projective/Weierstrass declarations, no curve criterion.
* For the three new notions, the exact additional LeanFinder, LeanSearch and
  Mathlib grep queries and results are in each new node's `mathlib_searches`.
  Direct `rg` with `IsSemistableAt|localMarkingLength|IsProjectiveLineTree|curveNodes`
  and `restrictCurve` found no existing project or upstream declarations.
* Direct upstream searches for this node id found no declaration. Broader `rg`
  for semistability, arithmetic genus and projective trees in both Lean trees
  found the dependency modules already cited, not the requested statement.
* DAG text search for projective-line trees, local marking length and local
  semistability found theorem nodes using the notions, no definition node.
  `tools/blueprint_refs.py search` for "projective-line tree", "semistable",
  "marking" and "tree" returned zero blueprint matches; `ancestor` identified
  `lem-trf-local-term-locality` as recorded in the three new nodes.

No `STATEMENT-DISPUTED` issue was found. There are no dependency record repairs.
The initial transitive-module compilation failure was resolved by compiling
against the refreshed side overlay; the original dependency interfaces remain
in use. Only the expected `sorry` warning is permitted in the final compilation.

## New nodes

`def-trf-semistable-marked-point` defines canonical open restriction of the curve
and marking in the category over the base, and local semistability through the
existing global predicate. The source is §1.2 and the localization in Lemma 4.4.2.
It fills the local interface missing from the global pair definition without
copying or altering that definition. Its module is
`Sheaf.TraceFormula.SemistableMarkedPoint`.

`def-trf-local-marking-length` defines the target marking's actual local factor
length, with zero for the empty factor. It uses `Orgogozo.localScalar` and
`Module.finrank` of the actual stalk; the finite sum has at most one term. The
source is the marked formulation of §1.2 and Appendix B as made explicit by the
item. Its module is `Sheaf.TraceFormula.LocalMarkingLength`.

`def-trf-projective-line-tree` defines the reduced nodal projective-line tree on
the given scheme, with actual finite node and component sets and the connected
multigraph edge count from Appendix B, Corollary B.2's proof. It also names the
closed nonsmooth point set used in that same definition. It constructs no
arbitrary graph or replacement fibre. Its module is
`Sheaf.TraceFormula.ProjectiveLineTree`.

All three definitions have real data, explicit universes, source docstrings and
logged searches. None has a postponed proof. The DAG and blueprint searches
above found no existing definition node to reuse.

Validation: all four modules were compiled separately through `scompile.py`, including
private-overlay dependency compilation and library-name compilation. The corrected
main theorem and all helper definitions passed without errors or warnings. The final
packet's Mathlib proof-leaf import is also checked by the delivery dry run.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
