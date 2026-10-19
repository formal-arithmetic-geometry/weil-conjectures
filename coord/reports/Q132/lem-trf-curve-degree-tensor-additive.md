## Worker report

The module `Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive` states
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj_of_topologicalKrullDim_le_one`.
Its sole theorem has proof `by sorry`; it introduces no definitions. The item node
changes only in `lean`. No statement correction, new node, or dependency repair is needed.

The source was read in `literature/stacks-project/varieties.tex`, at
`definition-degree-invertible-sheaf` (0AYR) and `lemma-degree-tensor-product` (0AYX).
The latter treats locally free sheaves of constant finite rank; setting both ranks
equal to one gives exactly this node. The theorem docstring includes all four steps
of the node's proof, including coherence, weighted component reduction, the generic
rank-one Euler identity and pullback/tensor comparison, and finite-sum arithmetic.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| A scheme X over k | `{X : Scheme.{u}} [X.Over (Spec (.of k))]` |
| X proper over k | `[IsProper (X ↘ Spec (.of k))]` |
| Topological Krull dimension at most one | `(hdim : topologicalKrullDim X ≤ 1)` |
| Two O_X-modules | `(L M : X.Modules)` |
| Both invertible | `[L.IsInvertible] [M.IsInvertible]` |
| Tensor product over O_X | `L ⊗ M`, the existing monoidal sheaf tensor |
| Degree is chi(F) minus chi(O_X) | `Scheme.Modules.degree k`, unchanged from the recorded dependency |
| Degree of the tensor is the sum | `(L ⊗ M).degree k = L.degree k + M.degree k` |

No smoothness, reducedness, integrality, connectedness, geometric connectedness,
dimension-exactly-one, or field-characteristic assumption occurs. There is one explicitly
declared universe `u`; the field, scheme and its module category use the recorded
degree API's common universe. Enlarging the universe accommodates any pair of sizes.
Both auto-implicit options are disabled.

Dependency declarations read and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, extending `CommRing`
  and `DivisionRing` and hence including nontriviality and nonzero inverses.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. It extends `IsSeparated`,
  `UniversallyClosed`, and `LocallyOfFiniteType`; universal closedness supplies
  quasi-compactness, so this is the specified finite-type properness.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, defined as `Order.krullDim (IrreducibleCloseds X)`
  with codomain `WithBot ℕ∞`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`. Its `exists_isoUnit`
  gives a local isomorphism with the structure module at every point.
- `def-pur-sheaf-tensor-product`: the recorded module
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly imported.
  Its `SheafOfModules.cochainModulesMonoidal` uses the existing localization tensor.
  The scheme specialization is already supplied by the monoidal instance in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` and is the tensor used here.
  The upstream `SheafOfModules.tensorObjIsoSheafification`, read in
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`, identifies this tensor
  with sheafification of the sectionwise presheaf tensor; no tensor is redefined.
- `def-pc-degree-line-bundle`: `AlgebraicGeometry.Scheme.Modules.degree` in
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`. Its body is precisely
  `M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)`.
  It is defined without a smoothness assumption, so its interface is usable as is.

The two Mathlib statement dependencies are publicly available through `EulerChar`;
the field class is also available through these imports. The other statement-dependency
modules are direct public imports. Proof-only imports are
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (recorded canonical pullback),
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
(`invertible_pullback_tensor`), and
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
(`isCoherent_iff_isQuasicoherent_and_isFiniteType`). The latter two current sources
were read with `scompile.py --source`, since the older local checkout lacks them.
The remaining stated proof dependencies are imported transitively: `Spec`,
`IsNoetherianRing`, `IsLocallyNoetherian`, the finite-type/Noetherian Mathlib results,
and `Scheme.Modules.eulerChar` (the latter's full signature and finsum definition
were read in `Cohomology.Defs`). The two proof-only nodes
`lem-trf-degree-weighted-irreducible-components` and
`lem-trf-curve-euler-tensor-generic-rank` have neither a Lean record nor a Mathlib match
at the time of reading, so no import can yet be added for those proof steps. Their
statements are not prerequisites for elaborating this theorem and are preserved in
its proof docstring; no extra hypotheses replace them.

Edge cases checked mathematically before writing:

- Empty X has dimension minus infinity and is admitted by `≤ 1`; all degrees vanish.
  No `Nonempty X` assumption is present.
- On a proper zero-dimensional scheme, an invertible module has the same Euler
  characteristic as the structure module; all three degrees are zero.
- Disconnected schemes use the same constant local rank one on every component.
  Euler characteristics and degrees add across components; connectedness is unnecessary.
- Singular, nonreduced curves and curves with embedded points are admitted. For
  example, on P1 over the dual numbers, viewed over k, the degree of O(d) is 2d;
  the claimed equality respects this multiplicity. No smooth-curve theorem is used
  to narrow the statement.
- Taking either factor to be the unit gives the usual degree-zero identity; negative
  degrees and all field characteristics are admitted.

Searches for existing declarations (all search commands used the prescribed wrapper
with group Q132 and this item):

- LeanFinder: “On a proper scheme of dimension at most one over a field the degree
  of the tensor product of invertible sheaves is the sum of their degrees”, followed
  by “degree of tensor product of line bundles on a proper curve is additive”. The
  returned candidates concern rational-function degree, ring Picard groups,
  Weierstrass ideals, homogeneous localization, simplicial dimensions, and tensor
  ranks at stalks. None states this cohomological degree formula.
- LeanSearch: “On a proper scheme of dimension at most one over a field, degree is
  additive under tensor products of invertible sheaves”. Eight hits; polynomial and
  rational-function degrees, additive pullback/pushforward and properness
  multiplicativity do not match the statement.
- Loogle: `"degree_tensor"` returned zero hits.
- Mathlib grep: `degree.*tensor|tensor.*degree` under `AlgebraicGeometry` returned
  zero hits.
- `rg` with that pattern in the source `WeilConjectures/` and project `lean/Sheaf`
  found the upstream `Modules.degree_tensorObj` in `Curve/RiemannRoch.lean` and
  unrelated tensor/cohomological-degree discussions. Its docstring and signature,
  including enclosing variables at lines 231–232, require
  `SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))`. It therefore does not cover
  this node's possibly nonreduced and zero-dimensional schemes. The more general
  theorem receives a distinct name.
- `grep -rn` for the exact node id in upstream `WeilConjectures/` found no attachment.
  `rg` for the proposed full declaration's final component in Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py Q132 lem-trf-curve-degree-tensor-additive <file>` succeeded
both as `Sheaf.Stage2.Sandbox0` (2.8 s) and as its final library module (2.1 s),
with no errors or warnings. The maximum Lean line length is 87. The only postponed
proof is the named theorem recorded on this node. No statement is disputed.

## Second reading by Q132

This section records the worker's self-check; the dispatcher supplies the independent
maintainer review. No additional agent was started, as instructed by the launcher.
I reread the node and final module side by side: `Field`, scheme-over-k, properness,
the non-strict dimension bound, both invertibility hypotheses, and the single integer
degree equality agree clause by clause as tabulated above. I rechecked the bodies of
`degree` and the existing sheaf tensor construction, rather than introducing substitutes.
The smoothness hypothesis in the older theorem was the only apparent reuse candidate
that failed this comparison; it was not imported as a replacement statement. No mismatch
requiring a node change or a dependency module was found.
