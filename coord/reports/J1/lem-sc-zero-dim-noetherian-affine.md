## Worker report

The module `Sheaf.AlgebraicGeometry.ZeroDimNoetherianAffine` states
`AlgebraicGeometry.Scheme.Modules.isAffine_and_isAmple_tensorUnit_of_dim_le_zero`.
Its only proof is `sorry`; no definitions or additional nodes are needed.

Hypothesis and conclusion correspondence:

- A scheme Y: `(Y : Scheme.{u})`, with the universe explicitly declared.
- Noetherian: `[IsLocallyNoetherian Y] [CompactSpace Y]`. Mathlib's
  `IsNoetherian` class extends exactly these two classes. This spells out both
  dependency notions instead of assuming only a Noetherian underlying space.
- Separated: `[Y.IsSeparated]`, Mathlib's scheme-level separatedness over the
  terminal scheme, equivalently its absolute diagonal is a closed immersion.
  No properness or finite-type hypothesis is imposed.
- Topological Krull dimension at most zero: `(hdim : topologicalKrullDim Y ≤ 0)`.
  This compares elements of `WithBot ℕ∞` and includes the empty scheme.
- Y affine: the first conjunct `IsAffine Y`. Its definition says the canonical
  map `Y → Spec Γ(Y, ⊤)` is an isomorphism, equivalent to being a spectrum.
- The trivial invertible module O_Y ample: the second conjunct
  `IsAmple Y (𝟙_ Y.Modules)`. The tensor unit is the structure sheaf;
  `Scheme.Modules.isInvertible_tensorUnit` supplies its invertibility without
  a new assumption. `IsAmple` is the recorded absolute ampleness predicate,
  including quasi-compactness and positive tensor powers with affine
  nonvanishing loci through every point.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme` (transitively imported).
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`, in
  `Mathlib.AlgebraicGeometry.Noetherian` (direct import).
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`, in
  `Mathlib.Topology.Defs.Filter` (transitive); does not require Hausdorffness.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`, whose recorded
  module is `Mathlib.AlgebraicGeometry.Morphisms.Proper`. Only its separated
  notion is needed; its defining module
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` is imported directly, using
  `AlgebraicGeometry.Scheme.IsSeparated` for the absolute specialization.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`, in
  `Mathlib.Topology.KrullDimension` (direct import).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, in
  `Mathlib.AlgebraicGeometry.Scheme`; the affineness class `IsAffine` in
  `Mathlib.AlgebraicGeometry.AffineScheme` is imported through `Ample`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  and its tensor-unit instance, in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (through `Ample`).
- `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, in
  `Sheaf.AlgebraicGeometry.Ample` (direct import). Its full definition and
  nonvanishing-locus definition were read, not the distinct relative
  `AlgebraicGeometry.IsAmple` in the source repository.

Edge cases: the empty scheme has dimension bottom, satisfying the weak
inequality; it is affine (the spectrum of the zero ring) and ampleness has no
pointwise obligations. The spectrum of a field and a finite disjoint union of
spectra of Artinian local rings satisfy the statement. Nonreduced Artinian
rings are included: there is no reducedness, integrality, field, characteristic,
or nonemptiness assumption. Quasi-compactness is essential for the Noetherian
hypothesis: an infinite discrete union of field spectra is locally Noetherian
but does not meet `[CompactSpace Y]`. The separatedness assumption is retained
exactly as in the node even though this Noetherian discrete case implies it.

Sources: local `literature/stacks-project/properties.tex` is absent on this
machine, so read the primary sources at
https://stacks.math.columbia.edu/tag/0AAX and
https://stacks.math.columbia.edu/tag/0CKV. The former gives discreteness in the
locally Noetherian dimension-zero case; the latter gives affineness in the
separated quasi-compact case. The declaration docstring carries all three
proof steps and all node references. No statement correction or dispute.

Searches (2026-10-11):

- `msearch.py ... leanfinder "A Noetherian separated scheme of topological
  Krull dimension at most zero is affine and its structure sheaf is ample"`:
  eight hits, notably `IsLocallyArtinian.of_topologicalKrullDim_le_zero`;
  none gives both conclusions with this ampleness predicate.
- `msearch.py ... loogle "topologicalKrullDim, IsAffine"`: zero hits;
  service reported unknown identifier `IsAffine`.
- `msearch.py ... leansearch "Noetherian dimension zero scheme is affine
  structure sheaf ample"`: unavailable, Internal Server Error; no result.
- `msearch.py ... grep "topologicalKrullDim|IsAmple|dimension.*zero"
  AlgebraicGeometry`: eleven Mathlib hits, mainly the locally Artinian
  criterion; none matches the whole node.
- `rg` for `topologicalKrullDim|zero_dim|zeroDim|IsAmple` in the source's
  `WeilConjectures/AlgebraicGeometry` and project's `lean/Sheaf/AlgebraicGeometry`:
  source dimension/cohomology results and relative ampleness; project absolute
  ampleness and dimension-at-most-one existence results; no exact theorem.
- `rg -n "lem-sc-zero-dim-noetherian-affine"` over the entire source
  `WeilConjectures`: no hits.
- Full proposed declaration name searched in `dag/lean_names_upstream.json`,
  all Mathlib, all source `WeilConjectures`, and `lean/Sheaf`: no collisions.

The server compile and `deliver2.py --no-push` validate the statement and
record; the independent second reading is left for the second worker.

## Second reading by J1

I independently read the item JSON and the complete delivered Lean module, and opened
all eight statement-dependency nodes and their declarations. The node introduces
one scheme, with three hypotheses and two conclusions. The correspondence is:

- Object: a scheme Y, rendered by `(Y : Scheme.{u})`. PASS: Mathlib's `Scheme`
  extends `LocallyRingedSpace` with local affine charts (`Scheme.lean:42`), the
  notion of `def-pc-scheme`; `u` is explicitly declared and arbitrary.
- Hypothesis: Noetherian Y, rendered by `[IsLocallyNoetherian Y] [CompactSpace Y]`.
  PASS: `Noetherian.lean:57` requires Noetherian section rings on affine opens;
  the recorded cover equivalence of `pqf-def-locnoeth` gives the same local notion.
  `Noetherian.lean:280` defines `IsNoetherian` as precisely these two classes.
  `CompactSpace` (`Topology/Defs/Filter.lean:283`) requires compactness of the
  whole underlying space, without a Hausdorff assumption, as its dependency says.
- Hypothesis: separated Y, rendered by `[Y.IsSeparated]`. PASS: the absolute
  class (`Morphisms/Separated.lean:338`) means separatedness of `terminal.from Y`;
  the morphism class at line 44 means its diagonal is a closed immersion.
  This specializes exactly the separated clause of `def-weil-proper-morphism`;
  properness, finite type and a field base are not implicitly imposed.
- Hypothesis: topological Krull dimension at most zero, rendered by
  `(hdim : topologicalKrullDim Y ≤ 0)`. PASS: `Topology/KrullDimension.lean:39`
  defines it as the order Krull dimension of irreducible closed subsets, in
  `WithBot ℕ∞`, exactly `def-kun-topological-krull-dimension`. It is a weak
  inequality, not equality, so includes dimension bottom for the empty scheme.
- Conclusion: Y affine, rendered by `IsAffine Y`, the first conjunct. PASS:
  `AffineScheme.lean:59` requires that the canonical morphism to the spectrum of
  global sections is an isomorphism, equivalent to the spectrum description in
  `def-pc-scheme` and `def-weil-affine-spectrum` (`Scheme.lean:470`).
- Conclusion: the trivial invertible module O_Y is ample, rendered by
  `IsAmple Y (𝟙_ Y.Modules)`, the second conjunct. PASS: the tensor unit is
  the structure sheaf and `Modules/Invertible.lean:132` supplies its invertibility
  by local trivializations, without an extra hypothesis. I read the recorded
  `Scheme.Modules.IsInvertible` at line 57. I read the entire project `Ample.lean`:
  `Scheme.Modules.IsAmple` is compactness and, for each point x, a positive tensor
  power and a global section whose entire nonvanishing locus is an affine open
  containing x. Its last universal equivalence forces that open to equal X_s;
  it does not merely permit a smaller affine neighbourhood. Thus the quantifiers
  and both conditions agree with `def-weil-pbc-ample-invertible-module`.

Source check: the repository has no Stacks .tex checkout. I fetched the primary
Stacks `properties.tex` into the sandbox's scratchpad and read labels
`lemma-locally-Noetherian-dimension-0`, `lemma-dimension-zero`, and
`definition-ample`, including their proofs and preceding conventions. The same
places are [0AAX](https://stacks.math.columbia.edu/tag/0AAX),
[0CKV](https://stacks.math.columbia.edu/tag/0CKV), and
[01PS](https://stacks.math.columbia.edu/tag/01PS). No field, reducedness,
nonemptiness, characteristic or other standing hypothesis occurs there. 0AAX
supplies discreteness for locally Noetherian dimension-zero schemes; adding the
node's quasi-compactness gives finiteness. 0CKV's final clause gives affineness
under quasi-compactness and separatedness. 01PS gives exactly the ampleness
predicate used. The node's explicit empty case is handled separately from the
sources' dimension-zero cases. No source or node correction is required.

Edge cases: the empty scheme (equivalently Spec of the zero ring) satisfies the
dimension inequality and has vacuous pointwise ampleness obligations; the
compactness condition still holds. Field spectra in any characteristic and
finite unions of spectra of nonreduced Artinian local rings are included.
There is no index set in the signature. The tensor unit can be the zero module
on the empty scheme. Tensor power zero exists in the dependency but ampleness
correctly requires positive n; the proof uses n = 1. Infinite discrete unions
are excluded only by the intended Noetherian/quasi-compact hypothesis. Arbitrary
scheme universes are covered; all binders and `u` are bound, with no independent
test-object universe or additional instance on Y.

Independent searches, with wording different from the first reader:

- LeanFinder via `msearch.py`: `Artinian scheme affine trivial line bundle ample`.
  Eight hits, including locally Artinian affine-section rings, the Artinian
  scheme compactness equivalence, discrete topology and singleton affine opens;
  none states both conclusions with this absolute ampleness predicate.
- Loogle via `msearch.py`: `topologicalKrullDim`. Seven hits, including
  `IsLocallyArtinian.of_topologicalKrullDim_le_zero`; none is this statement.
- LeanSearch via `msearch.py`: `A zero dimensional Noetherian scheme is affine
  and the tensor unit is ample`. Service unavailable (Internal Server Error);
  recorded as unavailable, with no absence verdict inferred from that failure.
- `rg` on all three Lean trees, using `Artinian`, `artinian`, `dim_le_zero`,
  `dim.*zero`, `ample`, `Ample`, and tensor-unit wording. I opened Mathlib's
  `Limits.lean:700`: `[Finite X] [DiscreteTopology X] : IsAffine X` proves only
  affineness under different binders, not this node's combined statement.
  I also opened upstream `Modules/Ample.lean:185`: its `AlgebraicGeometry.IsAmple`
  uses a morphism to Spec of a field and a very ample tensor power (projectivity),
  so cannot substitute for the recorded absolute predicate. Project dimension
  and ampleness modules do not state this combined assertion. The proposed full
  declaration name has no hits in Mathlib, upstream, project Lean or
  `dag/lean_names_upstream.json`. No reusable exact declaration was found.

H5-H9 check: there are no new definitions, new nodes, dependency modules or
private notions. The only theorem has exactly `by sorry` as its proof. Both
module and declaration docstrings carry the source and correct blueprint id.
The proof docstring renders all three node steps: the empty case and
Noetherian finite discreteness, separated affineness, and compactness plus
n = 1 and section 1 for ampleness. Each cited node id is preserved. All lines
are at most 100 characters. The four imports serve Noetherianity, absolute
separatedness, dimension and absolute ampleness respectively. The namespace is
upstream-compatible. The node's `lean.statement` is verbatim the file signature
up to `:=`. No mismatch found; the Lean and node were left unchanged. The only
change in this reading is this independent review appended to the worker report.
