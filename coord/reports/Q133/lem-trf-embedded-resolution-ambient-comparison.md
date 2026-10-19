## Worker report

The delivery states `AlgebraicGeometry.exists_synchronized_embedded_resolution` in
`Sheaf.AlgebraicGeometry.EmbeddedResolutionAmbientComparison`, with `sorry` as its
entire proof. It asserts the existence of a common ordered label type and of a
`SynchronizedEmbeddedResolution` assignment. The assignment is defined, with real
data throughout, in `Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution`. No theorem
other than the item's existence theorem is postponed. The item's informal statement
and proof are unchanged. The statement dependencies gain the new definition node.

Hypotheses and clauses, in the order of the node:

- Work over Q: `EmbeddedResolutionPair.base : P ⟶ Spec (.of (ULift.{u} ℚ))`.
  This is the rational base lifted to the scheme universe, not an extra field or
  algebra assumption. The declaration is polymorphic in the scheme universe `u`.
- Closed immersion and reduced source: the pair has `inclusion`, `closed :
  IsClosedImmersion inclusion`, and `reduced : IsReduced X`.
- Smooth, separated, finite-type ambient scheme: `smooth`, `separated`,
  `finiteType`, and `quasiCompact` concern the same `base` map, with the last two
  being the existing node's conjunction for finite type. There is no hypothesis
  of properness, connectedness, equidimensionality, or a global embedding bound.
  All finite disjoint unions satisfying these same conditions are inputs too.
- One common total order and simultaneous algorithm: the theorem quantifies
  `L : Type (u + 1)` and `order : LinearOrder L`, and then asserts
  `Nonempty (@SynchronizedEmbeddedResolution.{u, u + 1} L order)`. The latter
  structure's `tower` field assigns a tower to every pair. This is an existence
  theorem about actual assignment data; no definition chooses an arbitrary
  object from a postponed mere-existence theorem.
- Finite ordinary tower retaining the stages and centers:
  `LabeledEmbeddedResolutionTower.labels : Finset L`, `ambient`, `intrinsic`,
  and `inclusion` retain the entire diagrams, their structural maps and their
  closed immersions. `initialAmbient`, `initialIntrinsic`, and `initialInclusion`
  identify the empty cut with the original pair. For label `l`, the cut `Iio l`
  is immediately before its stage and `Iic l` is immediately after it.
  `ambientBlowup` and `ambientBlowupMap` identify the actual next map with the
  existing ordinary blowup of `center l`. `strictTransform`,
  `strictTransformMap`, and `strictTransformToSource` identify the next source
  with the existing scheme-theoretic strict transform and both structural maps.
  Thus this does not replace a strict transform with a topological closure.
- Centers contained in the strict transform: `centerToIntrinsic`, `centerClosed`,
  and `centerInclusion` retain their closed immersions and factorization of the
  actual ambient center inclusion. `nonemptyCenter` and `regularCenter` assert
  nonemptiness and regularity for every active label. `nowhereDense` is
  `interior (Set.range (centerToIntrinsic l)) = ∅`, precisely that its closed
  underlying set contains no nonempty open subset. `coherentAmbient` and
  `coherentIntrinsic` use the existing Stacks-coherent module class on the
  actual ideal modules, the latter being the kernel of the center's closed
  immersion in the strict transform. These assert coherent ideals, not only
  coherent structure sheaves or finite generation of unrelated ideals.
- Final regularity and stopping: `finalRegular` refers to the full cut.
  `stopAtRegular` says any cut with regular strict transform contains every
  active label, forbidding subsequent cleanup. `regularInput` and `emptyInput`
  explicitly give `labels = ∅` for regular and empty inputs.
- Distinct labels in prescribed order: a `Finset L` cannot repeat a label; lower
  cuts implement its common total order. `constantAmbient` and
  `constantIntrinsic` assert that transition maps across intervals with no new
  active labels are isomorphisms. After choosing the increasing enumeration of
  the finite label set and deleting these isomorphisms, the diagrams are exactly
  a finite ordinary tower. The comparisons carry this finite order without
  independent renumbering. This presentation also handles a dense or unbounded
  common order; it assumes no well-foundedness of that order.
- Every smooth ambient morphism and its pullback pair:
  `EmbeddedResolutionSmoothMap A B` has an arbitrary smooth `ambient : A.P ⟶
  B.P`, an `intrinsic` map, and the cartesian initial square. Requiring a chosen
  cartesian source is equivalent to using `X ×_P Q` up to its canonical
  isomorphism, and allows direct composition without hard-coded pullback
  associators. There is no constant relative-dimension condition.
- Pullback of the complete tower, with exactly empty centers deleted:
  `LabeledEmbeddedResolutionPullback` gives the two natural transformations,
  their compatibility with `inclusion`, their initial maps, and cartesian
  ambient/intrinsic squares over the initial schemes at every cut. `centers`
  identifies the actual ideal with `.comap` of the original ideal at every
  label. `retainedLabels` is the iff between membership in the pulled-back
  finite label set and membership in the original set with nonempty pulled-back
  center. Therefore no extra labels appear, and exactly empty centers disappear.
  `absentCenter` says the ideal at an absent label is the unit ideal, while the
  no-active-label interval laws give identity stages up to the canonical
  isomorphisms of their diagrams.
- Identity and composition: `SynchronizedEmbeddedResolution.pullbackId` and
  `.pullbackComp` are equations of both actual natural transformations for any
  maps with the indicated underlying identity/composite maps. The formulation
  quantifies over witnesses of smoothness/cartesianness, avoiding dependence
  on a particular proof or on independently chosen pullback presentations.
- Intrinsic ambient comparison: `.intrinsic` takes any initial isomorphism
  `e : A.X ≅ B.X`. Its `iso` is a natural isomorphism of the full strict-transform
  diagrams, `initial` gives its map over the specified initial isomorphism,
  `labels` identifies the active labels exactly, and `centers` identifies the
  intrinsic ideal centers by comap. Taking the identity isomorphism treats two
  embeddings of the same reduced X. Ambient schemes need not be isomorphic.
- Compatibility with isomorphisms of X and transitivity for three embeddings:
  `.intrinsicId` and `.intrinsicComp` are actual natural-isomorphism equations.
  Taking three identity isomorphisms of X gives the requested cocycle; general
  isomorphisms give the transport case. The comparisons remember ideals even
  when an intrinsic blowup is already an isomorphism.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (topological closed embedding and
  surjectivity on stalks).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`
  (all rings of sections reduced).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  `smooth_comp`, `smooth_isStableUnderBaseChange`, and the smooth-to-flat
  instance; no fixed-dimensional predicate is used.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.Separated`, `.FiniteType`,
  and `.QuasiCompact`: `IsProper`, `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact`; the ambient condition uses the separated and finite-type
  clauses of the recorded nodes, not the stronger proper condition.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and
  `.blowupMap`, read at their actual declarations.
- `WeilConjectures.Compactification.StrictTransform`:
  `Scheme.IdealSheafData.strictTransform`, the generic `strictTransformMap`
  and `strictTransformToSource`, with scheme-theoretic-image construction.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme = IsLocallyNoetherian X ∧ IsRegular X`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre`:
  `Scheme.Modules.IsFiniteTypeWithFiniteTypeKernels`, the audited upstream
  Stacks 01BV coherence class. The new tower node records a note explaining why
  this direct class is used for coherent center ideals: the unchanged
  `pqf-def-coherent` record exposes `IsQuasiCoherentFiniteType`, which does not
  expose the finite-type-kernel field.
  Its exact current server declaration and docstring were read using
  `scompile.py --source`, rather than inferred from its name.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules` is the actual kernel ideal module.
  Mathlib's `.comap`, `.subscheme`, `.subschemeι`, and `Scheme.Hom.ker`
  retain actual quasi-coherent ideals and closed subschemes.
- Proof-only imports `WeilConjectures.Blowup.FlatBaseChange` and
  `WeilConjectures.Compactification.StrictTransformBlowup`: current server
  declarations `.blowupFlatBaseChange`, `.blowupFlatBaseChangeIso`, and
  `.exists_isClosedImmersion_blowup_comap` and their source docstrings were
  read with `scompile.py --source`. Other already stated proof dependencies
  are available through the imported smooth/proper modules. The local-invariant
  calculus node has no Lean declaration and consequently no module to import;
  it is the future mathematical input in the theorem's complete proof docstring,
  not an extra hypothesis or an unstated axiom in the signature.

Edge cases checked: empty X in a nonempty ambient scheme; empty ambient scheme;
regular X with any embedding; zero active labels (all maps are isomorphisms);
restriction missing some centers or every center; variable relative dimensions
on disconnected smooth sources; finite disjoint unions of different dimensions;
two ambient embeddings of unequal dimensions; an intrinsic blowup which is an
identity but whose nonempty center ideal must remain recorded; arbitrary, possibly
dense common label orders with only finitely many active labels per input. No
node correction or disputed statement was needed.

Searches: `msearch.py` LeanFinder with the statement in plain words returned
ordinary smoothness, closed immersion and standard-smooth chart declarations,
not an embedded resolution algorithm. Loogle `"blowup"` returned zero hits.
Mathlib grep `desingulari[sz]|Bierstone|embedded.*resolution` returned zero hits.
LeanSearch on finite labeled embedded blowup towers returned ordinary smooth
base change, finite morphisms and closed-immersion base change. Searches in
`WeilConjectures/`, `lean/Sheaf`, and the upstream declaration names found no
matching existing assignment or labeled-tower definition. Searching the item id
in upstream sources found no attachment. DAG search found only this item and its
ordinary-resolution consumer; `tools/blueprint_refs.py search 'labeled tower'`
returned zero blueprint nodes. Exact search outputs for the new notion are in
its `mathlib_searches`. Raw worker search logs remain only in the sandbox.

Source checks: read ILO VIII printed pp.93--94 directly from the local PDF
(PDF pages 99--100): 2.3.11 expressly stops before exceptional-divisor cleanup,
and 2.3.13 discusses the synchronization correction for arbitrary smooth maps.
Read BMT arXiv:0905.3580 online, Theorem 6.1, Addendum (especially (3)--(4)),
and section 6.3: https://arxiv.org/html/0905.3580 . Its embedded and intrinsic
comparisons are the mathematical source of the interface; the new node only
packages data, it does not assert existence or implement the invariant algorithm.

Validation: both delivered files compiled separately and cleanly via the
prescribed `scompile.py`, in dependency order; the wrapper also checked the
library module forms. Explicit universes and `set_option autoImplicit false`
exclude auto-bound variables. The only `sorry` is the main theorem.

## New nodes

`def-trf-labeled-embedded-resolution` packages embedded pairs, finite labeled
ordinary blowup towers, smooth cartesian comparisons, intrinsic comparisons and
their coherent assignment in `LabeledEmbeddedResolution.lean`. The source is ILO
VIII 2.3.1, 2.3.4, 2.3.11--2.3.13 and BMT 6.1 Addendum / 6.3. Existing nodes define
individual blowups, strict transforms, regularity and coherent modules, but none
defines a finite tower with retained ideal centers, common labels and the specified
comparison laws. Its search records contain LeanSearch, LeanFinder/Loogle and
Mathlib/project/DAG grep evidence. It introduces no duplicate of any of those
existing geometric notions. Every declaration is listed in `lean.declarations`.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
