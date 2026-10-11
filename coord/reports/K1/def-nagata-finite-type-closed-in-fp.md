## Worker report

The module `Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope` defines
`AlgebraicGeometry.nagataFinitePresentationEnvelope`, the explicit dependent pair
`Env_fp(X/S)`. This is a full noncomputable definition with no `sorry`, no new
notion, and no theorem proved. The node copy changes only `lean`.

Source read: the original blueprint page
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-envelope/def-nagata-finite-type-closed-in-fp.md`,
order 396, over read-only SSH on the server because literature is absent from the
local clone. It states exactly the imported node, including the bypass status note.
Both statement dependency nodes, their recorded declarations and their complete
signatures/docstrings were read.

Hypothesis and clause correspondence:

- Schemes `X` and `S`, and the morphism `X → S`: explicitly bound as
  `{X S : Scheme.{u}} (f : X ⟶ S)`, with explicit universe `u`.
- The base `S` is qcqs: `[CompactSpace S] [QuasiSeparatedSpace S]`.
- The morphism is finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`.
- The morphism is separated: `[IsSeparated f]`.
- No additional hypothesis on `X` is imposed. The local instances
  `QuasiCompact.compactSpace_of_compactSpace f` and
  `quasiSeparatedSpace_of_quasiSeparated f` supply its qcqs structure, using the
  Mathlib instance `IsSeparated f → QuasiSeparated f`.
- Form `FP(X/S)`: `F := Classical.choice
  (f.nonempty_finitePresentationApproximation)` has exactly the recorded type
  `f.FinitePresentationApproximation`. The existence theorem's source proof
  constructs the closed-subscheme system of finite type subideals of a closed
  immersion into a finite-presentation model, following the immersion/shrinking
  construction in the dependency. This supplies the chosen system; no private
  system structure is introduced.
- Its index set and models are `F.I` and `F.D.obj`; its structural maps `i_α`
  are `F.π.app`. The fields record closed immersions and the compatibility
  `F.w i : F.π.app i ≫ F.p.app i = f`.
- Apply the selected-stage dependency: `αsep := nagataSeparatedStage
  F.isLimit F.p i₀`. The initial index `i₀` is chosen from
  `IsCofiltered.nonempty (C := F.I)`, as required by the dependency's signature.
  The necessary separatedness instance is transported along `F.w i₀` from
  `[IsSeparated f]`; it adds no hypothesis or postponed proof.
- The equation `α_sep^(X/S) = α_sep` is the preceding local definition `αsep`.
- `X_fp = X_αsep` is the pair's first component `F.D.obj αsep`.
- `i_fp = i_αsep : X → X_fp` is its second component `F.π.app αsep`.
- The explicit pair is `⟨F.D.obj αsep, F.π.app αsep⟩` of type
  `Σ Y : Scheme.{u}, X ⟶ Y`. Closedness is already recorded by
  `F.isClosedImmersion_π`; the definition does not add a separate existence
  conclusion or restate the later envelope specification theorem.

Dependency declarations used:

- `def-nagata-fixed-base-separated-stage`:
  `Sheaf.AlgebraicGeometry.NagataFixedBaseSeparatedStage`,
  `AlgebraicGeometry.nagataSeparatedStage` (the direct import).
- `def-nagata-finite-type-fp-model-system`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
  `AlgebraicGeometry.Scheme.Hom.FinitePresentationApproximation`, together with
  its fields and `Scheme.Hom.nonempty_finitePresentationApproximation` from the
  same source module (available through the direct import). The structure is
  reused, not copied.

Edge cases checked before writing: the empty source is permitted; an empty base
forces the source empty but changes none of the construction. A cofiltered index
category is nonempty even for an empty scheme, so the auxiliary choice `i₀`
requires no extra assumption. Identity morphisms and separated finite-type
morphisms over affine fields fit the same signature. There is no Noetherian,
nonempty-scheme, reducedness, characteristic, or finite-presentation assumption
on `f`. All schemes and the dependency's small index category share arbitrary
universe `u`, as required by the recorded dependency; no test objects are
quantified in a smaller universe.

Searches actually run with `msearch.py` (group K1, this item):

- LeanSearch, query `Separated finite presentation envelope of a finite type
  scheme morphism chosen from finite presentation approximations`: unavailable
  (HTTP Internal Server Error), not recorded as a negative mathematical result.
- LeanFinder, the same query: eight hits, involving affine space and general
  locally-finite-presentation and separatedness declarations; no envelope pair.
- Loogle, query `AlgebraicGeometry.IsSeparated, AlgebraicGeometry.FinitePresentation`:
  zero hits with diagnostic unknown identifier `AlgebraicGeometry.FinitePresentation`.
  This query supplies no substantive evidence of absence.
- Mathlib grep, query `envelope|FinitePresentationApproximation`, subdirectory
  `AlgebraicGeometry`: no matches.
- `rg` of the project's `lean/Sheaf` and source `WeilConjectures` for
  `envelope|Env_fp|FinitePresentationApproximation|nagataSeparatedStage`: the
  recorded approximation structure and stage selector exist; the source envelope
  theorem `Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation`
  is an existential proposition, not the explicit definition of the pair.
- `grep -rn` of the source for the exact item id: no matches.
- Name collision search for `nagataFinitePresentationEnvelope` in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no matches.

Validation: the server single-file compile completed in 1.8 seconds with exit
code 0 and no warnings. The dry run is run after writing this report; the second
reader will supply the independent second-reading section and deliver.

No statement correction, disputed statement, new node, or dependency module.

## Second reading by K1

I independently read the node statement, its source place, both dependency nodes, and the Lean declaration.
The objects and clauses match as follows:

- The node's qcqs base (S) and source/target schemes (X,S) render as
  `{X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]`.
  The universe is shared, so no covered scheme case is excluded.
- “Separated and of finite type” renders as `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, and `[QuasiCompact f]`.  These are precisely the
  standard scheme-morphism type-class hypotheses; no Noetherian, finite-presentation,
  characteristic, nonempty, or reducedness assumption is added.
- The finite-presentation system `FP(X/S)` is the chosen
  `F := Classical.choice (f.nonempty_finitePresentationApproximation)`, namely
  `Scheme.Hom.FinitePresentationApproximation`, the recorded dependency
  `def-nagata-finite-type-fp-model-system`.  Its index, models, projections, and
  compatibility are used as `F.I`, `F.D.obj`, `F.π.app`, and `F.w`.
- The selected index is rendered by
  `αsep := nagataSeparatedStage F.isLimit F.p i₀`, with
  `i₀ := Classical.choice (IsCofiltered.nonempty (C := F.I))`.  The required
  separatedness instance is transported from `[IsSeparated f]` along `F.w i₀`.
  This is exactly `def-nagata-fixed-base-separated-stage` and adds no hypothesis.
- The displayed definitions (alpha^{X/S}_{\rm sep}=alpha_{\rm sep}),
  (X^{\rm fp}=X_{\alpha_{\rm sep}}), and
  (i^{\rm fp}_{X/S}=i_{\alpha_{\rm sep}}) render as the local `αsep` and the
  returned sigma pair `⟨F.D.obj αsep, F.π.app αsep⟩`.  The projection is a closed
  immersion by `F.isClosedImmersion_π`; the later proposition records that property,
  as in the node's definition-versus-specification split.
- The final explicit pair `Env_fp(X/S)` renders as
  `nagataFinitePresentationEnvelope ... : Σ Y : Scheme.{u}, X ⟶ Y`.

The empty scheme, empty base, identity morphisms, and zero-dimensional cases are
covered by the same type-class hypotheses.  Cofilteredness supplies `i₀` without a
nonemptiness assumption on (X) or (S).  No characteristic or `n = 0` parameter
occurs.  All index and scheme universes are the common `u` required by the
approximation dependency.

Searches found no duplicate explicit envelope definition: LeanFinder returned only
unrelated finite-presentation/separatedness declarations; grep over Mathlib,
`WeilConjectures`, and `lean/Sheaf` found no `nagataFinitePresentationEnvelope` or
`Env_fp` declaration.  The source's existing theorem is existential and therefore
is not this definition.

No mismatch was found.  The worker module was left unchanged; its declaration
compiled cleanly with `scompile.py`, and the node copy changes only the `lean`
record with the exact signature.  No statement correction, new node, or dependency
module is needed.
