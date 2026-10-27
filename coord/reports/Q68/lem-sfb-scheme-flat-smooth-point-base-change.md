## Worker report

The module `Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange` states
`AlgebraicGeometry.smooth_at_point_pullback_snd_iff_of_flat`. Its only theorem
has proof `sorry`; it introduces no definitions. The node changes only in `lean`.

Hypotheses and clauses, in the order of the node:

- Schemes U, T and T' are `{U T T' : Scheme.{u}}`, with explicit universe `u`.
- The family is `(f : U ⟶ T)`; flatness is `[Flat f]`, and local finite
  presentation is `[LocallyOfFinitePresentation f]`.
- Arbitrary base change is `(h : T' ⟶ T)`, with no assumption on h.
- U' is the chosen scheme `pullback (C := Scheme.{u}) f h`. Its projections
  a and f' are `pullback.fst f h` and `pullback.snd f h`, respectively.
- Every point u' is covered by the unrestricted binder
  `(x : pullback (C := Scheme.{u}) f h)`.
- Smoothness of f' at u' is
  `∃ V : (pullback f h).Opens, x ∈ V ∧ Smooth (V.ι ≫ pullback.snd f h)`.
- Smoothness of f at a(u') is
  `∃ W : U.Opens, pullback.fst f h x ∈ W ∧ Smooth (W.ι ≫ f)`.
- The conclusion connects these two predicates by `↔`, in the node's order.
  In each predicate the open inclusion followed by the family is the restriction
  to that open neighbourhood. No global smoothness assumption is used.

Statement dependencies, with their recorded interfaces read in full:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- def-weil-flat-morphism: `AlgebraicGeometry.Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; its stalkwise equivalence
  `Flat.iff_flat_stalkMap` identifies it with the node's local-ring definition.
- def-sbc-locally-finite-presentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst` and
  `pullback.snd` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. The recorded interface identifies
  this affine-local smoothness with the infinitesimal definition by Stacks 02H6.

The module imports the recorded statement modules publicly and the available
proof modules ordinarily. The latter include
`Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion`
(`AlgebraicGeometry.smooth_at_point_iff_smooth_fibre_at_point`),
`Sheaf.AlgebraicGeometry.FieldBasePointFibreIsomorphism`
(`AlgebraicGeometry.Scheme.fieldBasePoint_fibre_isomorphism`), and
`WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent`
(`Algebra.isSmoothAtPrime_of_fieldExtension`). Mathlib's pullback, fibre and
pullback-carrier modules give the remaining currently recorded proof interfaces.
The two proof dependencies lem-trf-smooth-fibre-affine-ring-at-prime and
lem-trf-affine-smooth-prime-scheme-neighbourhood have no recorded Lean interface
in the read base; they are retained verbatim in the proof docstring and DAG.
They are not notions needed to type this statement.

Source read directly: `literature/stacks-project/morphisms.tex`,
`lemma-set-points-where-fibres-smooth`, Stacks 02V4, case (1), and its proof.
It says W' is the inverse image of W when f is flat and locally finitely
presented, with an arbitrary base map. The pointwise formulation above is
exactly that assertion, with neighbourhood smoothness spelled out.

Edge cases checked before writing:

- Empty pullback (including an empty new base): the point quantification is
  empty, as required, without assuming nonemptiness.
- Identity base change: both sides describe the same local smoothness under
  the canonical pullback isomorphism.
- Nonflat base change: h remains arbitrary. In particular a residue-field
  inclusion into a positive-dimensional base is allowed.
- Inseparable residue-field extensions and positive characteristic: no field,
  characteristic or separability restrictions were added.
- The nodal flat family xy=t includes nonsmooth special points; the theorem
  compares the relative smoothness at corresponding points and does not infer
  smoothness of the entire family from a smooth fibre.
- Flatness of f is substantive: without it, the closed immersion of the origin
  into the affine line becomes an identity after base change to the origin,
  so reflection would fail. Its local finite presentation is also retained.
- The universe is arbitrary and all schemes belong to the same scheme
  category, as required for its categorical pullback; `autoImplicit false`
  rules out hidden variables.

Searches for an existing exact statement:

- msearch.py, leanfinder: "Smoothness at a point of a flat locally finitely
  presented scheme morphism is invariant under arbitrary base change".
  Eight hits, headed by smoothness and flatness stability under base change.
  They give ascent and do not state the pointwise reflection equivalence.
- msearch.py, leansearch: "For a flat locally finitely presented scheme
  morphism smoothness at a point is reflected by arbitrary base change".
  Eight hits, including scheme smoothness stability and
  `Algebra.Smooth.baseChange`; none is the pointwise equivalence.
- msearch.py, loogle:
  `AlgebraicGeometry.Scheme.Hom.smoothLocus, AlgebraicGeometry.Smooth`.
  Two hits: `smoothLocus_eq_top` and `smoothLocus_eq_top_iff`; neither is a
  base-change comparison.
- msearch.py, grep: `preimage_smoothLocus|smoothLocus.*(baseChange|pullback)`
  in AlgebraicGeometry. Four hits. The declaration `preimage_smoothLocus_eq`
  in Mathlib Smooth.lean assumes an open immersion of the source, so cannot
  represent an arbitrary base change. Its full signature was read.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`, by the node id,
  smooth-locus/pullback patterns and the intended declaration name: no exact
  match. `smoothLocus_baseChange` in SemistableMarkedBaseChange requires a
  semistable multipointed pair; ProjectiveNodalFamilyGeometry treats a
  projective nodal family. These are restricted cases, not this general flat
  locally finitely presented statement. The intended name is also absent
  from `dag/lean_names_upstream.json` and Mathlib.

The inherited stage-1 ending was not a stage-2 obstruction: the live node has
a passing split review and no Lean record, and coord/brief-stage2.md section 0
explicitly authorizes this handoff. The accepted split is preserved. No
statement correction, new node or dependency repair is needed; no
STATEMENT-DISPUTED issue was found.

Validation uses scompile.py only. The first attempt needed an explicit
`(C := Scheme.{u})` on the point's pullback to prevent inference of a pullback
in Type. The signature has been corrected accordingly. The corrected file
compiled cleanly both as a sandbox module (8.7 s) and under its library module
name (6.4 s), with no errors or warnings.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
