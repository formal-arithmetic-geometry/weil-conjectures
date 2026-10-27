## Worker report

The module `Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle` states
`AlgebraicGeometry.isProjectiveBundle_of_isProper_of_relative_ample`, with `sorry` as
its sole proof. No definitions, other theorem statements, or new nodes are introduced.
The item's JSON changes only in `lean`.

The previous retry classified Q07's landing as making this assignment stale. I checked
the current item and the ledger: Q07's 2026-10-22 05:21 landing was the stage-1 split,
with `reviewed.result = pass`, but no `lean` or `reviewed_lean`. It does not supply a
Lean statement or prevent this stage-2 delivery. The reported retained report was
absent at the sandbox path when this attempt began.

I read the source in `literature/stacks-project/morphisms.tex`: Definition
definition-relatively-ample (01VH), definition-quasi-projective (01VW(1)),
definition-projective (01W8(1)), and lemma-projective-is-quasi-projective-proper
(0BCL(1)), including its proof. A proper morphism is of finite type, so the item's
relative-ampleness assumption gives the quasi-projectivity used in the converse of
0BCL(1). Both base hypotheses are retained. The source uses a finite-type
quasi-coherent projective bundle, which is exactly the conclusion below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes X and S and the morphism h are `{X S : Scheme.{u}} (h : X ⟶ S)`.
  The universe `u` is explicitly declared and unrestricted. Both automatic implicit
  options are disabled.
- Properness is `[IsProper h]`, the recorded Mathlib predicate. Its parent classes
  give separatedness, universal closedness and local finite type. Universal
  closedness implies quasi-compactness, giving the finite type in the source.
- Quasi-compactness of S is `[CompactSpace S]`. Mathlib's compactness imposes no
  Hausdorff condition.
- Quasi-separatedness of S is `[QuasiSeparatedSpace S]`. I read
  `quasiSeparatedSpace_iff_forall_affineOpens` and the equivalence with
  quasi-separatedness of the structural morphism in Mathlib's QuasiSeparated module.
- Existence of an invertible O_X-module is the literal existential
  `∃ L : X.Modules, L.IsInvertible ∧ ...` in `hample`. L is a genuine module in the
  recorded category, not an arbitrary object or an ample-module witness assumed
  independently of h.
- The quasi-compactness clause in relative ampleness is `QuasiCompact h` inside
  `hample`. It is retained even though properness also implies it, because the node
  expressly spells out this conjunct as part of relative ampleness.
- Every affine open of S is `∀ V : S.Opens, IsAffineOpen V → ...`. The restriction
  of L to h^{-1}(V) is
  `(Scheme.Modules.tensorPullback (h ⁻¹ᵁ V).ι).obj L`, using the canonical tensor
  pullback along the open inclusion. Its scheme is `(h ⁻¹ᵁ V).toScheme`.
- Absolute ampleness of each restriction is `@Scheme.Modules.IsAmple ... hL`.
  The preceding `∃ hL : (...).IsInvertible` supplies the proof argument required
  by the existing absolute-ampleness predicate. This is the same restriction
  interface as `relative_ample_very_ample`; it introduces no new mathematical
  assumption since restrictions of an invertible module are invertible. The
  proof object is irrelevant, so the existential does not choose new module data.
- The conclusion is exactly `IsProjectiveBundle h`: an existential finite-type
  quasi-coherent module E on S and a closed immersion into the canonical relative
  Proj of Sym(E), whose composite with its structure morphism is h. This is the
  recorded projective-bundle convention. No locally free E, embedding into a
  fixed finite projective space, or Noetherian hypothesis is required.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
  (def-weil-finite-type-morphism); finite type is their conjunction.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (def-sc-invertible-module).
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`
  (def-weil-pbc-ample-invertible-module). I read its full definition, including
  positive tensor powers, global sections, maximal-ideal stalk condition and
  quasi-compactness.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper` (def-weil-proper-morphism), and
  `AlgebraicGeometry.IsProper.of_comp` (lemma-nagata-proper-to-separated-target).
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`
  (def-weil-pbc-quasi-compact-scheme).
- def-weil-pbc-scheme-conventions records a convention rather than a declaration.
  Its quasi-separated meaning is rendered by `QuasiSeparatedSpace`, using
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `AlgebraicGeometry.IsProjectiveBundle` (def-trf-projective-bundle-morphism).
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, the existing canonical
  tensor-formula pullback, used for restriction as in the next dependency.
- `Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple`:
  `AlgebraicGeometry.Scheme.Modules.relative_ample_very_ample`, read in full,
  including precisely the same affine-restriction relative-ampleness predicate.
- `Sheaf.AlgebraicGeometry.RelativelyVeryAmple`:
  `AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple`.
- `Sheaf.TraceFormula.ProjectiveBundleSeparated`:
  `AlgebraicGeometry.isSeparated_projectiveBundle`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`, the mathlib_match of
  lem-weil-pbc-proper-immersion-closed, together with the closed-image property
  coming from universal closedness.

All stated proof dependencies are imported. The proof-only node
lem-sfb-very-ample-finite-type-realization has neither a recorded Lean declaration
nor a Mathlib match in the read repository, so there is no module to import for
it yet. The five-step proof docstring names it at exactly the finite-type
realization step. Its statement is not needed to type this theorem's statement;
no missing construction is assumed or replaced in this delivery.

Edge cases checked before writing:

- X empty: absolute ampleness has no pointwise tests; restriction schemes remain
  empty and quasi-compact. The empty closed subscheme of a projective bundle is
  allowed. There is no nonemptiness or positive-rank hypothesis.
- S empty: h forces X empty, so the same case is retained; there is no excluded
  affine-open or point case.
- Empty affine opens are included in `∀ V`; the absolute predicate on their
  inverse images has precisely its usual vacuous pointwise condition.
- Arbitrary non-Noetherian qcqs S: both the statement and the projective-bundle
  predicate allow this. Finite-type approximation in proof step 3 supplies E;
  coherent proper pushforward is not silently used.
- E need not be locally free, and it may be zero for an empty source. The
  conclusion places no extra rank or finite-projective-space restriction on E.
- No characteristic, dimension, reducedness, or field restriction appears.

Searches actually run on this attempt:

- msearch leanfinder: "A proper morphism of schemes with a relatively ample
  invertible sheaf over a quasi compact quasi separated base is projective in
  the projective bundle sense". Eight hits: Proj properness/universal
  closedness/quasi-compactness, IsProper, isProperMap, finite-morphism
  properness, and Proj separatedness. None gives this relative-ampleness to
  projective-bundle embedding statement.
- msearch loogle: `"AlgebraicGeometry", "IsProjectiveBundle"`. OK, zero hits.
- msearch grep over Mathlib/AlgebraicGeometry:
  `IsProjectiveBundle|[Pp]roper.*[Aa]mple|[Aa]mple.*[Pp]roper`. OK, zero hits.
- msearch leansearch: "A proper morphism admitting a relatively ample
  invertible sheaf over a quasi compact quasi separated scheme is projective".
  Eight hits on IsProper, its constructors/projections/equivalent predicates,
  and the valuative criterion; no matching theorem.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for IsProjective,
  IsRelativelyAmple/RelativelyAmple and proper/ample/projective combinations.
  The existing `IsProjective` is the finite-projective-space convention;
  `IsProjectiveBundle` is the correct existing conclusion. The nearby
  `proper_fibrewise_ample_projective` assumes Noetherian schemes and geometric
  fibre degree conditions, so it is not this statement. The existing
  `relative_ample_very_ample` provides the correct inline hypothesis interface.
- rg for the exact item id in those two source directories finds only the
  proof docstring in ProjectiveBundleComposition.lean; no existing declaration
  states the item. The new theorem name has no source collision in those
  searches.

No statement dispute or node correction was found.

Validation: the prescribed scompile.py compiled this file both as a sandbox
module (7.7 seconds) and under its final library module name (8.6 seconds),
with exit status zero and no unexpected warnings. A local comparison confirms
that `lean` is the sole changed JSON field, the recorded signature is extracted
verbatim from the source, there is exactly one named theorem and one `sorry`,
and every source line has at most 100 characters. Delivery preflight is run
through deliver2.py only.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
