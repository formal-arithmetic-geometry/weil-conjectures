## Worker report

The module `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace` states
`AlgebraicGeometry.Etale.ambientAffineTranslationTrace`. It uses exactly the
coordinate-tower model already supplied by `lem-amb-affine-space-top-trace`:
`affineTraceTower S d`, `affineTraceLeft A S d`, and
`(affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)` represent affine
space, its compact-support functor, and `A_V(d)[2d]`. This is the dependency's
model of these objects, rather than a new derived category or a new orientation.
The existing `affineTraceAffineSpaceIso` identifies the scheme with the
`AffineSpace (ULift (Fin d)) S` of `def-sbc-affine-space`.

Hypotheses and clauses, in the order of the node:

- `N : ℕ` and `hN : 0 < N` express the positive integer N.
- `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`, and `hA : (N : A) = 0`
  express exactly a finite commutative ring annihilated by N. No domain,
  nonzero-ring, field, or flatness hypothesis is present.
- `S : Scheme.{u}`, `[IsNoetherian S]`, and
  `hS : IsUnit (N : Γ(S, ⊤))` express the Noetherian scheme and invertibility
  of N. Mathlib's `IsNoetherian` is locally Noetherian and quasi-compact,
  equivalently the finite affine-cover condition in the node.
- `d : ℕ` includes zero. `a : Fin d → Γ(S, ⊤)` is exactly a section vector.
- `ambientAffineTranslation S d a` is the scheme isomorphism `z ↦ z-a` on
  the recorded tower. It reuses upstream `AffineSpace.translation`, with
  a negative last coordinate pulled back from S, and `AffineSpace.functor`
  on the preceding coordinates. It is literally `Iso.refl S` in rank zero.
  Its inverse uses the opposite upstream translation at each coordinate.
- The named helper `ambientAffineTranslation_lineSquare` states the Cartesian
  coordinate restrictions of the translation square. These are the squares
  needed to write the actual exchange in the tower model, not an extra
  assumption on the section or the scheme.
- `ambientAffineTranslationExchange` is the existing unbounded proper/open
  exchange pasted over the ordered coordinate compactifications. At each
  step it uses `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and
  `rightDerivedLowerShriekOfCompactificationIso`; at rank zero it inserts
  the canonical identity inverse-image comparison. The dependency's tower,
  composition, and D+/unbounded coherence identify this with the exchange
  named in the node on the shifted Tate input.
- `ambientAffineTranslationTate` is the canonical Tate identification, built
  recursively from tensor pullback, inverse-image composition, and
  `ordinaryFiniteShiftedLinePullback`. The latter uses the normalized roots
  and pure-tensor transport from the dependency. The line expansion helpers
  simply expand the existing projective/open right functor.
  `ambientAffineTranslationTateStep` packages one coordinate pasting, and the
  complete map uses `Nat.rec` with the explicit dependent motive. They do not use
  an arbitrary trivialization or select the bare `Nonempty` right-functor
  isomorphism in the trace dependency.
- `ambientAffineTraceTransport` and `ambientAffineTraceDatum` select the
  normalized data furnished by `exists_affineSpaceTopTrace`. The roots
  inclusion, pure tensors, Kummer Chern specification, decomposition
  components, and counit equations constrain these data and determine the
  maps used here. This is the allowed selection of normalized canonical
  data, rather than selection from an unconstrained existence theorem.
- `affineTraceCounit` is the dependency's actual counit trace at the constant
  coefficient complex. It is used on both sides of the equality. Thus the
  conclusion is precisely `Ex ≫ Rq_!.map κ.hom ≫ t_q = t_q`, the node's
  `t_q ∘ Rq_!(κ_a) ∘ Ex_{τ_a} = t_q` in Lean's composition order.

The postponed theorems are the Cartesian coordinate-square helper and the main
trace equality, both recorded in `lean.declarations` for this node. Their
source and proof docstrings explain respectively the geometric square and all
five steps of the DAG's universal-translation proof. Every definition contains
real data. No trace, exchange, or Tate identification is a free parameter.

Dependency declarations read and used:

- Mathlib: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `IsNoetherianRing`,
  `AlgebraicGeometry.IsNoetherian`, `AlgebraicGeometry.AffineSpace`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the coefficient encoding
  recorded by `def-weil-pbc-derived-categories`).
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `affineTraceLineLeft`,
  `affineTraceLineRight`, `affineTraceLeft`, `affineTraceRight`,
  `affineTraceCounit`, and `exists_affineSpaceTopTrace`.
- `Sheaf.AlgebraicGeometry.AffineTraceTower`: `affineTraceTower`,
  `affineTraceProjection`, `affineTraceAffineSpaceIso`,
  `affineTraceLineCompactification`, `affineTraceInvertible`,
  `affineTraceProjectiveInvertible`. This already-landed definition node is
  added to `stmt_deps` because the statement uses its coordinate model.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback`, whose normalized
  finite-line transport is the recorded `OrdinaryFiniteTwistTransport`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification` and the existing canonical
  proper/open comparisons (ordinary etale compact supports).
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleCompactSupportBaseChange`, its tower/plus normalization
  package, and `unboundedEtaleUpperStarIdIso`.
- Proof-only imports retain the recorded compact-support action,
  constant-sheaf sections, degree-zero full faithfulness, Noetherianity,
  polynomial-domain, prime-spectrum, connected locally constant-map,
  and Nagata compactification inputs. No import cycle is introduced.

Edge cases checked: rank zero makes the tower, adjunction, and translation
identities, with the canonical constant-object pullback identification; a zero
translation vector also gives identity translations. The empty scheme is
permitted by `IsNoetherian` and the invertibility predicate. Nothing assumes
that S is connected or reduced. The multiplier proof applies fibrewise over
residue fields. `A = 0` is permitted, including `N = 1`; the identities are
then identities on zero coefficient complexes. Universes are the existing
ordinary etale convention `Scheme.{u}`, coefficients `Type (u + 1)`; no
additional equality of universes or essential-smallness assumption is imposed.

Searches actually run in this session:

- `msearch.py ... leanfinder "Translation invariance of the compactly supported
  etale trace of affine space over a Noetherian base"`: eight hits, on
  `AffineSpace.homOfVector_toSpecMvPoly`, smooth/etale algebra, and ring trace
  quotient/localization; none states the desired derived trace equality.
- `msearch.py ... loogle '"trace", "AffineSpace"'`: zero hits.
- `msearch.py ... grep 'translation.*trace|trace.*translation' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in upstream `WeilConjectures` and side-project `lean/Sheaf` for the
  same patterns and the proposed declaration names: no matching trace theorem.
  The exact blueprint-id grep in upstream also found none.
- A focused upstream affine-space search found `AffineSpace.translation`,
  `translation_add`, `translation_zero`, `translation_over`, and `functor`.
  Their signatures and bodies were read and are reused, not copied.

The earlier ledger's Q84 merge is a stage-1 split, as confirmed by its report
and lack of a Lean binding. The authorized stage-2 dry run accepts a Lean
packet on top of that split. This delivery does not re-split the node or
change its natural-language statement, proof, or review fields. No new
independent notion, dependency repair, statement correction, or disputed
statement is needed.

## Author self-check

The first draft mistakenly bound arbitrary maps for the three canonical maps.
That draft was discarded. The final construction uses the actual counit,
canonical exchanges, and normalized Tate transport throughout. I checked the
node and final signature clause by clause as above. There is no independent
second worker in this session; the maintainer performs the independent review.

## Validation

The final module passed `scompile.py Q04 lem-trf-ambient-affine-translation-trace`
with the standard settings and 60-second per-file limit. The sandbox check took
28.3 seconds and the library-path check took 26.3 seconds, both with no warnings
or errors. Diagnostic heartbeat and profiler settings have been removed.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
