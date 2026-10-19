## Worker report

The delivery states `AlgebraicGeometry.Scheme.normalization_completion_base_change` in
`Sheaf.AlgebraicGeometry.NormalizationCompletionBaseChange`. Its only theorem has proof
`sorry`; no definitions or auxiliary theorems are added. The source was read in
`literature/stacks-project/resolve.tex`, lines 2972–3021, the statement and entire proof of
`lemma-normalization-completion` (Tag 0BG9). It agrees with the node without correction.
The declaration docstring supplies the source's affine reduction, faithful flat descent,
Nagata finiteness, formal gluing of finite algebras, normality descent, and final gluing.
The DAG's proof and proof_deps are empty, so no separate recorded proof imports exist.

Hypotheses and clauses, in order:

- The commutative Noetherian local ring `(A,m)` is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`, with `m = IsLocalRing.maximalIdeal A`.
- Its completion is exactly `AdicCompletion (maximalIdeal A) A`, with the canonical
  `algebraMap A (AdicCompletion (maximalIdeal A) A)`, not an arbitrary complete algebra.
- `X → Spec A` is `f : X ⟶ Spec (CommRingCat.of A)` for `X : Scheme.{u}`;
  locally of finite type is precisely `[LocallyOfFiniteType f]`. No quasi-compactness,
  separatedness, reducedness, integrality, excellence, or domain assumption is imposed.
- The scheme `Y` is the actual `pullback f (Spec.map (CommRingCat.ofHom (algebraMap ...)))`.
  Its map to `Spec Â` is `pullback.snd`. The annotation `: Scheme.{u}` fixes the category
  for the point binder, so it cannot be mis-inferred as a pullback in Type.
- The special fibre has underlying set of points sent by that second projection to
  `closedPoint (AdicCompletion (maximalIdeal A) A)`. Thus `hnormal` quantifies over every
  point `y : Y` whose image differs from that closed point, and requires `IsDomain
  (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)`. These are the local
  normal domains defining normality of the open complement. Stalks there agree with
  the ambient stalks, so no open choice or hypothesis is hidden.
- The componentwise normalization and its map are the dependency's `X.reducedNormalization`
  and `X.fromReducedNormalization`. In particular, this is not Mathlib's normalization of
  the structure morphism `f`.
- Finiteness is the first conjunct `IsFinite X.fromReducedNormalization`.
- The second conjunct supplies an isomorphism `e` from `Y.reducedNormalization` to
  `pullback (X.fromReducedNormalization ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap ...)))`.
  Reversing this isomorphism gives the orientation stated by the node.
- The first equation compares the maps to `X`: `e.hom ≫ pullback.fst _ _ ≫
  X.fromReducedNormalization = Y.fromReducedNormalization ≫ pullback.fst f _`.
  The second compares maps to `Spec Â`: `e.hom ≫ pullback.snd _ _ =
  Y.fromReducedNormalization ≫ pullback.snd f _`. Jointly, by the pullback universal
  property, they say exactly that the comparison is over `Y`. They do not impose a
  further property or uniqueness assertion.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-finiteness meaning.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`; the actual ring and algebra
  structures were read in `.Algebra`. `.LocalRing` supplies the completion's local-ring
  instance, identifying its closed point without an extra assumption on the completion.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence for schemes.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: the full file was read, including
  `reducedNormalizationComponent`, `isIntegral_reducedNormalizationComponent`,
  `reducedNormalization`, and `fromReducedNormalization`. The integral component's
  function-field normalization is the upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, also inspected.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with `IsDomain` for normal local domains. This follows the normal-ring node's recorded
  inline convention. `IsNormalScheme` in the project is unsuitable: it additionally
  requires integrality of the entire scheme, excluding disconnected and empty opens.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.

Edge cases checked: `X` empty gives an empty normalization and an empty pullback; all
normality hypotheses are vacuous and the conclusion is valid. When `A` is a field, its
maximal ideal is zero and its spectrum has only the closed point: the normality hypothesis
is vacuous, while finite-type schemes over a field have finite normalization and completion
is the identity. Nonreduced schemes and multiple irreducible components are retained by
using the existing reduced componentwise normalization. No global compactness or finite
number of components is required. Arbitrary characteristic is allowed. `A` and `X` have a
common arbitrary universe `u`, as required for scheme fibre products; the completion stays
in `Type u`.

Searches actually run (logged in sandbox searches.jsonl):

- LeanFinder: “Normalization of a locally finite type scheme over a Noetherian local ring
  commutes with completion when the completed scheme is normal away from the special fibre”.
  Eight hits, all relative-normalization constructions or their composition identities;
  no completion theorem.
- Loogle: `AdicCompletion, AlgebraicGeometry.IsFinite`: zero hits.
- Mathlib grep through msearch: `normalization.*completion|completion.*normalization`
  in AlgebraicGeometry: zero hits.
- LeanSearch: “Normalization commutes with completion of a Noetherian local base if the
  completed scheme is normal outside its special fibre”. Eight relative-normalization
  hits, including `Scheme.Hom.normalizationDesc`, none with the required completion or
  finiteness assertion.
- Direct rg over upstream `WeilConjectures` and side `lean/Sheaf` for normalization,
  completion, reducedNormalization, and the proposed theorem/module name. The existing
  function-field and componentwise normalizations were reused. Related curve-normalization
  completion and coherent-completion theorems concern different objects/hypotheses. The
  normalized-blowup-completion-descent module cites this missing lemma in its proof plan;
  it does not state it. Exact item-id grep over upstream had no matches. The proposed
  declaration name was also searched in `dag/lean_names_upstream.json`, with no match.

Validation: prescribed `scompile.py` compiled both its sandbox-check module and final
library module cleanly (2.1 seconds each), with no diagnostics. `autoImplicit` is explicitly
false, and the only universe variable is declared. The initial type-inference error in the
point binder was repaired by specifying the pullback's scheme category. There are no node
faults, statement corrections, new nodes, or dependency modules.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (H8)

The Worker report says the DAG proof is empty. It is not: the node (split 2026-10-19,
reviewed by NR) has an eight-step proof (affine reduction and the Nagata input; finiteness
of `C^ν`; formal gluing to a finite `D`; normality descent along `D → C^ν`; minimal primes
of `D`; generic residue fields; normalization recognition; gluing). The delivered
docstring gave a different five-step route. The maintainer replaced the theorem
docstring with the node's eight steps. The statement, the signature, the imports and the
`lean` record are unchanged. The fixed module compiles cleanly with `nt_compile.py`.
