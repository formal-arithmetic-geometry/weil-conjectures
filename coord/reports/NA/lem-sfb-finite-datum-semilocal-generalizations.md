## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteDatumSemilocalGeneralizations` states
`AlgebraicGeometry.exists_invariant_semilocal_generalizations`, with one whole-proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement changes.

Hypothesis and conclusion correspondence, checked with the node and module open:

- Affine schemes Q and S: `{Q S : Scheme.{u}} [IsAffine Q] [IsAffine S]`.
- Finite surjective q: `(q : Q ⟶ S) [IsFinite q] [Surjective q]`; there is no flatness
  hypothesis on q.
- Scheme Z over Q: `(V : Over Q)`, with Z = V.left and structure morphism V.hom.
- Noetherian means exactly locally Noetherian and quasi-compact:
  `[IsLocallyNoetherian V.left] [CompactSpace V.left]`.
- Descent datum: `(D : Over.DescentDatum q V)`, the dependency's existing upstream
  transport-style definition, whose documentation identifies it with the cocycle isomorphism.
- R = Z ×_S Q is `pullback (V.hom ≫ q) q`; r0 is `pullback.fst (V.hom ≫ q) q`;
  r1 is `D.toHom`, the existing universal-point transport morphism from that same module.
  Its source is definitionally precisely R.
- Finite subset E: `(E : Set V.left) (hE : E.Finite)`; invariance is the exact equality
  `pullback.fst (V.hom ≫ q) q ⁻¹' E = D.toHom ⁻¹' E`.
- A quasi-affine open containing E: `hQuasiAffine` supplies an open `W`, `E ⊆ W`, an
  affine scheme A and an open immersion `i : W.toScheme ⟶ A`, with W quasi-compact.
  An open immersion identifies W with its open image in A. Its image is quasi-compact
  exactly when W is, so this is the stated isomorphism to a quasi-compact open in an
  affine scheme. No relative quasi-affineness hypothesis on Z → Q is introduced.
- Existence of L and j: `∃ (L : Scheme.{u}) (j : L ⟶ V.left)`.
- L affine, j quasi-compact, flat, monic: `IsAffine L ∧ QuasiCompact j ∧ Flat j ∧ Mono j`.
  Mathlib's QuasiCompact condition on compact opens is equivalent to the node's condition
  on affine opens, which form a basis; Mono is equivalent to invertibility of the diagonal.
- Exact image: `Set.range j = {z | ∃ e ∈ E, z ⤳ e}`. The orientation means z specializes
  to e, exactly the generalizations of E, not its specialization closure.
- Equality of the two pullback subfunctors of h_R: for every scheme T and every T-point
  `g : T ⟶ R`, existence of `a : T ⟶ L` with `a ≫ j = g ≫ r0` is equivalent to
  existence of one with `a ≫ j = g ≫ r1`. By the pullback universal property these are
  precisely membership in the two pullback subfunctors. Since j is monic, the lifts are
  unique, so these propositions describe the actual subfunctors, without requiring a
  chosen isomorphism or replacing equality by mere equality of topological images.
- Image contains E and is stable under generalization:
  `E ⊆ Set.range j ∧ StableUnderGeneralization (Set.range j)`.
- Semilocality: `Finite (MaximalSpectrum Γ(L, ⊤))`, literally finitely many maximal
  ideals of the coordinate ring. This uses the existing Mathlib maximal spectrum.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `Scheme.Opens`, and the global-sections notation.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and `CategoryTheory.Over.DescentDatum.toHom`.
  Read the full structure, the equivalence explanation, and the universal-point definition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.fst`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and its documented
  equivalence with flatness of stalk maps.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- Also `IsAffine`, `QuasiCompact`, `Surjective`, `Mono`, `StableUnderGeneralization`,
  and `Mathlib.RingTheory.Spectrum.Maximal.Defs.MaximalSpectrum` use existing notions.

Proof dependencies that have recorded modules or Mathlib matches are imported privately,
including prime avoidance, localization spectra/preimmersions/flatness, ideal subschemes,
quasi-compact/quasi-separated permanence, proper/finite maps, finite fibres, and pullback
images. The still-unstated `lem-sfb-qc-flat-monomorphism-ringed-image` is only a proof
input; it has no recorded module to import. No new interface for it is needed for this
statement. The complete seven-step DAG proof is in the theorem's docstring.

Edge cases checked: E empty (L = Spec 0 and empty maximal spectrum); empty Z and empty
base; singleton generic point; comparable points of E (only inclusion-maximal point
primes contribute maximal ideals); nonclosed points; nonflat finite surjective q.
No nonemptiness, reducedness, separation, or finite-presentation condition was added.
All schemes and test schemes use the same arbitrary universe u. There are no auto-bound
variables, file-local notation, extra axioms, or constructed data with sorry.

Searches actually run through the prescribed msearch wrapper:

- LeanFinder: `For a finite descent datum an invariant finite subset in a quasi affine
  open has an invariant affine semilocal generalization subscheme`. Eight hits on affine
  transition-limit cover constructions and affine charts, no matching theorem.
- Loogle: `AlgebraicGeometry.Flat, CategoryTheory.Mono`. Six hits: flat pushout-section
  monomorphisms, the finite-presentation open-immersion criterion, and the surjective
  quasi-compact flat mono isomorphism criterion; none constructs this invariant subscheme.
- Mathlib grep (AlgebraicGeometry): `semilocal|semi.local|invariant.*monomorphism`.
  Zero hits.
- LeanSearch: `Invariant semilocalization of a finite subset under a scheme descent datum`.
  Eight hits on descent of morphism properties and localization modules, no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for semilocal/finite-datum names
  found semilocal normalization and unrelated ring/curve lemmas, no matching theorem.
  Exact item-id and proposed declaration-name searches found no existing declaration.
  The upstream name index has only the unrelated semilocal-fibre-generators attachment.

Source check: read the current `literature/blueprint/latest/` direct-image proof and
Raynaud's primary Numdam scan, printed pp. 5-17 and 5-21, including Lemma 4.3 and the
start of reduction 6. Those passages give the affine semilocal generalizations and
pullback agreement. The node's seven-step prime-avoidance proof supplies its explicitly
stated quasi-affine-open variant. No statement dispute or node fault was found.

## Second reading by NA

The dispatcher explicitly forbids starting another agent; this section records a fresh
self-reading, not an independent reviewer. Independent review is by the maintainer.
Reopened the JSON statement and the complete Lean signature. Matched every hypothesis
and clause as listed above, including the distinction between absolute quasi-affineness
of W and a relative property, the canonical source of D.toHom, the specialization
orientation, the actual functor-of-points condition, and the empty maximal spectrum.
No mismatch found and no statement change made.
