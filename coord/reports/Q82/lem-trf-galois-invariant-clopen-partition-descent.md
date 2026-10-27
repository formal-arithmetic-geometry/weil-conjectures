## Worker report

The module `Sheaf.AlgebraicGeometry.GaloisInvariantClopenPartitionDescent` states
`AlgebraicGeometry.existsUnique_clopen_partition_of_galois_invariant`, with its
whole proof `sorry`. It introduces no definition. Only the item's `lean` field
is changed; no statement correction, new nodes or dependency repair is needed.

Source read: `literature/stacks-project/varieties.tex`, Tag 038B,
`lemma-closed-fixed-by-Galois` (lines 898–934), and Tag 038C, `lemma-tricky`,
the descent paragraph immediately following the displayed intersection/union
(lines 1042–1053). Tag 038B descends each invariant closed subset; the recorded
surjectivity facts yield the partition, nonemptiness and uniqueness.

Hypothesis and conclusion correspondence:

- The fields and extension are `(k L : Type u) [Field k] [Field L] [Algebra k L]`.
  `algebraMap k L` is the given embedding. `[IsGalois k L]` means precisely
  separable algebraic and normal: Mathlib's `IsGalois` contains
  `Algebra.IsSeparable k L` and `Normal k L`; the latter requires every mapped
  minimal polynomial to split. No finite-dimensional hypothesis is imposed.
- The arbitrary k-scheme is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
  Its structure morphism is `X ↘ Spec (.of k)`.
- The types of `P Q` explicitly use the underlying points of the chosen pullback
  of this structure morphism and
  `Spec.map (CommRingCat.ofHom (algebraMap k L))`. This is exactly X_L.
- `hPne`, `hQne` assert nonemptiness; `hP`, `hQ` assert `IsClopen` for both.
  `hdisjoint : Disjoint P Q` and `hcover : P ∪ Q = Set.univ` assert the
  disjoint union decomposition X_L = P ⊔ Q.
- `hPinvariant` and `hQinvariant` quantify over all `σ : L ≃ₐ[k] L` and
  assert equality of each subset with its image under
  `baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)`.
  `specAlgEquivOver` is literally the spectrum of σ over Spec k;
  `baseChangeMap` is the canonical id_X × Spec(σ), using pullback.map.
- `∃! R : Set X × Set X` expresses existence and uniqueness of an ordered pair.
  `R.1.Nonempty ∧ R.2.Nonempty` and `IsClopen R.1 ∧ IsClopen R.2` express
  the specified properties of P₀ and Q₀. `Disjoint R.1 R.2` and
  `R.1 ∪ R.2 = Set.univ` express X = P₀ ⊔ Q₀. The last two conjuncts
  are exactly the two preimage equalities along the chosen `pullback.fst`.
- There are no connectedness, quasi-compactness, finite-type or nonemptiness
  assumptions on X itself, or any finiteness restriction on L/k.

Dependency declarations read and used:

- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` (field extension).
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, `IsSeparable`;
  `Mathlib.FieldTheory.Normal.Defs`: `Normal`;
  `Mathlib.FieldTheory.Galois.Basic`: `IsGalois` (separable algebraic plus normal).
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, with its structure arrow.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  base-change conventions identify X_T with `Limits.pullback` and p with
  `pullback.fst`. `moduleBaseChange` is not used: it concerns modules, not points.
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`: `specAlgEquivOver`;
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`: `baseChangeMap`.
- Proof import `WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends`:
  `exists_closed_subset_of_galois_invariant`, with exactly the same action and
  pullback convention. The source is now proved upstream, but this delivery
  still postpones its own theorem as required for stage 2.
- Proof imports `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` and
  `Mathlib.AlgebraicGeometry.PullbackCarrier`: the nonempty-to-subsingleton
  `Surjective` instance for Spec L → Spec k and the
  `Surjective.instIsStableUnderBaseChangeScheme` instance. These are the two
  Mathlib proof leaves' recorded interfaces.

Edge cases checked before writing: L = k gives the original partition unchanged;
infinite Galois extensions are admitted by IsGalois without FiniteDimensional;
empty X admits no nonempty P,Q, so the implication is vacuous; disconnected,
non-quasi-compact, nonreduced and arbitrary-characteristic schemes are allowed.
The partition is ordered, so a swap does not satisfy the prescribed preimages.
The common arbitrary universe u follows the recorded Scheme/Spec/pullback API;
it allows every size of field and scheme after choosing an ambient universe.

Searches actually run:

- `msearch.py ... leanfinder` with query "Galois invariant nonempty clopen
  partition of a scheme after scalar extension descends uniquely to the original
  scheme": eight hits, about AffineTransitionLimit and PullbackCarrier;
  none gives this partition descent statement.
- `msearch.py ... loogle 'Topology.IsQuotientMap, IsClopen'`: one hit,
  `Topology.IsQuotientMap.isClopen_preimage`. It reflects clopenness of an
  existing preimage, without supplying Galois saturation or the descended pair.
- `msearch.py ... grep` with regex
  `[Gg]alois.*[Cc]lopen|[Cc]lopen.*[Gg]alois|clopen.*descen|descen.*clopen`:
  zero Mathlib hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for Galois/clopen,
  Galois/partition and `clopen_partition`: upstream
  `exists_finite_invariant_clopen_partition` constructs an invariant partition
  over a finite intermediate field from a different input, rather than descending
  the given ordered invariant pair to k. The many Scheme.GaloisPartition hits
  concern constructible-module stratifications. None is this statement.
- `grep -rn` of the exact item id in `lean/WeilConjectures`: no hits.
  `rg` of `galois_invariant|clopen_partition` in `dag/lean_names_upstream.json`
  and `lean/Sheaf` likewise found no exact match.
- The proposed full declaration name is new; no private copy of a notion is made.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q82

Author's self-check, not an independent review: I reopened the node and the file
and checked each correspondence above against their actual text. In particular,
`IsGalois` includes algebraicity and splitting of every minimal polynomial,
not merely an automorphism group; the action is the exact recorded canonical
base-change action; both invariant subsets are quantified, and uniqueness is
of the whole ordered pair via a single `∃!`. Both nonemptiness assertions,
both clopenness assertions, disjointness, covering and both preimage equalities
appear in the conclusion. No extra scheme hypothesis or degree bound appears.
The docstring supplies all four recorded proof steps and names all three proof
dependencies. No mismatch or correction resulted from this check. The
maintainer's independent delivery review remains the independent reading.

Validation: `scompile.py Q82 lem-trf-galois-invariant-clopen-partition-descent`
compiled this file in sandbox and library module forms, exit 0, with no compiler
errors or warnings (15.4 s and 4.9 s respectively). All lines are at most 100
characters. An exact-name rg across Mathlib and both project roots found no
existing declaration with the proposed full name.
