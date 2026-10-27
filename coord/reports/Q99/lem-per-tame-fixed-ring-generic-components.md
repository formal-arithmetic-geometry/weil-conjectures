## Worker report

The module `Sheaf.RingTheory.TameFixedRingGenericComponents` states
`FixedPoints.tame_fixed_ring_generic_components`, with one `sorry` and no new
definitions. The node's mathematical statement and dependencies are unchanged.
The source read is ILO, Travaux de Gabber, Exposé IV, Proposition 2.2.3 and its
proof, printed pp.53–54, and paragraph 2.2.4. The module docstring carries all
eight reviewed DAG proof steps and their cited nodes.

Hypotheses, matched individually:

- The commutative ring is `(C : Type u) [CommRing C]`.
- Nonzero and local are `[IsLocalRing C]`: this class already implies
  `Nontrivial C`. An explicit redundant `Nontrivial C` binder was removed after
  the server's overlapping-instances warning. The nonzero case remains required.
- Reduced is `[IsReduced C]`, not a domain assumption; multiple minimal primes
  remain allowed.
- Noetherian is `[IsNoetherianRing C]`.
- Completeness for the maximal ideal is
  `[IsAdicComplete (IsLocalRing.maximalIdeal C) C]`, including separatedness.
- Characteristic p > 0 is `(p : ℕ) [CharP C p] (hp : 0 < p)`.
- The finite dimension e ≥ 1 is `(e : ℕ) (he : 1 ≤ e)` and
  `hdim : ringKrullDim C = e`; finite natural dimensions are coerced into
  `WithBot ℕ∞`, preserving Mathlib's zero-ring and infinite-dimension conventions.
- Equidimensionality is `hequidim : ∀ q : Ideal C, q ∈ minimalPrimes C →
  ringKrullDim (C ⧸ q) = e`, exactly the node's definition.
- The finite group is `(H : Type v) [Group H] [Finite H]`, independently sized
  from C. Its action by ring automorphisms is `[MulSemiringAction H C]`.
  Each group element acts invertibly, and any automorphism of a local ring
  preserves its unique maximal ideal; no extra locality or faithfulness
  hypothesis is imposed.
- Tameness is `htame : IsUnit (Nat.card H : IsLocalRing.ResidueField C)`.
  It is imposed in k, as in the node, rather than silently moved to C.
- The named fixed subring B is `(B : Subring C)` with
  `hB : B = FixedPoints.subring C H`. This is an explicit name for the exact
  canonical subring, not an arbitrary invariant subring assumption. The theorem
  specializes to that canonical subring with `hB := rfl`.

Conclusions, matched individually:

- Reduced B: `IsReduced B`.
- Noetherian B: `IsNoetherianRing B`.
- Module-finite canonical inclusion B ↪ C: `Module.Finite B C`, using the
  subring's existing algebra structure, whose algebra map is `B.subtype`.
- Locality of B is the existential `∃ _ : IsLocalRing B, ...`. The witness is
  the actual local-ring property; subsequent terms use that witness as an
  instance. This avoids assuming a conclusion as a binder.
- Its maximal ideal is exactly n = m ∩ B:
  `IsLocalRing.maximalIdeal B =
  (IsLocalRing.maximalIdeal C).comap B.subtype`.
- Its n-adic completeness is
  `IsAdicComplete (IsLocalRing.maximalIdeal B) B`, interpreted using the preceding
  equality, and including the intersection-of-powers condition.
- Put k = `IsLocalRing.ResidueField C`. Mathlib's existing induced
  `MulSemiringAction H k` is used, via `ResidueField.mapAut`; it satisfies
  `residue C (h • c) = h • residue C c`.
- Put λ = `FixedPoints.subfield H k`. The canonical residue-field identification
  is `∃ f : IsLocalRing.ResidueField B ≃+* λ, ∀ b : B,
  (f (residue B b) : k) = residue C (b : C)`. The formula on every representative
  specifies precisely the inclusion-induced map B/n → k and fixes f uniquely;
  this is not a bare assertion of an unspecified field isomorphism.
- Finiteness and separability of k/λ are `Module.Finite λ k` and
  `Algebra.IsSeparable λ k`, with the existing subfield-inclusion algebra.
- Contraction takes every minimal prime to a minimal prime:
  `∀ q : Ideal C, q ∈ minimalPrimes C →
  q.comap B.subtype ∈ minimalPrimes B`.
- It is onto on minimal primes:
  `∀ r : Ideal B, r ∈ minimalPrimes B →
  ∃ q : Ideal C, q ∈ minimalPrimes C ∧ q.comap B.subtype = r`.
- Each component clause quantifies over `q : PrimeSpectrum C` with
  `q.asIdeal ∈ minimalPrimes C`, so the required prime instances are available
  without adding any hypothesis. This quantification includes every minimal
  prime ideal, since such ideals are prime.
- For r = q ∩ B the dimension clause is
  `ringKrullDim (B ⧸ q.asIdeal.comap B.subtype) = e`; the equality with
  `ringKrullDim (C ⧸ q.asIdeal)` is supplied by the already-bound `hequidim`.
- Component fraction fields use `(q.asIdeal.comap B.subtype).ResidueField` and
  `q.asIdeal.ResidueField`. The pinned Mathlib source
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` defines these and provides
  `IsFractionRing (R ⧸ I) I.ResidueField` at lines 108–125. They are exactly
  Frac(B/r) and Frac(C/q), not the original local ring's closed residue fields.
- The component extension algebra `a` is existentially bundled and constrained
  by the equality
  `algebraMap _ _ = Ideal.ResidueField.map
  (q.asIdeal.comap B.subtype) q.asIdeal B.subtype rfl`.
  Thus it is exactly the canonical map induced by inclusion and contraction;
  equality of algebra maps uniquely fixes the algebra structure. The following
  `Module.Finite` and `Algebra.IsSeparable` clauses use this same instance `a`.
  There is no unconstrained field embedding and no added algebra hypothesis.
- Finally `ringKrullDim B = e` and
  `∀ r : Ideal B, r ∈ minimalPrimes B → ringKrullDim (B ⧸ r) = e`
  state dimension and equidimensionality of B separately.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`:
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` (definition and its
  ideal-finiteness docstring at lines 195–206).
- `def-weil-pbc-adically-complete-ring`:
  `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete` (lines 44–56,
  extends Hausdorffness and precompleteness).
- `def-weil-pbc-krull-dimension-ring`:
  `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim` (lines 27–31).
- `def-weil-finitely-generated-module`:
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite` (lines 116–120).
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`
  (lines 95–99, canonical ring homomorphism and scalar action).
- `def-weil-pbc-separable-algebraic-extension`:
  `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable` (lines 533–550;
  algebraicity is included via separability of each minimal polynomial).

All six recorded statement-dependency modules are imported publicly. The stated
proof dependencies are imported without `public`, including trace-one invariant
finiteness, subideal completeness, fixed-field Galois theory, invariant prime
orbits, minimal primes, lying over, going up, dimension-zero localizations,
localization base change, Artinian decomposition and integral dimension equality.
The record for `lem-per-tame-invariants-arbitrary-base-change` points to the
withdrawn module `Sheaf.DeligneLaumon.TameInvariantsArbitraryBaseChange`; its
`lean.note` says it was deleted on 2026-10-20. A live-server source query using
`scompile.py --source` also returned `Module source unavailable`. This nonexistent
proof-only module is not imported; its DAG dependency and the proof step using
it are retained unchanged. It supplies no notion needed for this statement.

Searches actually run for this item:

- LeanFinder via msearch: “A tame finite group acting on a complete reduced
  equidimensional Noetherian local ring has complete local fixed ring and finite
  separable generic components”. Eight hits, including `FixedPoints.isSeparable`,
  `Ideal.Quotient.finite_of_isInvariant`, and arithmetic-Frobenius facts; no match
  for the full fixed-ring theorem.
- Loogle via msearch: `"FixedPoints", "IsLocalRing"`. Zero hits.
- Mathlib grep via msearch in RingTheory:
  `fixed.*(IsLocalRing|IsAdicComplete)|[Ii]nvariant.*(complete|noetherian)|[Rr]eynolds`.
  Three unrelated fully-invariant-submodule hits in SimpleModule/Isotypic.
- LeanSearch via msearch: “The fixed subring of a reduced complete Noetherian
  local ring under a tame finite group is complete local and finite with
  separable generic components”. Eight hits, including `FixedPoints.subring`,
  `IsGalois.of_fixed_field`, and unramified residue-field finiteness; no full match.
- Project rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for the node
  id, `fixed.*(IsLocalRing|IsAdicComplete)`, `tame_fixed`, `tameFixed` and invariant
  completeness/Noetherianity. The existing tame local regularity statement is
  about the fixed subscheme quotient, not the invariant subring. The upstream
  `WeilConjectures.RingTheory.Invariant.Etale` module was opened and its
  `Algebra.IsInvariant.isSeparable_of_mem_minimalPrimes` signature read: it gives
  the generic separability clause, not completeness, locality, finiteness,
  equidimensionality and the residue identification together. No exact existing
  declaration was found, and no existing notion is redefined.

Edge cases checked mathematically before writing and again against the signature:
trivial H and an arbitrary kernel of its action, multiple branches such as
F_p[[x,y]]/(xy) with the branch swap (p odd), and F_p[[x]] with x ↦ -x (p odd).
The first gives B = C, the second retains the stabilizer and faithful-image
argument, and the branch swap has one contracted minimal prime without assuming
C is a domain. Different actions on a nontrivial residue field remain permitted.
The zero ring is excluded by the node and by `IsLocalRing`; e = 0, characteristic
zero and wild group orders are excluded exactly as in the node. No irreducibility,
faithfulness, perfect residue field, coefficient field, flatness or continuity
assumption was added. Automorphisms preserve powers of the maximal ideal
and are therefore automatically continuous in the adic topology.

There are no new nodes, no dependency repairs, no statement correction and no
STATEMENT-DISPUTED issue. The supplied CompactObject example module has been
withdrawn; its current node points to the identical upstream definition. Its
record shape and current module conventions were followed.

Validation: the final server compilation succeeded for both the sandbox module
and its actual library module name, with no errors or warnings. Only the named
theorem's proof is postponed. Delivery preflight results are recorded below.

The prescribed `deliver2.py --no-push` completed successfully: the packet passed
live-server preflight and clean per-file compilation. Only the item's `lean`
field changed, and the Lean file has one theorem, one `sorry`, all universes
explicitly bound, `autoImplicit false`, and maximum line width 94.

## Second reading by Q99

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
