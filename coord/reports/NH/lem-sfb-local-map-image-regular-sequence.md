## Worker report

The module `Sheaf.RingTheory.LocalMapImageRegularSequence` states
`IsLocalRing.exists_isRegular_map_of_radical_map_maximalIdeal`, with `sorry` as
its entire proof. Source read: Stacks Algebra, Tag 06LC,
`lemma-find-sequence-image-regular`, including its prime-avoidance proof at
`literature/stacks-project/algebra.tex:25425`. No new definitions or nodes,
dependency repairs, or statement corrections are needed. Only the item's `lean`
record changes.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Two commutative rings | `{A : Type u} {B : Type v} [CommRing A] [CommRing B]` |
| Both local and nonzero | `[IsLocalRing A] [IsLocalRing B]`; this Mathlib class extends `Nontrivial` |
| Ring homomorphism | `(φ : A →+* B)` |
| Locality, explicitly the preimage equality | `hlocal : (maximalIdeal B).comap φ = maximalIdeal A` |
| Only B is Noetherian | `[IsNoetherianRing B]`; no finiteness assumption on A |
| Finite nonnegative dimension d | `(d : ℕ)` and `hdim : ringKrullDim B = (d : WithBot ℕ∞)` |
| Cohen--Macaulay, stated as equality | `hdepth : depth (R := B) B = (d : ℕ∞)` |
| Extended maximal ideal has the prescribed radical | `hradical : ((maximalIdeal A).map φ).radical = maximalIdeal B` |
| d selected source elements | `∃ as : List A, as.length = d` |
| All selected elements are in the source maximal ideal | `∀ a ∈ as, a ∈ maximalIdeal A` |
| Their ordered image is a regular sequence in B | `RingTheory.Sequence.IsRegular B (as.map φ)` |
| Empty sequence allowed at dimension zero | Length zero forces `as = []`; the regularity predicate permits the empty sequence on a nonzero module |

The independent ring universes `u v` allow arbitrary source and target sizes.
`Ideal.map` is exactly the ideal spanned by the set image, not the set image
itself (Mathlib `Ideal/Maps.lean:41-44`). `Ideal.comap` is the preimage ideal.
`Ideal.radical` uses powers with exponent in ℕ, which agrees with the node's
positive-exponent formulation: exponent zero can occur only if the ideal is the
unit ideal; then exponent one is also a witness for every element. Here the
extended ideal is proper in any event, by locality. No extra hypothesis is needed.

Statement dependencies used, with their source docstrings and signatures read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` (dimension of the ordered prime spectrum in `WithBot ℕ∞`).
- `WeilConjectures.RingTheory.Depth`: `IsLocalRing.depth`, built from `Ideal.depth` using regular-sequence lengths and the stated infinity convention. This is the exact recorded interface, with module argument B over itself.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`, extending injectivity on successive quotients by the condition that the final quotient is nonzero.

Proof dependencies are imported without `public`, except those already public
for the statement. The proof docstring expands all five steps of the node:
variable-ring dimension induction; finite associated primes and their
minimality; source prime avoidance; quotient induction preserving locality and
the radical condition; lifting the quotient regular sequence and prepending the
first element. The relevant recorded declarations are:

- `associatedPrimes.finite`, `Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness`;
- `biUnion_associatedPrimes_eq_zero_divisors`, `Mathlib.RingTheory.Ideal.AssociatedPrime.Basic` (available through the finiteness import);
- `Ideal.mem_minimalPrimes_of_depth_ge`, `WeilConjectures.RingTheory.AssociatedPrimeMinimalOfDepth`;
- `Ideal.subset_union_prime`, `Mathlib.RingTheory.Ideal.Operations`;
- `IsLocalRing.depth_quotient_nonzerodivisor`, `WeilConjectures.RingTheory.DepthQuotientNonzerodivisor`;
- quotient structure from `Ideal.Quotient.nontrivial_iff`, `IsLocalRing.of_surjective'`, `IsLocalRing.map_maximalIdeal_of_surjective`, and `IsLocalHom.of_surjective`, in the recorded Mathlib quotient/local-ring modules.

Edge cases checked mathematically before writing: dimension zero (including a
field target) uses the empty sequence; a nonreduced Artinian target is allowed;
dimension one uses one element and a nonzero quotient; the identity map is
included; a non-Noetherian source is allowed. The zero ring is excluded exactly
as in the node by `IsLocalRing`'s nontriviality field. The statement uses equality
of depth and dimension, as the node requests, even though the induction proof
uses the stronger theorem with a depth lower bound. There are no node faults or
STATEMENT-DISPUTED findings.

Searches actually run through `msearch.py NH lem-sfb-local-map-image-regular-sequence`:

- LeanFinder: `A local homomorphism into a Noetherian Cohen Macaulay local ring with maximal primary extended maximal ideal admits an image regular sequence of length its dimension`. Eight hits: localization/flat transport and dimension formulas for supplied sequences; no source-image selection theorem.
- Loogle: `"IsRegular", "IsLocalRing"`. Seven hits: permutations, weak versus ordinary regularity, depth suprema, and regular-local instances; none selects a sequence in a ring-map image.
- Mathlib grep (RingTheory): `exists.*regular.*sequence|Cohen.?Macaulay|find.*sequence.*image`. Three hits, all in `Depth/Rees.lean`. Its `ModuleCat.exists_isRegular_of_exists_subsingleton_ext` (lines 63ff read) chooses a sequence in an ideal under Ext vanishing; it does not choose elements of a specified ring-map image.
- LeanSearch: `A local homomorphism into a Cohen Macaulay Noetherian local ring with radical of the extended maximal ideal equal to the target maximal ideal admits a regular sequence of length the target dimension in the image`. Eight hits: locality characterization, regularity definition, transport, and dimension formulas, without the required selection assertion.
- `rg` in both project roots: `lem-sfb-local-map-image-regular-sequence|exists.*regular.*sequence|find.*sequence.*image` returned no existing assertion for this node.
- `rg` in both project roots and `dag/lean_names_upstream.json` for `local.*[Ii]mage.*[Rr]egular|exists_isRegular.*[Ii]mage|exists_regular.*[Ii]mage|lem-sfb-local-map-image-regular-sequence` returned only unrelated prose about images of already chosen parameters.
- Exact proposed declaration name `exists_isRegular_map_of_radical_map_maximalIdeal` was searched throughout Mathlib, both project roots and the upstream declaration inventory, with no match.

Validation: `scompile.py NH lem-sfb-local-map-image-regular-sequence` compiled the
delivered module in sandbox and library positions, each in 1.3 seconds, without
errors or unexpected warnings. All variables and universes are explicit and
`autoImplicit` is disabled.

## Second reading by NH

Author's second reading (the dispatcher brief forbids starting other agents):
reopened the node and the completed module and compared every binder and each
conjunct in the table above. Both local-ring classes enforce nonzeroness; only
the target has a Noetherian instance. The locality equality is exactly the node's
equality, and the extended ideal uses `map`, not the raw image. The depth binder
is equality, preserving the stated hypothesis rather than replacing it with a
lower bound. The list is in A, its membership assertion is in the maximal ideal
of A, its length is exactly d, and regularity is asserted for the mapped list on
B. No extra scalar/algebra structure is imposed on the map. Dimension zero and
independent universes remain covered. Found no mathematical mismatch; no Lean
statement changes were required after the first clean compile. The metadata
signature was checked to retain the named argument `R := B` verbatim.
