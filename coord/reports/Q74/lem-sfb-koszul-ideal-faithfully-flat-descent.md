## Worker report

Delivered statement: `Ideal.locally_koszulRegular_of_faithfullyFlat`, in
`Sheaf.RingTheory.KoszulIdealFaithfullyFlatDescent`.
Its only proof is `sorry`; no definitions, auxiliary claims, new nodes, dependency
repairs, or mathematical statement corrections are needed. All thirteen accepted
proof steps are transcribed into the declaration's source docstring.

The inherited BLOCKED ending concerned an already accepted stage-1 split. I read
brief-stage2 §0, the node, and its stage-2 queue row. The current node has no Lean
record; the Q104 `reviewed` record certifies stage 1, so this packet preserves that
split and supplies its missing stage-2 statement.

Source read: `literature/stacks-project/more-algebra.tex`, lines 8100–8125,
`definition-regular-ideal`, Tag 07CV(2), and lines 8174–8251,
`lemma-flat-descent-regular-ideal`, Tag 068N, including the Koszul-regular proof.
These agree with the item's expanded local formulation. No node fault or
STATEMENT-DISPUTED finding remains.

Hypothesis and clause correspondence:

- Commutative rings A and B: `{A : Type u} {B : Type v}` and the two `CommRing`
  instance binders. The universes are independent and explicitly declared.
- A faithfully flat homomorphism A → B: `[Algebra A B]` supplies the specified
  homomorphism `algebraMap A B`, and `[Module.FaithfullyFlat A B]` expresses its
  faithful flatness. Any commutative-ring homomorphism supplies this algebra via
  `RingHom.toAlgebra`; conversely its algebra map is the original homomorphism.
  This is the mandated STATE.md FAITHFULLY FLAT RING MAPS encoding, with no
  additional mathematical hypothesis.
- The ideal I: `(I : Ideal A)`. Its extended ideal IB is exactly
  `I.map (algebraMap A B)`: Ideal.map is defined as the ideal span of the image,
  not merely the set-theoretic image (Ideal/Maps.lean, lines 41–44).
- Every prime q containing IB: `∀ q : Ideal B, q.IsPrime →
  I.map (algebraMap A B) ≤ q →` in `hlocal`.
- A principal neighbourhood outside q: `∃ g : B, g ∉ q ∧ ...`.
- A finite sequence in B_g: `∃ r : ℕ, ∃ f : Fin r → Localization.Away g, ...`.
- Its Koszul-regularity: `RingTheory.Sequence.IsKoszulRegular f`, whose full
  definition is vanishing of all nonzero natural-degree homology of the
  canonical Koszul chain complex. Negative degrees are zero by convention.
- Its generation of (IB)B_g: `Ideal.span (Set.range f) =
  (I.map (algebraMap A B)).map (algebraMap B (Localization.Away g))`.
- Every prime p containing I in the conclusion: `∀ p : Ideal A,
  p.IsPrime → I ≤ p →`.
- A principal neighbourhood outside p: `∃ h : A, h ∉ p ∧ ...`.
- A finite Koszul-regular sequence in A_h generating IA_h: the existential
  `r : ℕ` and `f : Fin r → Localization.Away h`, followed by
  `RingTheory.Sequence.IsKoszulRegular f ∧ Ideal.span (Set.range f) =
  I.map (algebraMap A (Localization.Away h))`.
- Empty sequences and zero rings: no `0 < r`, `Nonempty (Fin r)` or
  `Nontrivial` assumption. No Noetherianity, finite presentation, finite
  generation, proper-ideal, domain, or fixed-rank hypothesis is added.

Dependency declarations read and used:

- `def-weil-pbc-faithfully-flat-ring-map`:
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`,
  class and full docstring at lines 59–65, and
  `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` at lines 424–433.
  The latter identifies this class with the node's exactness-test formulation.
  I also read the alternate recorded `RingHom.FaithfullyFlat` definition and
  docstring in `Mathlib.RingTheory.RingHom.FaithfullyFlat`, lines 24–34.
- `def-weil-pbc-koszul-regular-sequence`:
  `WeilConjectures.RingTheory.KoszulRegularSequence`,
  `RingTheory.Sequence.IsKoszulRegular`. I read the complete module and all four
  recorded definitions, including the tensor-with-module forms. The ring-only
  clause is the one this statement uses; its module is publicly imported.
- `def-weil-ring-localization-away`:
  `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away` at lines
  137–143, quotient by `Submonoid.powers`. I read its definition and docstring,
  and `IsLocalization.Away` at lines 47–51 of
  `Mathlib.RingTheory.Localization.Away.Basic`; that latter module publicly
  imports the ring structure and canonical algebra map needed here.

Every already stated proof dependency is imported without `public`; the proof
plan cites all dependency ids. `lem-sfb-koszul-equal-length-generators` has no
Lean record or usable Mathlib match in this snapshot, and is omitted from imports
until stated. It is only a proof dependency, so does not obstruct stating this
node. No other proof dependency was omitted. No import cycle is introduced by
an unstated parent.

Edge cases checked before writing: I=A makes both quantified loci empty;
A=0 has no primes and the conclusion is vacuous. Faithful flatness excludes a
map from a nonzero A to the zero ring B, rather than allowing a vacuous upstairs
condition to force an incorrect conclusion. For I=0 the empty tuple is permitted,
h=1 gives the expected downstairs neighbourhood, and its Koszul complex is
concentrated in degree zero. For a principal nonzerodivisor ideal the length-one
case gives exactly the usual Koszul local generation. Product rings permit
different lengths on different principal neighbourhoods; the quantifier order
does not demand a common length. Arbitrary, non-Noetherian commutative rings
remain in scope.

Searches actually run through `msearch.py Q74` for this item:

- LeanFinder: “Faithfully flat descent of ideals locally generated by finite
  Koszul regular sequences”: eight hits, chiefly
  `RingTheory.Sequence.IsRegular.of_faithfullyFlat`, weak regular sequence
  ascent, generic faithfully-flat injectivity/surjectivity descent and module
  flatness locality. None asserts local Koszul-regular generation descent.
- Loogle: `"Koszul", "FaithfullyFlat"`: zero hits.
- Mathlib grep: `Koszul|koszul|RegularIdeal` in RingTheory: one hit,
  Regular/RegularSequence.lean:21, a TODO for Koszul regular sequences.
- LeanSearch: “An ideal locally generated by Koszul regular sequences descends
  along a faithfully flat ring homomorphism”: eight hits, ordinary regular
  sequence ascent, generic descent/locality, ideal contraction, and lying over;
  none supplies this statement. The full source of the ordinary regular
  sequence result is in Mathlib/RingTheory/Regular/Flat.lean, and differs in
  both regularity notion and conclusion.
- Local project `rg -n` for `IsKoszulRegular` and Koszul descent/faithfully-flat
  combinations in both `lean/WeilConjectures` and `lean/Sheaf` finds regularity
  definitions, conormal comparisons, duality and flat ascent, but no local ideal
  descent statement. `grep -rn` for this node id in `lean/WeilConjectures` has
  no hit. Exact proposed declaration-name search in both Lean roots and
  `dag/lean_names_upstream.json` has no hit.

Validation: the prescribed `scompile.py Q74` server check passed for this module
in sandbox and library modes, with no errors or unexpected warnings. Source
checks find one named theorem with one `sorry`, no new definitions, no local or
private statement dependencies, explicitly bound universes and variables, and a
maximum line length of 98. The node copy changes only `lean`.

The first `deliver2.py --no-push` compiled successfully and found one metadata
mismatch: this preflight's signature extractor excludes the `:=` terminator.
I removed that terminator from `lean.statement`, retaining the exact signature
text before it; no Lean or mathematical change was needed. The final dry run
validates that repaired packet before delivery.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
