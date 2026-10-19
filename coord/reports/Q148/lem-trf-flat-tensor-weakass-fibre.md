## Worker report

States Stacks Project Tag 05IG, lemma-weak-bourbaki-pre (flat.tex, lines 3751–3774),
specialized to N=S. Its finite presentation over S is automatic (free rank one).
The single theorem has proof `sorry`; no definitions, auxiliary axioms, new nodes,
or dependency repairs are introduced. The item's sole changed field is `lean`.
The theorem docstring includes all thirteen proof steps from the node, with the
DAG dependency references, including the forward-implication-before-reverse order.

Clause-by-clause correspondence:

- Commutative rings and the map R→S: `(R : Type u) [CommRing R]`,
  `(S : Type v) [CommRing S] [Algebra R S]`; the map is `algebraMap R S`.
  An arbitrary ring map is represented by its `toAlgebra` instance.
- Finite presentation: `[Algebra.FinitePresentation R S]`.
- Flatness: `[Module.Flat R S]`, equivalent to flatness of the algebra map
  by `RingHom.flat_algebraMap_iff`.
- Arbitrary R-module: `(M : Type w) [AddCommGroup M] [Module R M]`.
  Its universe is independent of both ring universes. No finite generation,
  Noetherian, nontriviality, localness, or faithful flatness hypothesis is added.
- Prime p and prime q contracting to p: `p : PrimeSpectrum R` and
  `q : {q : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q = p}`.
  Quantifying over this subtype is exactly quantifying over all primes of S
  with the indicated contraction; it is not an extra restriction on q.
- Weak association means minimality over the annihilator of one element.
  `((⊥ : Submodule R M).colon {m}).minimalPrimes` renders this on the base.
  `Submodule.mem_colon_singleton` identifies the colon with `{a | a • m = 0}`;
  `Ideal.IsMinimalPrime` and `Ideal.minimalPrimes` impose precisely prime
  minimality among primes containing that ideal, without a radical-equality
  or exact-annihilator substitution.
- On the left, the witness is literally `z : M ⊗[R] S`. The colon is taken
  in `S ⊗[R] M` at `TensorProduct.comm R M S z`. This is exactly its
  S-annihilator through the second factor: swapping sends `m ⊗ s` to
  `s ⊗ m`, and first-factor multiplication by t corresponds to
  `m ⊗ (t*s)`. The swap is an additive bijection and preserves zero, so
  it neither adds a hypothesis nor changes the annihilator or its minimal
  primes. This uses the canonical Mathlib construction, not an arbitrary
  map or an additional module structure hypothesis.
- C and its residue field: `p.asIdeal.Fiber S` is Mathlib's
  `p.asIdeal.ResidueField ⊗[R] S`; `Ideal.ResidueField` is the residue field
  of `Localization.AtPrime p.asIdeal`. This is the mandated fibre convention,
  canonically swapping the source's tensor order. The map from S becomes
  `Algebra.TensorProduct.includeRight`.
- The corresponding fibre prime is
  `(PrimeSpectrum.preimageOrderIsoFiber R S p q).asIdeal`.
  The inverse of the recorded order isomorphism contracts along includeRight,
  so this is precisely the unique prime contracting to q.
- The right-hand fibre clause is membership in
  `RingTheory.annihilatorAssociatedPrimes (p.asIdeal.Fiber S) (p.asIdeal.Fiber S)`.
  This is the dependency's exact-annihilator definition, not Mathlib's
  radical-annihilator associated-prime predicate on an arbitrary ring.
- `↔` and `∧` render both directions and both simultaneous conditions.

Statement dependencies read and used:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`,
  `RingHom.flat_algebraMap_iff`, and its imported `Module.Flat`.
- `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`:
  `RingTheory.annihilatorAssociatedPrimes`. The older local source lacks
  this file; its complete live source was read via `scompile.py --source`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`:
  `PrimeSpectrum.preimageOrderIsoFiber`, `PrimeSpectrum.preimageEquivFiber`,
  `Ideal.Fiber`, and `Algebra.TensorProduct.comm`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`:
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`,
  `LinearMap.rTensor`, and `TensorProduct.comm`.

The recorded non-Mathlib proof modules `WeakAssLocalization`,
`AnnihilatorEqIffMinimalPrimeOfFG`, `LocalUniversalInjectiveResidue`, and
`ProjectiveOverLocalFree` are ordinary proof imports. Mathlib proof imports
cover associated-prime finiteness, exact localization, unramified local rings,
etale and flat morphisms, faithful flatness, and prime-spectrum topology.
The proof-only nodes `lem-trf-flat-algebra-etale-projective-neighborhood`,
`lem-trf-etale-weakass-invariance`, and
`lem-trf-nil-local-projective-injection-pure` have no recorded module on the
read base, so there is no module to import for them. They are not statement
prerequisites; this statement needs none of their data. No import cycle was added.

Edge cases checked:

- M=0: every element annihilator is top; top has no prime minimal above it,
  so the left and base weak-association conditions are both false.
- S=0 (or R=0): there is no q in the displayed prime subtype, so no invalid
  residue field or nontriviality assumption is imposed.
- R=S and the identity algebra: each fibre is a residue field, whose zero
  prime is the annihilator of 1; the equivalence becomes the identity case.
- Over a field the fibre is the algebra itself: every nonzero base module
  has zero weakly associated and the fibre is Noetherian by finite presentation;
  the result agrees with the usual associated-prime description of a free sum.
- Non-Noetherian R, infinitely generated M, and three different universes
  remain admitted. There is no restriction on characteristic or module rank.
- Empty finite selections and zero generator lists occur only in the proof;
  the copied proof explicitly handles their empty product and zero target.

Searches for an existing statement/definition:

1. `msearch.py ... leanfinder` queried “Weakly associated primes of a module
   tensor a flat finitely presented algebra are characterized by weak association
   on the base and associated primes of the fibre”: eight hits, concerning flat
   tensors, free loci, regular sequences and associated-prime localization;
   none states the theorem.
2. `msearch.py ... loogle 'weaklyAssociatedPrimes, TensorProduct'`: zero hits,
   unknown identifier `weaklyAssociatedPrimes`.
3. `msearch.py ... grep 'weak[Aa]ss|weaklyAssociated|WeaklyAssociated' RingTheory`:
   zero Mathlib hits.
4. `msearch.py ... leansearch` queried “Weakly associated primes of tensor
   products along flat finitely presented ring maps”: eight hits on regular
   sequences, faithfully flat tensor products, and flat kernels; no exact match.
5. `rg -n 'weak[Aa]ss|weaklyAssociated|WeaklyAssociated|lem-trf-flat-tensor-weakass-fibre'`
   in the named upstream and side sources: no upstream match; side hits included
   the ring-only `Ideal.WeakAss`, localization/finite-generation comparison
   lemmas, and the downstream `VerticalPrincipalIdealFibreDetection` proof text.
   Read the full weak-association and localization declarations. The ring-only
   definition cannot take arbitrary M, and the existing module localization
   statement uses exactly the same inline colon/minimalPrimes expression.
6. Searched the upstream declaration-name inventory and both source trees for
   tensor/weak-association theorem names: no existing matching declaration.
   The chosen full theorem name is absent from all these sources.

Validation: scompile.py compiled the sandbox and library forms separately,
cleanly (2.4 s and 1.9 s respectively); no unexpected warnings.
No statement dispute or node correction was needed.

## Second reading by Q148

A separate second pass by this worker reopened the node, source Tag 05IG and
final Lean signature. No other agent was started, as the dispatch brief expressly
forbids it; the maintainer supplies the independent delivery review.

The second pass checked every binder and conclusion again: commutative R and S,
arbitrary algebra map, finite presentation and flatness, arbitrary module M,
prime q over its contraction p, minimal-over-element-annihilator conditions on
both sides, and exact-annihilator association of the canonical fibre prime.
It checked that the left witness is M tensor S itself, that comm is used only
for its second-factor annihilator, and that the fibre swap carries the map from
S to includeRight. The order isomorphism's forward map is the residue-field
kernel and its inverse contracts to q, so no fibre prime is chosen arbitrarily.
It checked that all three universes are independent and no excluded zero,
non-Noetherian or infinite-module case appears. The proof is only sorry, and
all thirteen source proof steps are in its docstring. No mismatch was found and
no statement or dependency field was changed.
