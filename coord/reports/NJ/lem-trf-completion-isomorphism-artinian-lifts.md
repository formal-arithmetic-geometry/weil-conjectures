## Worker report

The module `Sheaf.RingTheory.CompletionIsomorphismArtinianLifts` states
`IsLocalRing.completion_isomorphism_artinian_lifts`, with a single `sorry` proof.
It introduces no definitions and changes only the item's `lean` field.

Hypothesis and conclusion correspondence, in the node's order:

- Nonzero commutative Noetherian local rings A and B: independent `Type u` and
  `Type v`, `CommRing`, `IsNoetherianRing`, and `IsLocalRing` instances.
  Mathlib's `IsLocalRing` extends `Nontrivial`, so nonzeroness is retained without
  an extra redundant binder. Their maximal ideals are `IsLocalRing.maximalIdeal`.
- The local homomorphism φ: `φ : A →+* B` and `[IsLocalHom φ]`.
  Mathlib's `IsLocalRing.local_hom_TFAE` identifies this predicate with equality
  of the inverse image of the target maximal ideal and the source maximal ideal.
- Completions: exactly `AdicCompletion (maximalIdeal A) A` and the analogous B
  ring. Their canonical maps are `algebraMap A (AdicCompletion ... A)` and
  its B counterpart; these are definitionally `AdicCompletion.of`.
  Coordinate projections are `(AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom`
  and its B counterpart, landing in `A ⧸ maximalIdeal A ^ n` and `B ⧸ ...`.
- The induced coordinatewise map is an isomorphism: `h` is a `≃+*` between
  these exact completion rings. `hcoord` specifies that if `x : A` represents
  coordinate n of z, φ x represents coordinate n of h z. Quotient surjectivity
  means this specifies every coordinate, hence exactly the induced completed
  homomorphism, rather than an arbitrary isomorphism commuting only on A.
  Conversely the coordinatewise induced map satisfies this condition. Packaging
  an isomorphism together with its defining coordinates introduces no extra
  mathematical hypothesis or choice. This also avoids introducing a duplicate
  completion-map construction.
- Nonzero commutative Artinian local C' and C: independent `Type w'` and `Type w`,
  `CommRing`, `IsLocalRing`, and `IsArtinianRing` instances. The latter means DCC
  on ideals, as it is Artinianity of the ring as its own module.
- Surjective homomorphism q: `q : C' →+* C`, `hq : Function.Surjective q`.
  No locality assumption on q is imposed; it follows in the proof.
- Local maps a and b: the corresponding `→+*` binders and `IsLocalHom` instances.
  Diagram compatibility is precisely `hab : q.comp a = b.comp φ`.
- Existence of positive exponents, nilpotence, and quotient factorizations is
  the first conjunct: `∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧ ...`, both maximal-ideal
  powers equal `⊥`, followed by existential ring homomorphisms `aBar`, `bBar`
  from the indicated quotients, with composites of quotient maps equal a and b.
- The phrase "for any such" is a separate universal second conjunct over
  every r, s satisfying the positivity and target nilpotence conditions and
  every aBar, bBar satisfying the two factorization identities. Thus the
  compatibility assertions are not limited to the existential witnesses.
- The completed maps are written explicitly as
  `aBar.comp (AdicCompletion.evalₐ (maximalIdeal A) r).toRingHom` and the B
  counterpart, throughout. No let-bound or arbitrary replacement map occurs.
- Their restriction identities are the first two conclusions under the
  universal quantifiers, composing with the canonical `algebraMap`s.
- Killing the powers of the extended maximal ideals is rendered by
  `(maximalIdeal A).map (algebraMap A (AdicCompletion ... A)) ^ r ≤ RingHom.ker ...`
  and the analogous B inequality. `Ideal.map` is precisely ideal extension,
  so these concern the extended ideals, not an unspecified completed maximal ideal.
- Compatibility of the two completed maps is the following equality of ring
  homomorphisms `q.comp (...) = (...).comp h.toRingHom`.
- The specified lift c is the explicit composite of the completed a-map,
  `h.symm.toRingHom`, and the canonical B completion map. The last three
  clauses assert `IsLocalHom` of precisely this map, its composite with q
  equals b, and its composite with φ equals a. No existential arbitrary lift
  replaces the formula required by the node.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, the exact recorded declaration.
- `def-weil-pbc-adic-completion`: `AdicCompletion` and `IsAdicComplete` in
  `Mathlib.RingTheory.AdicCompletion.Basic` (publicly imported through
  `Mathlib.RingTheory.AdicCompletion.Algebra`). Its compatible-sequence
  definition was read; the Algebra module supplies the ring structure,
  `algebraMap`, and `AdicCompletion.evalₐ`. This theorem uses the completion
  notion, without assuming either original ring already complete.
- Proof-only dependency `lem-weil-pbc-artinian-local-noetherian-nilpotent`:
  its recorded Mathlib match is imported without `public` from
  `Mathlib.RingTheory.HopkinsLevitzki`. The read signatures are
  `instIsNoetherianRingOfIsArtinianRing` and
  `isArtinianRing_iff_isNilpotent_maximalIdeal`. The proof docstring reproduces
  all five DAG proof steps, including the comparison at `max r s` and the
  locality argument using the inverse image of the maximal ideal under q.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-isomorphism-approximation` (Tag 0CAV), especially the first proof
paragraph identifying the induced completed stalk map and invoking Artinian
lifting to prove smoothness. This node is the explicitly extracted algebraic
sublemma, as its source record says, not the statement of the geometric tag.
No node correction, missing dependency interface, or disputed statement was found.

Edge cases checked before writing:

- Fields: maximal ideal zero permits exponent 1; the statement includes these
  rings and does not require a positive-dimensional or nonzero maximal ideal.
- Artinian rings need not be reduced; arbitrary positive nilpotence exponents
  are retained, including distinct r and s and exponents greater than minimal.
- Zero rings are excluded exactly as the node requests by `IsLocalRing`.
- Coordinate n = 0 is included in `hcoord`; its quotient is the zero ring and
  the coordinate condition is automatic, without affecting positive exponents.
- Identity φ/h/q and distinct ring universes are permitted. There is no
  extra continuity, finite-type, residue-field, algebra-structure, square-zero
  kernel, or same-universe hypothesis.
- The universal clause requires both factorizations; it neither asserts
  uniqueness of arbitrary ring maps from completions nor assumes continuity
  of such arbitrary maps. Only the displayed finite-coordinate maps occur.

Searches performed for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "An isomorphism of completions of local Noetherian rings gives compatible local homomorphism lifts to Artinian local rings"`:
  eight hits, including `IsAdicComplete.liftRingHom`,
  `IsAdicComplete.ofAlgEquiv_comp_liftRingHom`, and
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`;
  none states the compatible lifting theorem.
- `msearch.py ... loogle "AdicCompletion, RingHom, IsArtinianRing"`:
  zero hits.
- `msearch.py ... leansearch "local Artinian lifting across an isomorphism of completions"`:
  eight hits, including `RingEquiv.isArtinianRing`,
  `AdicCompletion.evalₐ_liftRingHom`, and `IsAdicComplete.liftRingHom`;
  no exact statement.
- `msearch.py ... grep "completion.*[Aa]rtinian|[Aa]rtinian.*completion" RingTheory`:
  zero hits in Mathlib.
- `rg -n 'completion.*[Aa]rtinian|[Aa]rtinian.*completion|lem-trf-completion-isomorphism-artinian-lifts' lean/WeilConjectures lean/Sheaf`:
  only an unrelated Artinian-completion comment in
  `CompletedMatchingRingMapResidueLift.lean`; no declaration for this node.
- `rg` for the new full-name components in `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.
  Direct searches and source reads in Mathlib's AdicCompletion, LocalRing,
  Noetherian, and Artinian modules found the exact component notions above.

Validation: `scompile.py NJ lem-trf-completion-isomorphism-artinian-lifts <file>`
compiled the sandbox and final module successfully in 2.1 s and 1.5 s, with
no errors or unexpected warnings. The initial obsolete `Artinian.Basic` import
was repaired to `Artinian.Defs`; a combining-character identifier was replaced
with `bBar`. All variables and universes are explicit and `autoImplicit` is false.

## Second reading by NJ

I reopened the node and the complete final module and performed a separate
clause-by-clause reading (the dispatcher forbids starting another agent; the
maintainer supplies the independent review). The first conjunct retains both
existence of the exponents and existence of the factorizations. The second
conjunct independently quantifies over every permitted pair of exponents and
factorizations and has eight conclusions: the two restrictions, two kernel
containments, compatibility with q, locality of the explicit inverse-completion
lift, and its two triangle identities. All hypotheses match the node; the
nonzero condition is inherited from each `IsLocalRing` instance. I checked
composition directions in both triangles and the power of `Ideal.map` in both
annihilation clauses. The representative-coordinate description of h fixes
the full map on every completion coordinate, including beyond the image of A.
No mathematical mismatch or change was found in this second reading.
