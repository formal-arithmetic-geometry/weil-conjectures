## Worker report

This is a stage-2 delivery for lem-trf-pointed-etale-henselization-isomorphism, not a
stage-1 re-split. The live node has Q151's accepted split but no Lean record; its queue
entry is stage 2. The standing brief §0 explicitly permits this handoff. The inherited
unchanged-item stage-1 refusal therefore does not apply. No repair note is present.
The accepted statement, dependencies, proof, proof dependencies, and review are preserved;
only `lean` is added. No new or dependency nodes are needed.

Module: `Sheaf.RingTheory.PointedEtaleHenselizationIsomorphism`.
All three theorems have `sorry` proofs. The only definition,
`Algebra.ordinaryHenselizationBaseMap`, is the actual composition of the two structural
ring maps; it is neither a chosen arbitrary map nor a second henselization definition.

Hypothesis and clause correspondence:

- Commutative rings and the étale homomorphism: `(A : Type u) (C : Type v)`, both
  `CommRing` instances, `(φ : A →+* C)`, and `(_hφ : φ.Etale)`.
- Prime ideals and preimage: `(p : Ideal A) [p.IsPrime]`, `(q : Ideal C) [q.IsPrime]`,
  and `(hp : p = q.comap φ)`. Thus the zero ring has no admissible input prime.
- The given induced residue-field isomorphism is bijectivity `hres` of exactly
  `Ideal.ResidueField.map p q φ hp`. Its inverse below is the inverse of
  `RingEquiv.ofBijective` applied to this very map.
- Ordinary henselizations exist for each local ring: apply
  `Algebra.exists_ordinaryHenselization_atPrime` to `(A,p)` and `(C,q)`.
  Its existential ring, algebra structure and henselian-local structure are followed
  by the recorded `IsHenselizationAtPrime'` predicate, with no extra assumption.
- The pair henselization uses exactly the full subcategory in the recorded
  `RingTheory.pair_henselization`: étale maps out of `Localization.AtPrime p` whose
  structural maximal-ideal quotients are bijective, and all under-category morphisms.
  `Algebra.pairColimit_isOrdinaryHenselization` quantifies over any colimit cocone of
  this diagram and concludes a henselian-local structure, equality of its maximal
  ideal with the extended maximal ideal, bijectivity of the structural quotient map,
  and `IsHenselizationAtPrime'` for the cocone's exact structural algebra. Locality and
  the universal property are the two conjuncts of that predicate. Applying this
  theorem to `(C,q)` gives the second pair assertion.
- Arbitrary choices: `(H : Type w) (K : Type x)` with their actual localized algebra
  and henselian-local structures and only `_hH`, `_hK`, using the recorded predicate.
  The four ring universes are independent. Existence is separately supplied in the
  base ring's universe; the comparison accepts any larger or differently sized model.
- Maximal ideals and unchanged residues for these arbitrary choices: the first two
  conjuncts are precisely the maximal-ideal extension equalities. The existential
  `eH` and `eK` are residue-field isomorphisms; the following equalities with
  `IsLocalRing.residue` ensure these are the structural isomorphisms, not unrelated ones.
- The canonical local comparison is `e.toRingHom`, for `e : H ≃+* K`.
  Its locality, its extension equation through `Localization.localRingHom p q φ hp`,
  and uniqueness among all local maps satisfying this equation are explicit.
  This states that the unique initiality map is an isomorphism without introducing
  a gratuitous noncanonical comparison construction.
- Inverse characterization: `f : C →+* H` is an `A`-map by `f.comp φ =
  ordinaryHenselizationBaseMap A p H`. Its maximal-ideal preimage is exactly `q`.
  Its residue equation is the inverse given residue isomorphism followed by `eH`.
  The quantified `f'` clause states uniqueness with exactly these properties.
  The equation `e.symm.toRingHom.comp (ordinaryHenselizationBaseMap C q K) = f`
  is the claimed inverse restriction. Localization and initiality then uniquely
  characterize its extension from `C_q` to `K`.
- Every ideal: `∀ (I : Ideal A), I ≤ p → ...`; no finite generation is required.
  `JH` and `JK` are forced to be respectively `I.map` of the structural map and
  `(I.map φ).map` of the other structural map. `JH.map e.toRingHom = JK` is the
  requested equality of the extended ideals.
- The quotient isomorphism is `E : (H ⧸ JH) ≃+* (K ⧸ JK)`. Its equality after
  composition with `Ideal.Quotient.mk JH` fixes it to the map induced by `e`.
- Structure maps from both quotient bases: `a : A/I → H/JH`, `b : C/IC → K/JK`,
  `c : C/IC → H/JH` have their exact defining quotient equations. In particular
  `c` is induced by the pointed `f`. The equations `E.toRingHom.comp a =
  b.comp (Ideal.quotientMap ...)` and `E.toRingHom.comp c = b` are the two
  required commutative diagrams.
- Final ordinary henselization assertions use the actual image primes `p/I` and
  `q/IC` (with their primality concluded existentially), their Mathlib localizations,
  and `IsHenselizationAtPrime'`. The equations after the predicates tie the localized
  algebra structures to `a` and `b`. Thus no arbitrary unrelated henselization
  structure can satisfy this conclusion in place of the required one.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`, and the
  `HasRingHomProperty @Etale RingHom.Etale` instance; its ring-map notion `φ.Etale`
  is the authorized ring form of the node's étaleness.
- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`, `Algebra.IsHenselizationAtPrime'`:
  local structural map and uniqueness against henselian test rings in `Type (max u v)`.
  No private universal-property predicate is introduced.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded henselian terminology;
  `HenselianRing`, `HenselianLocalRing`, and `IsStrictlyHenselianLocalRing` signatures
  were read. Only ordinary henselian terminology is needed here.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` and
  `Localization.localRingHom`, including its local instance and fraction formulas.
- `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` were read. This ring-level statement uses their exact
  underlying ring notions `IsLocalRing.ResidueField`, `IsLocalRing.residue` and
  `Ideal.ResidueField.map` (in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`).
- `WeilConjectures.RingTheory.PairHenselization`, `RingTheory.pair_henselization`:
  its actual full subcategory and cocone interface are reused in the pair clause.
- Recorded proof imports: `Sheaf.RingTheory.PrimePairColimitIndEtaleModel`
  (`RingTheory.prime_pair_colimit_indEtale_model`),
  `Sheaf.RingTheory.InitialHenselianColimitComparison`
  (`Algebra.initial_henselian_colimit_comparison`),
  `WeilConjectures.RingTheory.MapIntoHenselianColimit`
  (`Algebra.map_into_henselian_colimit`), and
  `Sheaf.TraceFormula.HenselizationQuotientAtPrime`
  (`Algebra.henselization_quotient_at_prime`). These are plain proof imports, while
  statement dependencies are public imports.

Sources opened: algebra.tex `lemma-map-into-henselian` (08HQ, line 42601),
`definition-henselization` (04GQ, line 43125), `lemma-quotient-henselization`
(05WQ, line 43617); more-algebra.tex `lemma-henselization` (0A02, line 2980) and
`lemma-henselization-local-ring` (0A03, line 3109). The latest blueprint's locality
node was located; this lower algebraic item retains the historical supporting role
already recorded in its accepted split. No unit statement or route is changed.

Edge cases checked before finalizing: identity map; a field at its zero prime;
a localization A_s at a prime avoiding s; a split étale product A × A with one chosen
prime; I = 0; I = p; non-finitely-generated ideals; arbitrary residue characteristic;
independently sized ring carriers. The pointed-prime condition selects one product
factor. At I = 0 the quotient clauses reproduce the original comparison; at I = p
both quotient local rings are their original residue fields. No Noetherian or
finite-generation assumption appears. The forbidden I = A is excluded precisely
by I ≤ p and primality, as in the source.

Searches actually run (msearch.py, group Q48 and this item):

- LeanFinder: "An etale ring map with identical residue fields induces an isomorphism
  of ordinary henselizations compatible with quotients". Eight hits, including
  `RingHom.Etale.respectsIso`, standard étale lifting and `Algebra.Etale.of_equiv`;
  none constructs or compares ordinary henselizations or states the quotient clauses.
- Loogle: `"Henselization", "Etale"`. Zero hits.
- Mathlib grep in RingTheory: `henseli[sz]ation.*[Ee]quiv|[Ee]tale.*henseli[sz]ation`.
  Zero hits.
- LeanSearch: "Ordinary henselization of an etale local ring map inducing an
  isomorphism of residue fields is an isomorphism and commutes with quotient by
  ideals". Eight hits on residue-field maps, étale localization and henselian
  constructors; no matching theorem.
- `rg` on both live `lean/WeilConjectures` and `lean/Sheaf` for
  `pointed.etale.henselization|henselization.*[Ii]somorphism|henselization.*[Ee]quiv`:
  only unrelated strict-henselization material and pair flat quotients.
- `grep -rn` of the item id in `lean/WeilConjectures`: no result.
- `rg` of all four proposed declaration names in Mathlib, both project roots and
  `dag/lean_names_upstream.json`: no result. This is a new statement module, not a
  duplicate existing attachment.

No STATEMENT-DISPUTED finding and no statement correction.

## Second reading by Q48

Performed a separate in-thread rereading of the node and the complete module after
compilation; no other worker was started, as the dispatch expressly forbids agents.
The maintainer's independent delivery review is still required.

The first compiled draft put A,C,H,K in the same universe. On rereading the arbitrary
choices clause I generalized all four universes independently; the generalized file
also compiled cleanly. I checked that the exact recorded generalized henselization
predicate is used, including its common-size test rings. I checked that `hres` refers
to the map induced by φ rather than an arbitrary isomorphism, that the canonical
comparison's uniqueness is present, and that the inverse's pointed lift has its
residue condition and uniqueness, not just an A-linearity equation.

For the closed quotient clauses I read the final existential binders against each
word of the node: the ideals are exact extensions, E is induced by e, the C/IC map
to the left quotient is induced by f, both squares are present, and each localized
quotient algebra structure composes to the specified a or b. These checks found no
remaining missing clause or extra hypothesis. The pair-colimit clause is stated for
an actual colimit, not an arbitrary ring with unspecified relation to the pair
construction. Both existence and pair statements quantify over a single arbitrary
base, so they apply separately to both rings as the node requires.

No new nodes, dependency repairs, or statement changes are delivered. The only node
delta is its Lean attachment. All source lines are at most 100 characters; there
are no auto-bound variables, local notations, private declarations, hidden chosen
maps, or proof-bearing definitions. Each postponed theorem carries the matching
node id and the relevant part of its natural-language proof.
