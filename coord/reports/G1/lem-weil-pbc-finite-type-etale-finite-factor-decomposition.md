## Worker report

The module `Sheaf.RingTheory.EtaleFiniteFactorDecomposition` states
`Algebra.exists_etale_finiteFactor_decomposition`, with proof `sorry`.
It defines no new notion. The node is unchanged except for its `lean` record.

Hypotheses and clauses, in the order of the node:

- Commutative rings and the map R → S: `{R : Type u} {S : Type v}`,
  `[CommRing R] [CommRing S] [Algebra R S]`; the map is `algebraMap R S`.
- Finite type: `[Algebra.FiniteType R S]`.
- A prime p of R: `(p : Ideal R) [p.IsPrime]`.
- An étale ring map R → R': existential `R' : Type u`, `CommRing R'`,
  `Algebra R R'`, and `Algebra.Etale R R'`.
- A prime P of R' lying over p: existential `(P : Ideal R')`, `P.IsPrime`,
  and `P.LiesOver p`. The last is exactly contraction along the algebra map.
- The induced residue-field map is an isomorphism: `Function.Bijective
  (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p))`.
  This is the canonical induced map, rather than an arbitrary field equivalence.
  Bijectivity of a field homomorphism is equivalent to being an isomorphism.
- The two R'-algebras: existential `A B : Type (max u v)`, with their
  `CommRing` and `Algebra R'` structures.
- The R'-algebra isomorphism: `Nonempty ((R' ⊗[R] S) ≃ₐ[R'] (A × B))`.
- A is a finitely generated R'-module: `Module.Finite R' A`.
- No prime of B over P is quasi-finite: `∀ q : PrimeSpectrum B,
  q.asIdeal.LiesOver P → ¬ IsQuasiFiniteAtPrime R' B q`.
  The existential `Algebra.FiniteType R' B` witness lets this predicate typecheck.
  It adds no mathematical restriction: B is a quotient of R' ⊗[R] S by projection
  through the product isomorphism, hence finite type by base change and quotients.

Dependencies read and used:

- `def-weil-pbc-finite-type-algebra`: Mathlib.RingTheory.FiniteType,
  `Algebra.FiniteType`, the finite generation of the top subalgebra.
- `def-weil-etale-morphism`: the recorded Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale` and its `HasRingHomProperty` instance were read.
  This node speaks of rings; following brief-stage2's ÉTALE RING MAPS convention,
  the statement uses Mathlib.RingTheory.Etale.Basic, `Algebra.Etale`.
- `def-weil-residue-field`: Mathlib.AlgebraicGeometry.ResidueField,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and `Spec.residueFieldIso`
  were read. In the affine ring setting the corresponding existing notions are
  Mathlib.RingTheory.LocalRing.ResidueField.Ideal, `Ideal.ResidueField` and
  `Ideal.ResidueField.mapₐ` (both signatures/docstrings read). The former is the
  residue field of the localization at the prime; `Spec.residueFieldIso` identifies
  it with the recorded scheme residue field. No duplicate definition is needed.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`: imported
  Sheaf.RingTheory.QuasiFiniteAtPrime, `Algebra.IsQuasiFiniteAtPrime`, read in full.
  This tests the openness of the singleton corresponding fibre prime.

The imports are used: Etale.Basic supplies `Algebra.Etale`; QuasiFiniteAtPrime
supplies the required predicate and its residue-field/tensor-product infrastructure.
All universes and variables are explicitly bound. No auxiliary theorem or definition
is introduced. The theorem docstring carries all six proof steps and their nodes.

Source check: the local `literature/stacks-project/algebra.tex` is absent on this
machine, so the source was read at https://stacks.math.columbia.edu/tag/00UK.
The node explicitly combines the source's finite factors; it does not claim each
prime of the combined factor is unique. No statement correction or dispute arose.

Edge cases checked before writing:

- No isolated fibre points: A may be the zero ring, B = S and R' = R.
  No `Nontrivial A` or `Nontrivial B` assumption excludes this case.
- Empty fibre: the condition on primes over P is vacuous; the same base case works.
- Entirely finite S: B may be the zero ring; the final universal condition is vacuous.
- A zero source ring admits no prime p, so the hypothesis itself rules that case out.
- Over a field k, S = k[x] × k has the finite factor k and complementary k[x].
  A non-closed generic prime of the fibre is not an isolated point.
- The two independent input universes u and v are allowed. R' can be chosen in u
  as in Mathlib's 00UJ theorem; the factors fit in max u v as quotients of the tensor
  product. This is a size choice for existential representatives, not a finiteness
  or nonemptiness assumption. No characteristic assumption is present.

Searches for an existing statement (msearch.py with this group/item):

- LeanFinder: "finite type algebra etale base change splits as finite algebra and
  algebra with no quasi finite primes in fibre". Eight hits included base-change
  and composition results, the field étale product criterion, and the one-prime
  splitting lemma; none states simultaneous finite-type factor decomposition.
- Loogle: "Algebra.FiniteType, Algebra.Etale, Module.Finite". One hit:
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, the 00UJ result
  requiring a selected quasi-finite prime, not this 00UK conclusion.
- msearch grep: "00UK|exists_etale.*prod|exists_etale.*finite" under RingTheory.
  Zero hits reported. Direct source inspection of Etale/QuasiFinite.lean read the
  00UJ and 00UL declarations and their docstrings: 00UL requires Module.Finite,
  whereas this theorem only assumes finite type.
- LeanSearch: "finite type algebra etale neighborhood decomposition finite factor
  no quasi finite primes". Service unavailable: Internal Server Error.
- rg in WeilConjectures and lean/Sheaf:
  "00UK|etale.*finite.*factor|etale.*decomposition|exists_etale". Nearby results
  include geometric-point finite-algebra splittings, finite sections, and étale
  residue-field constructions; no exact statement. rg for the item id in
  WeilConjectures produced no hits.
- rg for "exists_etale_finiteFactor_decomposition|EtaleFiniteFactorDecomposition"
  in dag/lean_names_upstream.json, Mathlib, WeilConjectures and lean/Sheaf:
  no hits; the proposed declaration/module names are unused.

Validation: the server scompile.py invocation passed with exit code 0 in 1.5 s,
without warnings. The first invocation exposed a missing tensor-product notation
scope; `open scoped TensorProduct` fixed it. The deliver2.py --no-push dry run printed OK: compilation and preflight pass,
except for the independent second reading that the second reader must supply.
Nothing was pushed.

## Second reading by G1

I independently opened the DAG node and `Sheaf.RingTheory.EtaleFiniteFactorDecomposition.lean` and
matched the statement in order.

- The node's finite-type ring map (R\to S) is rendered by `{R : Type u} {S : Type v}`,
  `[CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]`.
  No Noetherian, characteristic, nontriviality, or separatedness hypothesis is added.
- The chosen prime [0mp[0m is `(p : Ideal R) [p.IsPrime]`, exactly one prime ideal as in the node.
- The étale extension is the existential `R' : Type u` with `CommRing R'`, `Algebra R R'`,
  and `Algebra.Etale R R'`; this is the ring-map notion named by the dependency convention.
- The prime over it is `(P : Ideal R') [P.IsPrime] [P.LiesOver p]`, with no extra condition.
- The residue-field clause is exactly
  `Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p))`,
  so it uses the canonical induced map rather than an arbitrary equivalence.
- The factors are `A B : Type (max u v)` with their `CommRing` and `Algebra R'` instances,
  followed by `Nonempty ((R' ⊗[R] S) ≃ₐ[R'] (A × B))`, exactly the stated product isomorphism.
- `Module.Finite R' A` renders that (A') is a finitely generated (R')-module.
- The final clause is
  `∀ q : PrimeSpectrum B, q.asIdeal.LiesOver P → ¬ IsQuasiFiniteAtPrime R' B q`,
  which is precisely “not quasi-finite at every prime of (B') over (P)”.

The Lean binder `_ : Algebra.FiniteType R' B` appears immediately before the conjunction.
This is required to make the project's recorded predicate `IsQuasiFiniteAtPrime R' B q`
well-typed (its definition has `[Algebra.FiniteType R' B]`); it is not an additional
mathematical restriction, since the product decomposition makes the complementary factor
finite type. The conjunction order and all quantifier scopes otherwise agree verbatim with
the node. Universes permit the node's independent (u,v), while factors use `max u v` and
(R') uses (u), so no covered case is excluded.

Edge cases checked: the empty quasi-finite locus is covered by `A = 0, B = S`; the zero
factor is allowed (no `Nontrivial` assumptions); an empty fibre makes the final universal
vacuous; (n=0) polynomial presentations and every characteristic remain allowed; a zero
source ring has no prime hypothesis and is therefore correctly vacuous. The residue-field
map is still the identity in the base case.

I repeated the existing-definition searches with LeanFinder, Loogle, LeanSearch, and `rg` in
Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`. They found only
the one-prime 00UJ idempotent theorem and general base-change results, not this simultaneous
00UK decomposition. The dependency declarations (`Algebra.FiniteType`, `Algebra.Etale`,
`Ideal.ResidueField.mapₐ`, and `Algebra.IsQuasiFiniteAtPrime`) were opened and are the ones
used by the module; no private duplicate or missing dependency was found.

No mismatch required a code or node repair. The module compiles cleanly with `scompile.py`,
and the only delivery change in this second reading is this report section.
