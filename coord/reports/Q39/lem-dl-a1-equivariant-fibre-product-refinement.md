## Worker report

The module `Sheaf.RingTheory.EquivariantFibreProductRefinement` states
`Algebra.exists_equivariant_fibre_product_refinement`, with one postponed proof.
The node's statement, dependencies and proof plan are unchanged. No new definitions,
new nodes or dependency modules are needed. Source read: `pione.tex`, Tag 0BST,
`lemma-inertia-invariants-etale`, especially the paragraph beginning “It may not be
 the case that G permutes the factors”. The eight proof steps of the DAG are
included in the theorem's docstring.

The following matches every hypothesis and conclusion with the Lean statement.

| Node text | Lean rendering |
| --- | --- |
| Commutative rings B and S and a homomorphism B → S | `B : Type u`, `S : Type v`, `[CommRing B]`, `[CommRing S]`, `[Algebra B S]`; the map is `algebraMap B S`. Every ring homomorphism supplies this algebra structure. |
| Every element satisfies a monic polynomial | `hIntegral : Algebra.IsIntegral B S`. This is integrality, without finiteness or Noetherianity. |
| Finite group acting by B-algebra automorphisms | `[Group G] [Finite G]`, `ρ : G →* (S ≃ₐ[B] S)`. No action on the original factor index set is assumed. |
| Prime p | `p : PrimeSpectrum B`, whose ideal is `p.asIdeal`. |
| Finite product with n ≥ 1 | `n : ℕ`, `hn : 0 < n`, `D : Fin n → Type w`, ring and B-algebra instances on each D, and `d : S ≃ₐ[B] ∀ i, D i`. |
| Exactly one prime over p in every D_i | `hD : ∀ i, ∃! Q : PrimeSpectrum (D i), Q.asIdeal.comap (algebraMap B (D i)) = p.asIdeal`. |
| Principal localization away from p | `∃ b : B, b ∉ p.asIdeal ∧ ...`; the rings are precisely `Localization.Away b` and `Localization.Away (algebraMap B S b)`. |
| Finite family of orthogonal idempotents with sum one | `e : Fin n → Localization.Away ...`, `he : CompleteOrthogonalIdempotents e`; its fields are `idem`, `ortho`, `complete`. |
| Product of the rings e_j S_b | `(he.idem j).Corner` is Mathlib's actual corner ring. Its carrier is the range of `s ↦ e j * s * e j`; for a commutative ring and an idempotent this is exactly `e j * S_b`. Its unit is e_j. |
| Isomorphism s ↦ (e_j s), inverse summation | `Φ : S_b ≃+* ∀ j, (he.idem j).Corner`, `(Φ s j).val = e j * s`, and `Φ.symm x = ∑ j, (x j).val`. |
| Isomorphism of B_b-algebras | The scalar formula for `Φ (Localization.awayMap (algebraMap B S) b a)` records the scalar map into corner j as `a ↦ e j * Localization.awayMap ... a`. This is the B_b-algebra condition, expressed on the ring equivalence and scalar maps to avoid choosing additional algebra instances on the corner types. These maps are unital into the corners, whose units are e_j. |
| Refinement of the localized original factor partition | For each j there is i such that `e j ∉ Q.asIdeal` implies `algebraMap S S_b (d.symm (Pi.single i 1)) ∉ Q.asIdeal`, for every localized prime Q. The pulled-back coordinate unit is the idempotent defining the original i-th factor open. |
| Exactly one prime over p B_b in every D(e_j) | `pb : PrimeSpectrum (Localization.Away b)`, `hpb` says its contraction is p, and the `∀ j, ∃! Q, ... ∧ e j ∉ Q.asIdeal` clause gives the specified uniqueness. The localization prime correspondence makes pb exactly p B_b. |
| G permutes idempotents, factors and opens | `ρb : G →* (S_b ≃+* S_b)` agrees with ρ on every element of S, hence is its unique localized action; `π : G →* Equiv.Perm (Fin n)` and `ρb g (e j) = e (π g j)`. These equations also restrict the automorphism to isomorphisms of the associated corners, and carry their basic opens to the corresponding basic opens. |
| Contraction identifies the fibre primes | `Set.BijOn (PrimeSpectrum.comap (algebraMap S S_b))` from the primes contracting to pb under the canonical localized scalar map onto those contracting to p in S. |
| Identification preserves the group action on primes | The equality of the two iterated ideal comaps after applying `ρb g` and `ρ g`. The action on primes itself is comap along the inverse automorphism; equality for every g also gives that convention. |
| Identification preserves residue fields and the base field embeddings | `σB` and `σQ` are ring equivalences of the residue fields, their ring homomorphisms are prescribed to be the canonical `Ideal.ResidueField.map`, and the square with the base residue embeddings commutes. The equality h used to form the original residue embedding is explicitly existentially supplied, rather than assumed. |
| Residue-field identifications preserve the G-action | The last clause equates the two compositions of canonical residue-field maps around the action/localization square, with an explicit equality witness h of the corresponding contracted ideals. Thus it is natural for every group element, including those moving a fibre prime. |
| Cardinality n and chosen prime in a relabelled first factor | The output index type is `Fin n`; for each localized fibre prime Q there is `σ : Equiv.Perm (Fin n)` with `e (σ ⟨0, hn⟩) ∉ Q.asIdeal`. The preceding bijection transports any originally chosen fibre prime here. |
| Purely inseparable residue extensions remain so | For each Q over pb the explicit `RingHom.IsPurelyInseparable` equivalence compares its base residue map with the original residue extension. In fact preservation in both directions follows from the compatible field isomorphisms. |
| Residue field means Frac(S/Q) | `Ideal.ResidueField` has the existing `IsFractionRing (S ⧸ Q)` instance, so its local-ring definition is the same residue field up to canonical isomorphism. |
| No Noetherian or module-finiteness hypothesis | Neither occurs; the universes u, v, w and z are separately bound. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`:
  recorded statement dependency `def-weil-affine-spectrum`. As its record notes,
  the underlying spectrum is `PrimeSpectrum`; primes and ring-induced maps in
  this ring-level statement use `PrimeSpectrum` and ideal contraction.
- `Mathlib.RingTheory.Idempotents`: `CompleteOrthogonalIdempotents`,
  `IsIdempotentElem.Corner`, and `CompleteOrthogonalIdempotents.ringEquivOfComm`
  (read for the carrier, multiplication, unit, product map and inverse). The
  theorem uses the first two notions and prescribes the latter map's formulas.
- `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away`,
  `Localization.awayMap` and its underlying `IsLocalization.Away.map`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`:
  `Ideal.ResidueField` and `Ideal.ResidueField.map`, with their signatures and
  the fraction-ring instance immediately below them.
- `Mathlib.RingTheory.RingHom.PurelyInseparable`:
  `RingHom.IsPurelyInseparable`, allowing the exact canonical field maps to be named.
- Proof dependency `Mathlib.RingTheory.Spectrum.Prime.Topology`:
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `PrimeSpectrum.isIdempotentElemEquivClopens`,
  `PrimeSpectrum.isClosedMap_comap_of_isIntegral`,
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`,
  `PrimeSpectrum.localization_away_comap_range` (all read).
- Proof dependency `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`:
  `IsLocalization.prime_localRing_residueField_iso`; read its full declaration
  and docstring, including the local ring and residue field normalization clauses.

Edge cases checked before drafting:

- n = 1 and the trivial group are permitted; the identity refinement and b = 1
  satisfy the mathematical assertion. The first-index clause uses precisely hn.
- n = 0 is excluded by the node itself. An empty group is impossible for a group.
- Zero B has no prime p; zero S or any zero D_i contradicts the unique-prime
  hypothesis. There is no additional nontriviality binder excluding valid cases.
- The initial factors may be disconnected and need not be permuted by G; no
  compatibility hypothesis is introduced. Empty pieces in the temporary common
  refinement are discarded only after principal localization.
- Infinite integral algebras are permitted; the proof uses closedness of an
  integral spectrum map and never module finiteness.
- Residue extensions may be non-purely-inseparable; preservation is conditional
  via an equivalence, not an added hypothesis. Characteristic zero is included.
- Moving as well as fixed primes are covered by the final residue square.
- The chosen prime clause applies to every fibre prime by the contraction
  bijection, with no additional pointing assumption on the original product.

Searches performed (2026-10-24):

- `msearch.py leanfinder`: “Integral algebra finite group action equivariant
  refinement of finite idempotent partition after principal localization”. Eight
  hits concerning invariant integrality, Frobenius and prime orbits; no refinement.
- `msearch.py loogle`: `IsIdempotentElem, Localization.Away`. Two étale
  quasi-finite splitting lemmas; these require finite type and change the base
  étale-locally, so do not give this statement.
- `msearch.py leansearch`: “Equivariant refinement of a finite product
  decomposition of an integral algebra after localization at an element outside
  a prime”. Eight hits about localization of products, induced maps and finite
  presentation; none states the required equivariant refinement.
- `msearch.py grep`: `idempotent.*(subring|factor|equiv)|(subring|factor|equiv).*idempotent`.
  Twenty-five hits, including the clopen correspondence and Morita material, with
  no exact match.
- Direct `rg` of Mathlib's `RingTheory/Idempotents.lean` found `Corner` and
  `ringEquivOfComm`, which are reused rather than redeclared.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for equivariant
  refinements/partitions, idempotent subrings, and the proposed declaration name
  found no existing statement; unrelated sheaf and normalized-splitting refinements
  do not concern this algebraic construction. A search for corner/idempotent
  product uses found the existing integral normal residue splitting statements,
  not this theorem.
- `grep -rn` of the item id in `lean/WeilConjectures` returned no match.
- `rg` of Mathlib, both project roots, and `dag/lean_names_upstream.json` for
  `exists_equivariant_fibre_product_refinement` returned no match.

No STATEMENT-DISPUTED flag or node fault was found. The inherited CompactObject
example file is now a withdrawn module, so the active module-mode conventions
of the standing brief and nearby current modules were followed.

## Second reading by Q39

A second pass by the same dispatched worker reopened the node and completed
Lean file. No other agents were started, as the assignment expressly prohibits
that; the maintainer's independent reading is still the independent review.

I checked all three input ring universes and the group universe; the action is
by B-algebra automorphisms, while the original decomposition has no equivariance
assumption. `hD` is unique existence over the specified prime, not a weaker
nonempty fibre. The output carries all three orthogonal-idempotent conditions,
the multiplication formula and summation inverse. Its B_b scalar map is the
canonical `Localization.awayMap`, with its components multiplied by e_j, so the
ring equivalence and the displayed scalar formula encode the algebra equivalence.
The original partition is rendered by pulled-back coordinate units, and the
refinement implication holds on all localized primes, not only fibre primes.
The output action is fixed on the image of every s in S, which uniquely specifies
its extension; the permutation homomorphism acts on all output idempotents.
I separately checked uniqueness of the prime in each piece, bijectivity on the
whole fibre, the relabelled-first-index clause, both residue isomorphisms, the
base square, the moving-prime action square and the purely inseparable clause.
The residue maps have their ideal equalities supplied explicitly, and
`Ideal.ResidueField` is a fraction field of the prime quotient. No mathematical
mismatch required a change. The first compiler pass found a line-broken field
projection; the next pass found one 101-character line. Both were repaired.
