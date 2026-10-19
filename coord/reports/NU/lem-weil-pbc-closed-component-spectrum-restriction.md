## Worker report

The module `Sheaf.RingTheory.ClosedComponentSpectrumRestriction` states
`PrimeSpectrum.exists_closed_component_restriction`, with `sorry` as its whole proof.
There are no definitions or additional theorems and no change to the natural-language statement.

Hypothesis and conclusion correspondence:

- A commutative ring A: `(A : Type u) [CommRing A]`.
- The underlying affine spectrum and its Zariski topology: `PrimeSpectrum A`, the underlying
  space of the dependency's `AlgebraicGeometry.Spec (CommRingCat.of A)`.
- The subset E: `(E : Set (PrimeSpectrum A))`; Zariski closed: `(hE : IsClosed E)`.
- E is a union of maximal connected subsets: `hcomponents : ∀ x ∈ E,
  connectedComponent x ⊆ E`. Since each point belongs to its connected component, this
  condition is equivalent to E being a union of connected components, with no restriction
  on how many components occur.
- There exist a commutative ring B and ring map v: `∃ (B : CommRingCat.{u}) (v : A →+* B)`.
  Bundling B provides its commutative ring structure; every commutative quotient of A can
  be represented in universe u, so this imposes no size restriction on the conclusion.
- Surjectivity: `Function.Surjective v`.
- A homeomorphism of Spec B onto E with the subspace topology: `∃ h : PrimeSpectrum B ≃ₜ E`.
  The clause `∀ q, (h q).val = PrimeSpectrum.comap v q` says that this is exactly the
  spectrum map induced by v, rather than an unrelated homeomorphism.
- Every prime q of B: `∀ q : PrimeSpectrum B`. The contracted prime p is
  `q.asIdeal.comap v`. The canonical induced map is
  `Localization.localRingHom (q.asIdeal.comap v) q.asIdeal v rfl`.
  Its `Function.Bijective` states precisely that this ring homomorphism is an isomorphism,
  with source `Localization.AtPrime (q.asIdeal.comap v)` and target
  `Localization.AtPrime q.asIdeal`. Bijectivity gives an inverse ring homomorphism and is
  equivalent to the existence of a ring equivalence agreeing with this map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  (lines 470–480): the spectrum scheme has underlying space `PrimeSpectrum`, and its map
  has underlying point function `PrimeSpectrum.comap`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` (lines 54–58)
  and `Localization.localRingHom` (lines 234–244), including its full docstring and type.
  The localizations are the existing dependency's localizations, not a replacement notion.
- Proof-only imports cover the recorded proof dependencies:
  `Mathlib.CategoryTheory.Limits.HasLimits` (`colimit`),
  `Mathlib.GroupTheory.MonoidLocalization.Away` (`Localization.Away`),
  `WeilConjectures.RingTheory.ProEtale.IndZariski`
  (`Algebra.IndZariski.bijectiveOnStalks_algebraMap`, lines 581–588),
  `WeilConjectures.RingTheory.ProEtale.WContractible`
  (`WContractification.Restriction.algebraMap_surjective`, lines 148–164;
  `range_algebraMap_specComap`, lines 192–242), and
  `Mathlib.RingTheory.Spectrum.Prime.Topology`
  (`PrimeSpectrum.isClosedEmbedding_comap_of_surjective`;
  `PrimeSpectrum.range_comap_of_surjective` is in its imported RingHom module).
  These are proof dependencies, not extra hypotheses. The docstring carries all five
  proof steps, including filteredness and the g = 1 local-isomorphism argument.

Sources opened: local `literature/stacks-project/proetale.tex`, `lemma-construct`
(Tag 097C, lines 863–878), and `lemma-ind-zariski-implies` (Tag 096T, lines 467–475).
Also read `literature/stacks-project/topology.tex`,
`lemma-closed-union-connected-components` (Tag 04PL, lines 1894–1928): a closed
component union in a spectral space is an intersection of clopens, as used in step 3.
The former proetale lemma states a surjective ind-Zariski map realizing the inverse image of a closed
subset of the component quotient. Saturation of E makes its image in the quotient closed,
so this is exactly the node's situation. The latter supplies the local-ring conclusion.

Edge cases checked mathematically before writing:
E empty is allowed: the zero quotient ring has empty spectrum and the local condition is
vacuous. E equal to the whole spectrum is allowed, with B = A and identity map.
The zero ring A is allowed and forces the empty case. A connected spectrum permits only
E empty or the whole space, both covered. Non-clopen closed unions in infinitely many
components remain permitted: no openness, finiteness, Noetherian or nontriviality
hypothesis is imposed. Nonreduced rings are allowed, and the local condition concerns
actual local rings, not their reduced rings or residue fields. The quantifiers cover
all primes and every universe u.

Searches actually run through `msearch.py NU lem-weil-pbc-closed-component-spectrum-restriction`:

- LeanFinder: "Closed union of connected components of a prime spectrum realized by a
  surjective ring map inducing isomorphisms on local rings". Eight hits: closed images
  of surjective spectrum maps, closed points, closed embeddings, spectral-space and
  specialization facts. No full statement or one-line specialization.
- Loogle: `RingHom.BijectiveOnStalks, PrimeSpectrum.comap`. Zero hits; unknown identifier
  `RingHom.BijectiveOnStalks` in the Mathlib search service. This project-defined notion
  was subsequently located and read directly in `StalkIso.lean`, lines 25–59; the present
  statement uses the underlying Mathlib canonical localization map directly.
- Grep: `connectedComponent.*(quotient|closed)|BijectiveOnStalks` in `RingTheory`.
  Zero hits reported by the search service.
- LeanSearch: "A closed union of connected components of Spec A is realized by a
  surjective ring map preserving local rings". Service unavailable (Internal Server Error).
  This is not recorded as a negative search result.
- Direct `rg` of the upstream ProEtale directory for the item id,
  `closed.*[Cc]omponent`, and `[Bb]ijectiveOnStalks` found the Restriction ingredients and
  local-ring predicates, but no single theorem stating the item's conclusion.
- Direct `rg` of `lean/Sheaf` for `closedComponent|closed_component|BijectiveOnStalks`
  found only unrelated finite-field component-descent lemmas.
- Direct item-id search in upstream `WeilConjectures` and `dag/lean_names_upstream.json`
  found no exact attachment. Full-name collision search for
  `exists_closed_component_restriction` in Mathlib, upstream and `lean/Sheaf` found none.

No new nodes, dependency repairs, statement correction, or disputed statement.

Validation: server-only `scompile.py` passed cleanly in 1.5 s (nice 19, two threads,
60-second file limit). `deliver2.py --no-push` printed OK: the module compiles and all
preflight checks pass except the independent second reading reserved for the next worker.
Nothing was pushed. No local Lean compilation or library build was run.

## Second reading by NU

Independently read the node, its complete five-step proof, the Lean module, the two
statement-dependency nodes and their actual Mathlib declarations. Read Stacks
proetale.tex, lemma-construct (097C), including its preceding section assumptions,
and lemma-ind-zariski-implies (096T); also topology.tex,
lemma-closed-union-connected-components (04PL), including all three topological
hypotheses. These apply to every affine spectrum: no field, reducedness,
Noetherian, finiteness or nontriviality assumption is implicit here.

Object/hypothesis/conclusion inventory and verdicts:

1. Arbitrary commutative ring A: `(A : Type u) [CommRing A]`. Exact; universe u is
   bound and unrestricted, and the zero ring is included.
2. Underlying Zariski space of Spec A: `PrimeSpectrum A`. Exact. Opened
   `AlgebraicGeometry.Spec` and `Spec.map` in Mathlib.AlgebraicGeometry.Scheme;
   these construct the affine scheme and contravariant induced map from the
   prime-spectrum locally ringed space. The node concerns its underlying space.
3. Subset E: `(E : Set (PrimeSpectrum A))`. Exact, with the subtype topology used
   by `PrimeSpectrum B ≃ₜ E`.
4. E Zariski closed: `(hE : IsClosed E)`. Exact.
5. E a union of maximal connected subsets: `hcomponents : ∀ x ∈ E,
   connectedComponent x ⊆ E`. Exact: every x belongs to its component, so E is
   precisely the union of the components of its points. This does not require
   E to be open or to have finitely many components.
6. Existence of B and v: `∃ (B : CommRingCat.{u}) (v : A →+* B)`.
   Exact: B carries its commutative-ring instance and v is a unital ring map.
   A surjective image of A has a representative quotient in Type u, so the
   existential universe does not remove any case of the mathematical claim.
7. v surjective: `Function.Surjective v`. Exact; no extra property of v assumed.
8. Spec(v) a homeomorphism onto E: `∃ h : PrimeSpectrum B ≃ₜ E` together with
   `∀ q, (h q).val = PrimeSpectrum.comap v q`. Exact: the pointwise equation
   ties the homeomorphism to the required induced map. Its codomain is exactly
   E with its subspace topology, not merely a homeomorphic abstract space.
9. Every prime q of B, p its contraction: `∀ q : PrimeSpectrum B` and
   `q.asIdeal.comap v`. Exact; bundling q quantifies over every prime ideal.
10. Induced localization map an isomorphism: `Function.Bijective
    (Localization.localRingHom (q.asIdeal.comap v) q.asIdeal v rfl)`.
    Exact: opened Localization.AtPrime and localRingHom, whose type is exactly
    the homomorphism A_p →+* B_q and whose formula extends v. Bijectivity is
    equivalent to being a ring isomorphism; no unrelated ring equivalence is used.

Checked all proof dependency records and actual source signatures:
`Restriction.diag`, `Restriction`, `Restriction.algebraMap_surjective`,
`Restriction.range_algebraMap_specComap`, and `Restriction.indZariski` in
WeilConjectures.RingTheory.ProEtale.WContractible use the clopen-neighborhood
colimit in CommAlgCat A. The diagram allows arbitrary T; the range lemma alone
requires IsClosed T. `Algebra.IndZariski.bijectiveOnStalks_algebraMap` in
IndZariski and `RingHom.BijectiveOnStalks` in ProEtale.StalkIso give the same
canonical localRingHom bijections. The Mathlib closed-embedding/range lemmas,
Localization.Away and colimit imports match the remaining proof nodes.
The module docstring reproduces all five proof steps, including filteredness
and the g = 1 neighborhood argument. No substitute notions or dependency
repairs are needed. The 51-module pro-etale framework instructions were read;
this ring-theoretic item does not use those module-object declarations.

Edge cases: E empty is realized by the zero ring (local conclusion vacuous);
E the whole space by the identity. A zero ring has empty spectrum. A connected
spectrum permits only these two E. Infinitely many components and a closed
union that is not open remain covered. Nonreduced rings and all characteristics
remain covered: local rings, not residue fields or reductions, occur in the
conclusion. There is no numerical n, finite-index hypothesis or independent
universe for test objects. The existential B and h precede the universal q,
as required. No unbound variables, hollow definitions, local notation or
instances occur; the sole theorem proof is sorry.

Independent searches (using different wording from the first worker):

- LeanFinder via msearch.py: "Realize a closed saturated subset of Spec R by a
  quotient with bijective canonical maps on prime localizations". Eight hits,
  including toPiLocalization_bijective, piLocalizationToMaximal_bijective,
  comap_quotientMk_bijective_of_le_nilradical and ZariskisMainProperty.
  None states this existence theorem; the nilradical quotient concerns an
  arbitrary fixed nilpotent-thickening quotient and does not preserve local rings.
- Loogle via msearch.py: `PrimeSpectrum.comap, Homeomorph`. Three fiber
  homeomorphism declarations, not this closed-component restriction theorem.
- Grep via msearch.py in RingTheory:
  `component.*(surject|quotient)|closed.*saturat|restriction.*spectrum`.
  Only an unrelated Witt-vector ghost-component hit.
- LeanSearch via msearch.py: "A closed saturated set of prime ideals is the
  spectrum of a surjective ring map inducing bijections on prime localizations".
  Service returned Internal Server Error; not counted as a negative search.
- Direct rg across upstream WeilConjectures and project lean/Sheaf with
  `closed.{0,20}component|component.{0,20}restriction|saturated.{0,20}spectrum`
  found the Restriction ingredients and unrelated descent/cohomology statements,
  not an existing theorem with this full conclusion. Read the relevant
  Restriction and StalkIso declarations rather than inferring their types by name.
  Exact-name searches in upstream, Mathlib, project sources and the upstream
  name index found no collision with exists_closed_component_restriction.

No mismatch found. Kept the correct Lean and node unchanged; added this
independent review and search evidence only. No new nodes, dependency modules,
statement correction or disputed statement, hence no corrected-statement citers.
