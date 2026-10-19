## Worker report

The module `Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso` states
`Algebra.isIndPrincipalZariski_of_bijective_localRingHom` with `sorry` as its entire proof.
No definitions, additional nodes, dependency modules, or statement corrections are needed.
The source is the blueprint node in `sec-proper-base-change/sk-thm-properbasechange`,
order 1230, read together with the expanded nine-step proof in the DAG node.

Hypotheses and conclusion, clause by clause:

- The commutative rings are `(A B : Type u) [CommRing A] [CommRing B]`.
- The ring homomorphism is the unrestricted `[Algebra A B]` structure, whose underlying
  ring map is `algebraMap A B`. Every homomorphism supplies this structure via `toAlgebra`.
- Every prime ideal of B is quantified by `∀ (q : Ideal B) [q.IsPrime]` in `hlocal`.
- Its contraction to A is `q.comap (algebraMap A B)`. The canonical map
  `A_(q ∩ A) → B_q` is
  `Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl`.
  The `rfl` certifies the equality with the contraction; it adds no hypothesis.
  `Function.Bijective` of this ring homomorphism says it is an isomorphism, including
  compatibility with the specified original map. This does not merely assume that the
  two local rings happen to be abstractly isomorphic.
- W-locality of Spec B is exactly the dependency's `[IsWLocalRing B]`.
  Neither A nor the morphism on spectra is assumed w-local.
- The entire conclusion is `IsIndPrincipalZariski A B`, the dependency's precise
  filtered-colimit presentation by finite products of principal localizations.
  Its definition quantifies over `I : Type u`, `SmallCategory I`, `IsFiltered I`, and
  `ColimitPresentation I (CommAlgCat.of A B)`, and requires each stage to be A-algebra
  isomorphic to `((j : Fin n) → Localization.Away (f j))` for some n and f.
  Thus the cocone maps preserve this same A-algebra structure and the specified ring map.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.ProEtale.WLocal`, `IsWLocalRing`; its field is
  `WLocalSpace (PrimeSpectrum B)`. Also read `WLocalSpace` in
  `WeilConjectures.Topology.SpectralSpace.WLocal.Basic`: closedness of closed points
  and uniqueness of closed specialization, matching the dependency's component description.
- `Sheaf.RingTheory.IndPrincipalZariski`, `Algebra.IsIndPrincipalZariski`, read in full.
  The alternative upstream `Algebra.IndZariski` allows local isomorphisms as terms and
  is not substituted for the dependency's principal-localization notion.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` and
  `Localization.localRingHom`, including the latter's canonical-map docstring.
  The recorded secondary declarations `Ideal.ResidueField` and `Ideal.Fiber` were read
  in Mathlib's `RingTheory.LocalRing.ResidueField.Ideal` and `.Fiber`; neither is needed
  in this node's signature.
- `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`, reused through
  the conclusion's definition rather than privately copied.

The stated proof dependencies are imported without `public`: `Algebra.FinitePresentation`
(`Mathlib.RingTheory.FinitePresentation`); the localization universal property
(`Mathlib.RingTheory.Localization.Away.Basic`); the basic-open, compactness and clopen
idempotent lemmas (`Mathlib.RingTheory.Spectrum.Prime.Topology`); open-immersion etaleness
(`Mathlib.AlgebraicGeometry.Morphisms.Etale`); finite presentation and localization of
etale algebras (`Mathlib.RingTheory.Etale.Basic`); finite products of etale algebras
(`Mathlib.RingTheory.Etale.Pi`); and `CommAlgCat.exists_filtered_colimit_of_factorization`
(`Sheaf.RingTheory.FilteredColimitOfFactorization`). The localizations and ind-Zariski
statement dependencies already have public imports. The proof dependency
`lem-weil-pbc-w-local-partition` has no recorded Lean declaration yet, so its future
import is omitted and listed here. The declaration docstring carries all nine proof steps.

Edge cases checked: no nontriviality hypothesis excludes the zero ring. When B is zero,
the prime-localization hypothesis is vacuous and its empty spectrum has the required
w-locality; the conclusion allows the empty finite product (`n = 0`). A nonzero target
with A zero admits no unital ring map, as required, without a separate exclusion. All
primes, not just maximal ideals, are assumed in the statement; only the proof starts
at maximal ideals. No characteristic restriction is imposed. A and B share the explicitly
bound universe u, as required by the recorded colimit notion; any two ring carriers can
be placed in a common universe. The diagram index lives in that same universe, not a
smaller independent universe. The conclusion's filtered category is nonempty by
`IsFiltered`; an empty product at a stage remains permitted.

Searches for an existing statement (all conducted before writing):

- `msearch.py` LeanFinder: “A ring homomorphism inducing isomorphisms of all local rings
  whose target spectrum is w-local is a filtered colimit of finite products of principal
  localizations”. Eight results, including `RingHom.locally_of_exists`,
  `RingHom.locally_iff_exists`, `RingHom.locally_iff_finite`, `RingHom.OfLocalizationPrime`,
  `MaximalSpectrum.mapPiLocalization`, `RingHom.HoldsForLocalization.localRingHom`,
  `RingHom.locally_iff_isLocalization`, and `RingHom.Locally`; none states this theorem.
- `msearch.py` Loogle: `IsLocalization.localRingHom`. No hits; unknown identifier.
  The source search resolves the correct name as `Localization.localRingHom`.
- `msearch.py` LeanSearch: “A ring map inducing isomorphisms on local rings with w-local
  target is ind-Zariski”. Service unavailable, Internal Server Error; no result claimed.
- `msearch.py` Mathlib grep: `IndZariski|IndPrincipalZariski|IsWLocalRing`. No hits.
- Source `rg` for `local.*[Ii]so|[Ii]so.*local|indZariski|IndZariski|indPrincipal` in
  `WeilConjectures/RingTheory/ProEtale` found the existing local-isomorphism definitions
  and the related `Algebra.BijectiveOnStalks.indZariski_of_isWLocal`. Its full signature
  and docstring in `IndBijectiveOnStalks.lean` were read: it assumes `[IsWLocalRing R]`,
  `[IsWLocalRing S]`, `[Algebra.BijectiveOnStalks R S]`, and a w-local ring map,
  and concludes upstream `Algebra.IndZariski R S`. The extra assumptions and different
  conclusion mean it does not state this item.
- Source grep for the item's exact blueprint id found no declaration.
- Project `rg` for `indPrincipal|IndPrincipal|local_rings_ind|localRings.*[Ii]nd|` followed
  by the exact item id found the principal ind-Zariski definition and its stability and
  w-localization consumers, but no statement of this item.
- A full-name collision search for `isIndPrincipalZariski_of_bijective_localRingHom` in
  Mathlib, upstream WeilConjectures, project Sheaf, and `dag/lean_names_upstream.json`
  found no hits.

No node faults or disputed statements were found. Server-only single-file compilation
and the delivery dry run are used for validation; only expected sorry warnings are allowed.

## Second reading by NO

I independently read the sandbox node, its blueprint source at
`sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-local-rings-ind-zariski.md`
(order 1230), the enclosing unit, and the delivered Lean module. This node's source
is the blueprint, not a Stacks tex lemma. Its source and unit impose no additional
Noetherian, characteristic, nontriviality, or finiteness assumptions on these rings.
The related upstream Stacks 097F statement was also inspected; it is not this node.

Object/hypothesis/conclusion checklist:

1. Commutative rings A and B: `(A B : Type u) [CommRing A] [CommRing B]`.
   Exact. There is no domain, field, or nonzero-ring assumption.
2. A specified homomorphism A to B: `[Algebra A B]`, with map `algebraMap A B`.
   Exact for commutative rings: an arbitrary unital ring map gives this structure
   by `RingHom.toAlgebra`. The same map occurs in both hypothesis and conclusion.
3. Every prime q of B: `∀ (q : Ideal B) [q.IsPrime]` in `hlocal`.
   Exact; this does not restrict q to maximal ideals.
4. Its contracted prime p: `q.comap (algebraMap A B)`. Exact. The contraction's
   primality follows from q's primality and does not add an assumption.
5. The induced map A_p to B_q is an isomorphism: `Function.Bijective
   (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl)`.
   Exact. I opened Mathlib's declaration and `localRingHom_to_map`: this is the
   canonical localization map commuting with the specified original ring map.
   Bijectivity of a ring hom is equivalent to being a ring isomorphism. The `rfl`
   supplies the definitional contraction equality, not an independent hypothesis.
6. Spec B is w-local: `[IsWLocalRing B]`. Exact. I opened the dependency node,
   `IsWLocalRing`, `WLocalSpace`, and the connected-components comparison in
   `WLocal/ConnectedComponents.lean`. The class says closed closed-points and
   unique closed specialization; its component comparison gives the dependency's
   unique closed point per connected component. Spec A and the ring map have no
   w-locality assumptions.
7. B is ind-Zariski over A, meaning a filtered colimit of finite products of A_f:
   `IsIndPrincipalZariski A B`. Exact. I opened both the dependency node and the
   complete definition in `Sheaf.RingTheory.IndPrincipalZariski`: it existentially
   gives `I : Type u`, `SmallCategory I`, `IsFiltered I`, and a
   `ColimitPresentation I (CommAlgCat.of A B)`, each term A-algebra isomorphic to
   `((j : Fin n) → Localization.Away (f j))`. This preserves the specified algebra
   structure and includes n = 0. `Localization.Away` is the existing localization
   at powers, not a private replacement. The dependency's unrelated ind-etale
   and weakly etale clauses need not be repeated in this theorem's conclusion.

Edge cases: for B zero there are no primes, so `hlocal` is vacuous, and the empty
spectrum is covered by w-locality. The conclusion allows the empty product (n=0),
which is the zero algebra. If A is zero, a unital algebra map forces B zero; no
nonzero cases are lost. Finite products allow f=0 as well as f=1. There is no
characteristic restriction. The filtered index is nonempty by `IsFiltered`, as
required for a filtered colimit; an empty product is a term, not an empty diagram.
The common universe u is explicitly bound and allows both ring carriers in any
common universe; the index lives in the same universe as the recorded definition.
No independent smaller test universe or hidden variable is introduced.

Independent searches (recorded also by msearch):

- LeanFinder: "A homomorphism bijective on stalks with target w-local is a filtered
  colimit of products of localization away algebras". Eight hits concerned
  stalkwise ring properties, local detection, or bijectivity after localization;
  none states this filtered-colimit conclusion.
- Loogle: `Localization.localRingHom`. Twelve hits confirm the canonical-map API,
  including its composition and uniqueness lemmas; no theorem states this item.
- Mathlib grep via msearch: `stalk.*[Ii]somorph|[Ii]somorph.*stalk` found geometric
  stalk-comparison and open-immersion results, not the present algebraic criterion.
- Direct rg on Mathlib RingTheory for `IsIndPrincipalZariski|IndZariski|BijectiveOnStalks`
  had no hits. Direct rg on upstream ProEtale and project Sheaf/RingTheory for
  ind-principal and stalk/ind-Zariski terms found the shared definition, its
  consumers, and `Algebra.BijectiveOnStalks.indZariski_of_isWLocal`. I read that
  theorem's full signature: it additionally assumes w-local A and a w-local map,
  and concludes upstream `Algebra.IndZariski`, whose presentation uses local
  isomorphisms. It cannot replace this node's theorem. No duplicate was found.

No new nodes or dependency modules are included, and no statement correction is
present or needed. The actual shared dependency modules were read rather than
inferred from their names. The nine-step docstring follows the node's proof,
including denominator clearing, clopen patching, the empty decomposition, finite
presentation, and the existing factorization criterion. The theorem's only body
is `sorry`; there are no definitions, private helpers, axioms, local instances,
notations, or proved claims in this delivery. All lines are at most 100 characters.
I mechanically compared `lean.statement` with the complete file signature: verbatim
match. Every variable and universe is bound.

Mismatches found: none. Changes: this independent second-reading record only;
the correct Lean and node were left unchanged. Server compilation through
`scompile.py NO lem-weil-pbc-local-rings-ind-zariski` passed cleanly: the shared
principal-localization module took 1.4 seconds and this delivered module took
1.5 seconds, both nice 19, two threads, limit 60 seconds per file.
