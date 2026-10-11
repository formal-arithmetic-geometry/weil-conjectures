## Worker report

The module `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition` states
`HenselianLocalRing.finiteType_exists_algEquiv_pi_prod`, with its sole proof `sorry`.
It defines no new notion and leaves the informal statement unchanged.
Source checked directly: https://stacks.math.columbia.edu/tag/04GJ,
Lemma 10.153.5. The local literature/algebra.tex is absent on this machine.
The source statement agrees with the node; its proof combines 04GG (11) and (10).
The declaration docstring carries all four steps of the node's proof.

Hypothesis and clause correspondence:

- The commutative henselian local ring `(R, m, κ)` is `(R : Type u) [CommRing R]
  [HenselianLocalRing R]`. This class extends `IsLocalRing R`; `m` is the canonical
  `IsLocalRing.maximalIdeal R`, and κ is its canonical residue field. Neither needs
  a separate arbitrary parameter.
- The finite-type ring map `R → S` is `(S : Type v) [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S]`; its ring map is `algebraMap R S`.
- An integer `n ≥ 0` is `∃ n : ℕ`. The local factors are indexed by `Fin n`.
- The rings `A₁, …, Aₙ` and B, each an R-algebra, are
  `(A : Fin n → CommAlgCat.{v} R) (B : CommAlgCat.{v} R)`. Each bundle supplies
  exactly the ring and R-algebra structures, without a nonzero condition on B.
- The R-algebra isomorphism is `Nonempty (S ≃ₐ[R] (∀ i, A i) × B)`.
  The dependent function type is the finite product with componentwise operations.
- Each factor is local and finitely generated as an R-module through
  `∀ i, IsLocalRing (A i) ∧ Module.Finite R (A i)`.
- Every prime of B lying over m is quantified as `q : PrimeSpectrum B` with
  `q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R`.
  The conclusion at each such prime is `¬ Algebra.IsQuasiFiniteAtPrime R B q`.
- The existential `Algebra.FiniteType R B` supplies the instance required by that
  recorded predicate. This is implicit in the informal use of the predicate:
  it follows from the displayed isomorphism and surjectivity of the B-projection,
  hence imposes no additional restriction on the decompositions in the node.

Dependency declarations read in full and used:

- `Sheaf.RingTheory.HenselianTerminology`: its mixed record explicitly assigns
  henselian local rings to Mathlib's `HenselianLocalRing`. Its signature, docstring,
  and inherited `IsLocalRing` were read in `Mathlib.RingTheory.Henselian`.
  The imported terminology module is the module recorded by the dependency node;
  `IsStrictlyHenselianLocalRing` is unnecessary here.
- `Sheaf.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`: the finite-type
  predicate says that the corresponding prime in the fibre spectrum is isolated.
  Its full definition and docstring were read, and it is used without a private copy.
- Mathlib's `CommAlgCat` bundles the factors' structures; Mathlib's algebra Pi and
  Prod instances supply precisely the finite product R-algebra.

Edge cases checked: `n = 0` gives the one-element zero ring as the empty product,
so the finite part may vanish. B is allowed to be zero, giving an empty prime spectrum
and a vacuous residual condition. S can be zero (take n = 0 and B zero). There is no
Noetherian, domain, characteristic, nonzero-S or nonzero-B assumption. R is nonzero
as part of the source's local-ring convention. The factor universe v is that of S:
all factors can be realized as quotients of S, so this excludes no decomposition.
Base-ring universe u is independent; there are no test-algebra universal quantifiers.

Searches made for an existing statement:

- `msearch.py ... leanfinder`: “finite type algebra over henselian local ring splits as
  finite local algebras and residual algebra with no quasi-finite points over maximal
  ideal”. Eight hits: HenselianLocalRing.TFAE, residue-field finiteness, and quasi-finite
  residue-field results; none states the decomposition.
- `msearch.py ... loogle`: `HenselianLocalRing, Algebra.FiniteType`: zero hits.
- `msearch.py ... leansearch`: “finite type algebra over henselian local ring decomposes
  into finite local factors”: service unavailable (Internal Server Error).
- `msearch.py ... grep`: `Henselian.*(prod|finite)|henselian.*(prod|finite)` in RingTheory:
  zero hits.
- `rg` in `WeilConjectures`: `Henselian.*(prod|splitting)|henselian.*(prod|splitting)|
  finiteType.*splitting`, and the exact node id: no hits.
- `rg` in `lean/Sheaf`: `henselian.*product|Henselian.*Product|finite.type.*decompos`:
  found the related `FiniteOverHenselianLocalProduct` (04GH, module-finite input),
  `EtaleRetractionFiniteTypeSplitting` (04GG, different input, two factors), and
  `EtaleFiniteFactorDecomposition` (étale base change). None is this statement.
  The first two modules were opened; the first has additional henselian-factor and
  residue-field conclusions and assumes module-finite input, so is not a match.
- Exact declaration-name collision search across Mathlib, WeilConjectures and Sheaf:
  no pre-existing `finiteType_exists_algEquiv_pi_prod`.

Server check: `scompile.py H1 lem-weil-pbc-henselian-finite-type-product-decomposition`
compiled the module in 1.7 seconds, exit code 0, no warnings. No statement dispute,
new nodes, dependency repairs, or statement corrections.

## Second reading by H1

I read the item node, its sandbox module, both statement-dependency nodes and their
recorded modules, and the Mathlib declarations those modules use. The repository's
Stacks checkout is absent. I therefore read Tag 04GJ and Tag 04GG online and fetched
Stacks' `algebra.tex` into this item's scratchpad. The label `lemma-mop-up` is at
42418, its statement at 42419–42423, and its proof at 42427–42428, exactly the source
place in the node. I also read the section-wide conventions at 42063 onward,
Definition 04GF, and 04GG (8), (10), (11). There is no ambient Noetherian, domain,
characteristic, or separatedness hypothesis. Source: https://stacks.math.columbia.edu/tag/04GJ
and https://stacks.math.columbia.edu/tag/04GG.

Here is my independent list of the objects, hypotheses and conclusion clauses,
matched item by item with the Lean signature:

1. A commutative henselian local ring `(R, m, κ)`: `(R : Type u) [CommRing R]
   [HenselianLocalRing R]`. The class extends `IsLocalRing R`, which extends
   `Nontrivial R`. The canonical maximal ideal is `IsLocalRing.maximalIdeal R`;
   the residue field is implicit, and the statement never needs a separate κ
   parameter. The dependency's mixed record expressly selects this existing
   Mathlib class, rather than its separate strictly henselian definition. Its
   simple-root criterion is 04GF, equivalent to the node's idempotent criterion.
   Verdict: same object and hypothesis.
2. A finite-type ring map `R → S`: `(S : Type v) [CommRing S] [Algebra R S]
   [Algebra.FiniteType R S]`. The map is `algebraMap R S`; an arbitrary unital
   commutative ring map supplies this algebra structure. FiniteType means finite
   algebra generation, not module finiteness. Verdict: exact.
3. A nonnegative integer and a finite family of local R-algebras:
   `∃ (n : ℕ) (A : Fin n → CommAlgCat.{v} R)`, with
   `∀ i, IsLocalRing (A i)` in the conjunction. I opened CommAlgCat.Basic:
   each bundle contains a carrier, CommRing and Algebra R structure, with no
   additional finiteness or nontriviality requirement. Locality supplies precisely
   the required nonzero local factors. Verdict: exact.
4. An R-algebra B, possibly zero: `(B : CommAlgCat.{v} R)`. There is no
   `Nontrivial B` or locality assumption. Verdict: exact.
5. An R-algebra isomorphism from S to the product of those factors and B:
   `Nonempty (S ≃ₐ[R] (∀ i, A i) × B)`. Pi and Prod have componentwise ring and
   algebra structures. Nonempty asserts existence of an isomorphism; regrouping
   the finite factors changes no mathematical assertion. Verdict: exact.
6. Every local factor is a finitely generated R-module:
   `∀ i, IsLocalRing (A i) ∧ Module.Finite R (A i)`. Verdict: exact, with no
   extra finite-presentation, flatness or residue-field clause.
7. For every prime of B over m, the structure map is not quasi-finite there:
   `∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap R B) =
   IsLocalRing.maximalIdeal R → ¬ Algebra.IsQuasiFiniteAtPrime R B q`.
   I opened the recorded definition: it says the corresponding singleton in
   Spec(κ(p) ⊗[R] B) is open, using preimageHomeomorphFiber. This is precisely the
   dependency's isolated-fibre-point notion, with the tensor factors commuted.
   Negation, contraction, and universal quantification agree. Verdict: exact.
8. The additional existential `(_ : Algebra.FiniteType R B)` is a typing witness
   for that recorded definition, not an input hypothesis. It follows already
   from clause 5: the B-projection composed with the isomorphism is a surjective
   R-algebra homomorphism. I read `Algebra.FiniteType.of_surjective` at
   FiniteType.lean:86. Thus any node decomposition supplies the witness, and
   forgetting it gives the node decomposition. Verdict: equivalent, no strengthening.

Edge cases: `Fin 0` is allowed, so the empty finite product is the zero ring.
For S = 0 take n = 0 and B = 0; B has no primes, so the residual condition is
vacuous. B = 0 also permits the wholly finite case. An empty closed fibre for a
nonzero B likewise makes the condition vacuous as required. R = 0 is excluded by
both local-ring conventions, not by an additional hypothesis. All characteristics
are admitted, including mixed characteristic. The independent universes u and v
are explicitly bound; factors may be taken as quotients of S in Type v. No
quantification over test rings in a too-small universe occurs. No scheme appears.

Independent searches used other wording than the worker's:

- LeanFinder via msearch: `Henselian ring finitely generated algebra finite summand
  decomposition isolated closed fibre points`. Eight hits, consisting of henselian
  root criteria and Algebra.quasiFinite_iff; none states this decomposition.
- Loogle via msearch: `HenselianLocalRing, AlgEquiv`: zero hits.
- LeanSearch via msearch: `henselian local finite type algebra product local
  finite algebras`: unavailable (Internal Server Error), recorded as unavailable.
- Grep via msearch in Mathlib/RingTheory: `henselian.*(summand|decompos|splitt)|04GJ|mop.up`:
  zero hits. Direct rg additionally inspected Henselian.lean and upstream Etale
  modules, then searched both WeilConjectures and the project's lean/Sheaf for
  henselian splitting/decomposition/product terminology and Tag 04GJ. I opened
  FiniteOverHenselianLocalProduct, EtaleRetractionFiniteTypeSplitting, and
  EtaleRetractionFiniteProductLocal. The first assumes module-finite input and
  has stronger factor conclusions; the latter two assume the retraction condition
  and provide different decompositions. None duplicates this node. The exact name
  is absent from those trees and dag/lean_names_upstream.json.

No H3–H9 mismatch found. There are no new definition nodes, dependency modules,
statement corrections or disputed flags in the delivery. The module uses the
recorded notions, defines nothing, and its sole theorem proof is `sorry`. Its
source docstrings contain the blueprint id and all four proof steps, with the
same dependency nodes as the node. Imports serve the used structures; no local
notation, private definition, hidden let binder, or unbound universe occurs.
The node's lean.statement agrees verbatim with the signature before `:=`.
I left the correct Lean and node unchanged and appended this second reading.

Independent server validation: scompile.py compiled the 53-line module in 1.7 s,
exit code 0, with no warnings or errors.
