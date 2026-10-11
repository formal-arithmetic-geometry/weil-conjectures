## Worker report

The module `lean/Sheaf/RingTheory/HenselianEtaleRetraction.lean` states
`existsUnique_algHom_of_henselianLocalRing_etale`. The binders `S B`, the
commutative-ring instances, and `[HenselianLocalRing S]` render the henselian
local base ring. The ring homomorphism `φ : S →+* B` and `[Algebra S B]`
render the map of rings and its S-algebra structure. The étale hypothesis is
the Mathlib scheme morphism `AlgebraicGeometry.Etale
(Scheme.Spec.map (CommRingCat.ofHom φ).op)`, exactly the morphism
`Spec B → Spec S`. The prime `q' : Ideal B` with `[q'.IsPrime]` renders the
chosen prime. `hq : q'.comap φ = IsLocalRing.maximalIdeal S` says that it lies
over the maximal ideal. The hypothesis `hres` is bijectivity of
`Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm`, the induced
map on residue fields. The conclusion `∃! σ : B →ₐ[S] S` gives exactly one
S-algebra homomorphism, and `(maximalIdeal S).comap σ.toRingHom = q'` is the
specified inverse-image condition. The proof is `sorry` as required at stage 2.

Dependencies used: `HenselianLocalRing` from Mathlib (the dependency
`def-weil-pbc-henselian-terminology` records this declaration),
`AlgebraicGeometry.Etale` from Mathlib (`def-weil-etale-morphism`), and
`Ideal.ResidueField.map` from Mathlib (`def-weil-residue-field`).

Edge cases checked: the statement permits arbitrary universe `u`, arbitrary
commutative rings (including the zero ring where permitted by the local-ring
class), arbitrary prime ideals, and does not impose finiteness or separable
closure assumptions. The residue-field condition is expressed by bijectivity,
so both injectivity and surjectivity are retained.

Searches made: the node's recorded LeanSearch, LeanFinder, Loogle, and grep
searches (all dated 2026-10-09) found only root-lifting and standard-etale
lemmas, with no theorem giving this henselian retraction. I additionally
searched `Mathlib.RingTheory.Henselian`, `Mathlib.RingTheory.Etale`, and the
source repository for retraction/section statements; no exact declaration was
found.

No `STATEMENT-DISPUTED` or node fault.

## Earlier second reading (a previous round; superseded)

Reading the node and module together: each node hypothesis is represented in
order. The local henselian assumption is Mathlib's `HenselianLocalRing`, whose
parent supplies `IsLocalRing`; `hq` therefore compares with its maximal ideal.
The scheme étale class is applied to the contravariant spectrum morphism built
from `φ`. The residue-field clause uses the canonical ideal residue-field map
with the equality oriented as required by Mathlib (`hq.symm`). The conclusion
is exactly existence and uniqueness of an S-algebra retraction with the stated
prime preimage. No mismatch was found.

## Second reading by F1

I read the sandbox node and Lean module, all three statement-dependency nodes,
their recorded declarations and source signatures, and Stacks algebra.tex,
section Henselian local rings: definition-henselian (04GF), lemma-uniqueness
(06RR), and lemma-characterize-henselian (04GG), especially condition (8) and
the proof of (1) ⇒ (8). The repository's literature/stacks-project directory
is absent on this machine; the available Stacks source is
/home/ubuntu/c1-stacks-review/algebra.tex, lines 42060–42220. The section's
standing assumption is only a local ring (R, m, κ), with the usual reduction
notation. There is no standing Noetherian, domain, characteristic, finiteness
of the algebra as a module, or separable-closure assumption.

Object/hypothesis/conclusion checklist (node order):

1. A commutative henselian local base S, maximal ideal m, and residue field κ:
   `{S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]`,
   `IsLocalRing.maximalIdeal S`, and its `Ideal.ResidueField`. PASS.
   I opened Mathlib.RingTheory.Henselian: HenselianLocalRing extends
   IsLocalRing and has the simple-root lifting axiom. The mixed recorded
   dependency Sheaf.RingTheory.HenselianTerminology explicitly records this
   existing class for the local notion, not its new strict-henselian definition.
   The idempotent formulation and this formulation are equivalent by the
   dependency's cited Stacks 09XI/04GG and the node's local-root-lifting lemma;
   no strict henselian or separably closed field condition has been inserted.
2. One ring map S → B: `(φ : S →+* B)`. Its S-algebra structure is now
   exactly `letI : Algebra S B := φ.toAlgebra` in the conclusion. REPAIRED:
   the former independent `[Algebra S B]` could be unrelated to φ, so the
   conclusion did not assert a retraction of the map in the hypotheses.
   RingHom.toAlgebra uses φ as its algebraMap; thus AlgHom.commutes says
   precisely σ ∘ φ = id. No extra compatibility hypothesis is needed.
3. Spec B → Spec S is étale:
   `[AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]`.
   PASS. I opened the dependency's Mathlib class (affine-locally étale ring
   maps) and its HasRingHomProperty bridge; this is exactly the specified
   spectrum morphism, without a finite-algebra or domain requirement.
4. A prime q' of B: `(q' : Ideal B) [q'.IsPrime]`. PASS.
5. q' lies above m: `hq : q'.comap φ = IsLocalRing.maximalIdeal S`. PASS.
6. The induced residue-field map κ → κ(q') is an isomorphism:
   `hres : Function.Bijective (Ideal.ResidueField.map
   (IsLocalRing.maximalIdeal S) q' φ hq.symm)`. PASS.
   I opened Ideal.ResidueField and map: they are the residue field of the
   localization at the prime and the map induced by Localization.localRingHom.
   I also opened the dependency's Scheme.residueField and
   Spec.residueFieldIso: on spectra this is exactly the scheme residue field,
   not another notion. At the maximal ideal of a local ring it canonically
   identifies with S/m. Bijectivity of this ring homomorphism expresses a
   field isomorphism and retains both injectivity and surjectivity.
7. Exactly one S-algebra homomorphism σ : B → S with σ⁻¹(m) = q':
   `∃! σ : B →ₐ[S] S, (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q'`,
   under the algebra structure of item 2. PASS after repair. Uniqueness is
   restricted to retractions with this preimage, exactly as Stacks (8), and
   all quantifiers are in the node's order.

Edge cases: no index set or degree parameter occurs in the signature. The
proof docstring explicitly retains n = 0 in the standard étale identity.
All characteristics, fields as local rings, nonreduced local rings and
arbitrary primes are allowed. The zero base ring is excluded by IsLocalRing's
Nontrivial parent, exactly because the source's local ring has a proper
maximal ideal and a residue field. A zero B (empty Spec B) has no prime q',
so there is no omitted admissible case. Universe u is explicitly bound and
arbitrary; both rings can be placed in a common larger universe by Lean's
cumulativity, so this does not impose a smallness bound or equate cardinalities.
There is no quantification over test rings in a potentially smaller universe.

Independent searches, recorded by msearch.py on 2026-10-11:

- LeanFinder: "étale algebra over a Henselian ring admits unique lift of a
  residue field valued algebra homomorphism". Returned StandardEtalePair.lift,
  homEquiv, the square-zero quotient lifting theorem, and HenselianLocalRing.TFAE;
  none is the general unique retraction theorem.
- Loogle: "HenselianLocalRing, AlgHom". Only HenselianLocalRing.TFAE.
- LeanSearch: "Unique algebra section of an etale ring map at a rational closed
  fibre point over a henselian local base". Service returned Internal Server
  Error; recorded unavailable, with no mathematical verdict claimed.
- Mathlib grep: `henselian.*(lift|section|retract)|existsUnique.*algHom`,
  RingTheory: no hit. Direct rg of project lean/Sheaf, all source WeilConjectures,
  and Mathlib RingTheory used the alternate words section, retract,
  exists.*AlgHom and Henselian. I opened the upstream Henselian and Etale/QuasiFinite
  files: HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq is the converse;
  Algebra.Etale.exists_algHom_comap_maximalIdeal_eq assumes an integrally closed
  domain with separably closed fraction field and gives only existence.
  Project HenselianOfEtaleSectionLifting is a converse pair criterion, and the
  other found statements are finite-étale categorical lifting or cohomology.
  None duplicates this item. The theorem's full name has no existing match.

Other mismatches and repairs: the old statement docstring compressed the
six-step DAG proof into one sentence (H8); it now carries the residue map and
kernel characterization, standard étale presentation, localization bijection,
simple residue root, existence by lifting, and uniqueness, with every named
proof dependency. Added the standard copyright/license/authorship header.
The node's lean.statement was synchronized verbatim with the new signature.
No natural-language node statement changed; no statement_change record,
new definition node, or dependency module is necessary. No data definition
was added, and the sole theorem remains `by sorry` as required by stage 2.
All imports are used, every variable/universe is bound, and lines are at most
100 characters. The earlier second reading above is superseded by this one.

Validation: scompile.py F1 lem-weil-pbc-henselian-etale-retraction on the
single delivery module exited 0 (compiled in 1.7 seconds), with no warnings.
