## Worker report

The module `Sheaf.RingTheory.MapIntoHenselianColimit` states
`Algebra.map_into_henselian_colimit`. It uses `HenselianLocalRing S` (which includes
locality), an explicit filtered diagram `F : I ⥤ CommAlgCat R`, its colimit identification
with `A`, and étaleness of every stage. The prime-over condition is rendered by `p` with
`hp : p = q.comap (algebraMap R A)` and `hm` identifying `p` with the preimage of the
maximal ideal of `S`. A homomorphism of residue fields is represented by `τ`; `hτ` states
that it is a map of `κ(p)`-algebras via `Ideal.ResidueField.map`. The conclusion gives a
unique `R`-algebra map `f`, with the exact preimage condition and induced residue map.

Each hypothesis and clause is rendered directly: `R,S,A` and their commutative-ring and
algebra structures are explicit binders; `I`, `SmallCategory`, `IsFiltered`, `F`, and
`HasColimit` state the filtered colimit; `hA` identifies its carrier with `A`; `hEtale`
states stagewise étaleness; `q,p` and their primality instances, `hp`, `hm`, `τ`, and `hτ`
state the prime and residue hypotheses. The conclusion is the `∃!` over `f` and the two
conjunctive conditions under `hf`.

Dependencies used are Mathlib `CommAlgCat`, `CategoryTheory.Limits.colimit`,
`CategoryTheory.IsFiltered`, `Algebra.Etale`, `HenselianLocalRing`, and
`Ideal.ResidueField` / `Ideal.ResidueField.map`; the DAG dependencies
`def-weil-pbc-henselian-terminology`, `def-weil-pbc-category-colimit`,
`def-weil-etale-morphism`, and `def-weil-residue-field` are represented by these recorded
Mathlib declarations. Edge cases checked include the empty ring (excluded by
`HenselianLocalRing` as in Mathlib), arbitrary filtered categories including singleton
ones, a one-stage étale diagram, and arbitrary prime ideals with their required primality
instances.

Searches: `msearch.py ... leanfinder "ring homomorphism ... henselian local ring"` found
only residue-field extension lemmas and no henselian lifting theorem; `msearch.py ...
loogle "HenselianLocalRing, Algebra.Etale"` found no match; grep of Mathlib
`RingTheory/Henselian.lean` and `RingTheory/Etale` found no map-into-henselian result;
`rg` over `WeilConjectures/` and `lean/Sheaf/` found no declaration of this statement.

## Earlier second reading (a previous round; superseded)

The node's ring maps, filtered colimit data, stagewise étale clause, prime-over
conditions, residue-field algebra-map condition, and unique-map conclusion all occur in
the Lean signature. The residue condition is exactly the equality of
`Ideal.ResidueField.map` with `τ`; no hypothesis or conclusion was omitted.

## Second reading by J1

Read the node's statement, all nine proof steps, each of its four statement-dependency
records, the delivered Lean, and Stacks algebra.tex at labels
`lemma-map-into-henselian` (08HQ) and `lemma-map-into-henselian-colimit` (08HR).
The repository does not contain the literature checkout on this machine; the Stacks TeX
was read from `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 42601–42638 and
42881–42899. The statements are self-contained there: no standing Noetherian,
finiteness, characteristic, domain, or field hypothesis on the base is assumed.
There is no statement correction, new definition node, or dependency module.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Commutative rings and a ring map R → S: `(R : Type u) [CommRing R]`,
   `(S : Type v) [CommRing S] [Algebra R S]`. An algebra structure on a
   commutative ring is precisely the specified ring map. Verdict: exact.
2. S henselian local with maximal ideal m: `[HenselianLocalRing S]` and
   `IsLocalRing.maximalIdeal S`. Opened Mathlib's class, which extends
   `IsLocalRing`; opened `Sheaf.RingTheory.HenselianTerminology` and upstream
   `WeilConjectures.Mathlib.RingTheory.Henselian`. Their dependency record explicitly
   assigns the henselian local notion to this Mathlib class, the equivalent root-lifting
   form of the idempotent wording (04GG). Strict henselianity is not assumed. Exact.
3. p is the preimage of m in R: `(p : Ideal R) [p.IsPrime]` with
   `hm : p = (IsLocalRing.maximalIdeal S).comap (algebraMap R S)`.
   Primality follows from being that preimage; supplying it is redundant data, not
   an additional restriction. Exact, although p's binder occurs later for readability.
4. An R-algebra A: `(A : Type w) [CommRing A] [Algebra R A]`. Exact.
5. A filtered colimit of étale R-algebras: `(I : Type x) [SmallCategory I]
   [IsFiltered I]`, `(F : I ⥤ CommAlgCat.{w} R) [HasColimit F]`,
   `hA : Nonempty (colimit F ≅ CommAlgCat.of R A)`, and
   `hEtale : ∀ i : I, Algebra.Etale R (F.obj i)`. Opened CommAlgCat's carrier,
   algebra structures and algebra-map morphisms; the isomorphism is over R, not
   just a ring isomorphism. Opened the recorded colimit construction in HasLimits
   and IsFiltered's nonemptiness and finite-cocone conditions. Exact.
   Opened Mathlib's Algebra.Etale definition and the recorded scheme Etale
   `HasRingHomProperty @Etale RingHom.Etale`: this is the affine ring-map form
   of the node's étale spectra, explicitly allowed by the project convention.
6. A prime q over p: `(q : Ideal A) [q.IsPrime]` and
   `hp : p = q.comap (algebraMap R A)`. Exact.
7. A κ(p)-algebra homomorphism τ : κ(q) → S/m:
   `τ : q.ResidueField →+* (IsLocalRing.maximalIdeal S).ResidueField`, with
   `hτ` equating its composite with the induced p-to-q residue map to the
   induced p-to-m residue map. Opened `Ideal.ResidueField`, `map`,
   `map_algebraMap`, `IsFractionRing` and `bijective_algebraMap_quotient_residueField`.
   At a maximal ideal the canonical map S/m → κ(m) is an isomorphism, so the
   displayed target is exactly the source's S/m under its canonical identification.
   The compatibility equality specifies κ(p)-linearity without arbitrary algebra
   structures. Exact. For the scheme-residue dependency, opened `Scheme.residueField`,
   `Scheme.Hom.residueFieldMap`, and `Spec.residueFieldIso`: Mathlib supplies the
   canonical identification with `Ideal.ResidueField`; no private residue notion.
8. Exactly one R-algebra homomorphism A → S: `∃! f : A →ₐ[R] S`. The diagram
   and τ are fixed before this quantifier, as in the node. Exact.
9. Its inverse-image ideal is q: `∃ hf : q =
   (IsLocalRing.maximalIdeal S).comap f.toRingHom`. Exact; the existential witness
   is a proof of the prescribed equality, not an extra choice of ideal.
10. It induces τ: `Ideal.ResidueField.map q (IsLocalRing.maximalIdeal S)
    f.toRingHom hf = τ`. The defining `map_algebraMap` identity makes this precisely
    the node's equality on A followed by residue, and `ringHom_ext` makes the
    converse hold. Exact; the predicate inside ∃! contains both conditions.

Edge cases: IsFiltered excludes an empty category exactly as the source does;
a singleton diagram gives the single étale case. The zero S is excluded by the
source's local-ring convention (Mathlib IsLocalRing extends Nontrivial); zero R
cannot map to such S, and zero A cannot have q prime. No nonemptiness condition
on affine spectra beyond these forced prime/local conditions is added. R need
not be a field, reduced or Noetherian. All characteristics are allowed. There is
no numeric n in the statement, so n = 0 is inapplicable. Universes u, v, w and x
are explicitly bound and independent; stage carriers and A share the chosen
CommAlgCat universe, with no constraint tying it to the ring or index universe.

Independent searches (different wording from the worker): LeanFinder query
"ind etale algebra unique morphism lifting residue field to Henselian ring"
returned StandardEtalePair.homEquiv/lift/hom_ext and infinitesimal square-zero
lifting, plus a universal-factorization-ring existence lemma, none this statement.
Loogle query `"HenselianLocalRing"` returned the class, its projection, constructor,
root-lifting field and TFAE, not this lifting theorem. LeanSearch query "unique lifting
of residue field homomorphisms from filtered colimit of etale algebras to henselian
local ring" was attempted and recorded unavailable (Internal Server Error), so no
negative verdict is inferred from that service. Grep of Mathlib Henselian.lean and
RingTheory/Etale, and independent rg over WeilConjectures/, lean/Sheaf/ and
`dag/lean_names_upstream.json`, using Henselian, henselian, 08HQ, 08HR and
map_into_henselian, found no duplicate. Opened the closest project declaration
`existsUnique_algHom_of_henselianLocalRing_etale` in HenselianEtaleRetraction:
it is the retraction with trivial residue extension used by the proof, not this
arbitrary R-algebra/filtered-colimit theorem. Upstream Henselian.lean proves the
converse henselian criterion, not this result.

Mismatches repaired: the index binder was `I : Type u`, unnecessarily tied to R;
it now uses the independent universe x. The proof docstring omitted the nine-step
detail; it now carries all steps, including the construction of q', residue
verification, cocone compatibility, elementwise verification and uniqueness,
with their dependency ids. Added the standard copyright header, placed the module
docstring before the namespace, corrected the title (maps into a henselian ring,
from an ind-étale algebra), and removed the redundant ResidueField.Basic import
already supplied by ResidueField.Ideal. No correct residue hypotheses or conclusions
were rewritten. The node's lean.statement was synchronized verbatim with the
signature. There are no definitions or proved auxiliary results: the sole theorem
body is `by sorry`, and no binder or universe is implicit or unbound.

Validation: remote scompile accepted the repaired module without errors or warnings;
the final delivery dry run recompiles it after the redundant import removal.

## Reviewer fix (R-mhc1126)

The index category was `I : Type x` in an independent universe (the second reading had
"repaired" `Type u` to `Type x`). By the FILTERED COLIMITS OF RINGS convention the index
type lives in the rings' universe: `I : Type w`, the universe of `A` and of
`CommAlgCat.{w} R`; `universe x` removed. Nothing else changed: `HenselianLocalRing`
(recorded local form of def-weil-pbc-henselian-terminology), `Algebra.Etale` stages,
`HasColimit`, `IsFiltered`, the prime/residue hypotheses and the `∃!` conclusion match the
node clause by clause; names checked with `#check`.
