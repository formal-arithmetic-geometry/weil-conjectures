## What changed

Replaced the sole sorry in Polynomial.completeLocalFormalFibres with a compiling proof.
Mathlib supplies flatness. For each prime of the localization, the proof uses quotient
transport to a complete local domain, splits the polynomial prime into zero/nonzero,
and in the nonzero case splits the characteristic of the fraction field. The positive
characteristic case uses Polynomial.formalFiber_isGeometricallyRegular from the existing
Sheaf.RingTheory.PolynomialFormalFiber module. Three strictly smaller subarguments are
stated separately, each in a new module with a node and full proof docstring. Existing
signatures and the unit route are unchanged. Imports needed only by the proof are private.

All four files compile using lcompile.py. The main theorem compiles without warnings.

## Proved and sorry left

Closed: Polynomial.completeLocalFormalFibres (one of one original holes).
This is a decomposition, not a completed foundational proof: three new holes were added,
so the delivery's net hole count is minus two, before pruning or existing dependencies.
No sorry remains in the original module. The three new named holes are:

- Polynomial.exists_completeLocalDomain_fibre_reduction:
  lem-weil-pbc-polynomial-complete-local-fibre-reduction. This is only the quotient and
  localization transport step. It contains no assertion that an arbitrary fibre is regular.
- Polynomial.completeLocalGenericFibre:
  lem-weil-pbc-polynomial-complete-local-generic-fibre. This treats only the zero polynomial
  prime over a complete local domain.
- Polynomial.completeLocalNonzeroFibreCharZero:
  lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero. This treats only nonzero
  primes above zero over complete local domains in characteristic zero.

The existing positive-characteristic theorem is still sorry in the repository and is
used as intended by stage 3; this delivery neither adds nor changes its hole.
No definitions, axioms, or arbitrary data obtained from unproved existence were introduced.
The existential transport theorem is eliminated within a proof of a proposition.

Edge cases checked mathematically: a prime of S[X]_Q always contracts inside Q; its
contraction to S is proper and prime, so S/p is a nontrivial domain. If S has nilpotents,
passing to S/p removes them without assuming S itself a domain. A field base is allowed;
its generic fibre is a localization, and its nonzero primes are polynomial hypersurfaces.
The nonzero case requires r intersect A = 0; without that hypothesis its fraction-field
argument would fail. Both characteristic zero and every positive prime characteristic
are covered, including imperfect fields. The generic fibre is allowed to be the zero
ring: geometric regularity permits this since it has no primes. No dimension, perfection,
or characteristic restriction was added to the original theorem.

## No longer needed

Removed direct proof imports from the item:
- Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
- Sheaf.RingTheory.AdicCompletionNoetherian
- Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
- Sheaf.RingTheory.CompleteLocalQuotient
- Sheaf.RingTheory.CompletionRegularLocal
- Sheaf.RingTheory.Derivation.CompletionAndLocalization
- Sheaf.RingTheory.FibreRingNoetherian
- Sheaf.RingTheory.FormalFibreQuasiFiniteAscent
- Sheaf.RingTheory.HypersurfaceDerivationRegular
- Sheaf.RingTheory.LocalCompletionQuotient
- Sheaf.RingTheory.PowerSeriesPolynomialFormalFiber
- Sheaf.RingTheory.RegularLocalLocalization
- Sheaf.RingTheory.RegularRingSmoothAscent

These dependencies are delegated to the full proof plans of the three extracted steps,
not claimed globally unnecessary. The item now directly needs only the three new modules,
PolynomialFormalFiber, and Mathlib's flatness/characteristic machinery. None of the old
mathematical nodes is globally pruned: the generic and characteristic-zero subarguments
still require the regular-subring, quasi-finite-ascent, completion-regularity, localization,
and derivation arguments. The old direct edges are replaced by the new subargument nodes.
No removed import realizes a unit statement or unit proof step in dag/units/sk-thm-p1.json.
Pruned modules: none.

Removed direct proof_deps edges (retained in subargument plans where needed):
- def-weil-pbc-adically-complete-ring
- def-weil-pbc-finite-purely-inseparable-extension
- def-weil-pbc-localization-at-prime
- def-weil-pbc-noetherian-ring
- def-weil-polynomial-ring
- def-weil-regular-scheme
- lem-weil-pbc-adic-completion-noetherian
- lem-weil-pbc-complete-local-domain-finite-over-regular
- lem-weil-pbc-complete-local-quotient
- lem-weil-pbc-completion-regular-local
- lem-weil-pbc-derivation-extends
- lem-weil-pbc-fibre-ring-noetherian
- lem-weil-pbc-finite-algebra-is-integral
- lem-weil-pbc-finite-type-algebra-noetherian
- lem-weil-pbc-formal-fibre-quasi-finite-ascent
- lem-weil-pbc-helper-g-ring-char-p
- lem-weil-pbc-hypersurface-derivation-regular
- lem-weil-pbc-local-completion-local-ring
- lem-weil-pbc-local-completion-quotient
- lem-weil-pbc-localization-at-prime-of-quotient
- lem-weil-pbc-polynomial-ring-domain
- lem-weil-pbc-polynomial-ring-smooth
- lem-weil-pbc-regular-local-localization
- lem-weil-pbc-regular-ring-smooth-ascent
- pqf-def-quasifinite

Second reading restored private proof-dependency imports in all three open subargument
modules, so the targets retain those plans in their import closure.

## Where the brief, the DAG or earlier work was wrong

The original DAG already records the characteristic-zero nonzero-prime gap in the source:
that formal fibre is R/fR, not merely a localization of the completion. The new
characteristic-zero lemma retains the recorded derivation repair (07PE/07PF).
The local checkout lacks literature/stacks-project/more-algebra.tex; the cited source
was read at https://stacks.math.columbia.edu/tag/07PV and
https://stacks.math.columbia.edu/tag/07PU. No literature or coordination file outside
the sandbox was written.

Searches were run through msearch.py (searches.jsonl). LeanSearch was unavailable
(Internal Server Error), recorded as unavailable rather than a no-match claim.
Loogle found AdicCompletion.flat_of_isNoetherian and the regular-polynomial-ring
instance, but no polynomial adic-completion or formal-fibre theorem. LeanFinder returned
smooth/etale-at-prime results, and for transport returned Ideal.Fiber and spectrum-fibre
correspondence; these do not establish the new assertions. Mathlib grep found no formal
fibre or geometric regularity result. The repository and whole blueprint were searched
for duplicate generic, nonzero characteristic-zero and quotient-transport statements;
none was found. Existing 07PU and 07PR declarations are retained as dependencies of the
appropriate arguments, not duplicated. There were no applicable open change records.

## New nodes

lem-weil-pbc-polynomial-complete-local-fibre-reduction:
Sheaf.RingTheory.PolynomialCompleteLocalFibreReduction, the localization/quotient
transport step of 07PV paragraph 2 and 07PN. Its witnesses are the concrete quotient S/p
and image primes; its remaining proof is the canonical fibre identification.

lem-weil-pbc-polynomial-complete-local-generic-fibre:
Sheaf.RingTheory.PolynomialCompleteLocalGenericFibre, the zero-prime subargument of
07PV paragraphs 3--5: regular coefficient subring, quasi-finite ascent, and the two
characteristics, with 07PR used only for the generic positive-characteristic case.

lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero:
Sheaf.RingTheory.PolynomialCompleteLocalNonzeroFibreCharZero, the nonzero-prime
characteristic-zero subargument of 07PV and the 07PU derivation repair. The fraction-field
polynomial is irreducible and separable; its derivative is a unit modulo it.

## Second reading by P1

1. Unchanged interface: compared the complete original module with the repository using
   diff. Only private proof imports and the proof body differ; the public imports,
   universe, namespace, docstring and completeLocalFormalFibres signature are byte-for-byte
   unchanged. There are no definitions or change records. No applicable open change record
   was found by searching coord/changes for the module and declarations. Verdict: passes.
2. Kernel check: all four modules compile cleanly with lcompile.py --all, including after
   restoring plan imports. Scratch copies with #print axioms for each of the four
   declarations report only propext, Classical.choice, Quot.sound and sorryAx. The item
   has no sorry; exactly the three reported public named subarguments have := by sorry.
   No axiom, unsafe, opaque, implemented_by, extern, or hollow definition occurs. The
   existential transport witness is eliminated only into a proposition; no data definition
   chooses a witness. Verdict: passes as a decomposition, not an axiom-free final proof.
3. New statements: read Stacks 07PV, 07PU and 07PP and the actual declarations of
   quotient_complete_local, exists_local_completion_quotient,
   prime_localRing_residueField_iso, complete_local_domain_finite_over_regular,
   isRegular_formalFiber_of_isQuasiFiniteAtPrime,
   formalFiber_polynomial_isGeometricallyRegular, and the derivation/hypersurface lemmas.
   The transport statement asserts only an implication across the quotient S/p fibre
   identity; p is prime and proper even for a nonreduced S. Its witness is S/p in the
   same universe, not an arbitrary regular fibre. The generic statement treats only zero
   in the polynomial domain. The characteristic-zero statement requires r nonzero,
   r <= q and r intersect A = 0, so rK[X] is a nonzero proper prime and its irreducible
   generator has coprime derivative. After finite regular-subring reduction, a zero
   contraction is handled separately. The completed regular ring localized at nonzero
   coefficients gives R, and the nonzero fibre is R/fR, not merely a localization.
   Derivation extension and the unit derivative criterion provide the missing argument
   in the source's characteristic-zero sentence. Fields, zero generic primes, imperfect
   fields of positive characteristic, and nonreduced original coefficient rings satisfy
   the stated reductions. Each assertion is strictly a subargument and has a source,
   complete proof docstring and matching node. New searches with AdicCompletion,
   Ideal.Fiber and quotient/localization transport or characteristic-zero hypersurface
   wording found no replacement: Loogle zero hits; LeanFinder returned smooth/etale locus
   and regular-sequence results, not completion-fibre regularity; Mathlib grep zero hits.
   Repository rg with generic fibre and fibre reduction wording also found no duplicate.
   None of these three sizable transport/regularity proofs can be closed in a few minutes
   by the existing interfaces. Verdict: passes.
4. Route and pruning: the main proof first obtains flatness from Mathlib, then genuinely
   combines quotient transport, zero/nonzero and zero/positive-characteristic splits,
   using the existing 07PU declaration in positive characteristic. Every old proof_deps
   edge removed from the main node is now listed under No longer needed. Read
   dag/units/sk-thm-p1.json: no removed edge realizes its statement or steps and the
   realized route is unchanged. Found missing private proof-plan imports in all three
   new open modules; restored the stated dependencies so their mathematical plans
   remain in the target import closure (stages/2-statements.md rule 7). All four public
   imports remain necessary for the signatures. Pruned modules: none. Verdict: passes
   after repair; one upper hole closed and three lower holes added, net minus two.
5. Nodes: the existing node changes only proof, proof_deps and proof_origin. Its new
   steps match Mathlib flatness, transport and the Lean case split. For each new node,
   checked source, statement dependencies, proof steps, union of uses = proof_deps,
   origin, searches, status split, created/blueprint/chapter/unit and the verbatim Lean
   signature. The quotient, regular-subring, quasi-finite, completion and derivation
   statements cited above provide the facts their steps request. Verdict: passes.

Changes by this reader: restored private dependency imports in the three new modules;
completed the removed-edge list in No longer needed; added this independent review.
The Lean proof bodies and all statements were retained. No additional holes were added
or closed by the second reading. All axiom scratch probes are excluded from delivery.
