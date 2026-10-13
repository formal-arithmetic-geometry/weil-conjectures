## What changed

Repaired the duplicate-theorem return in
`lean/Sheaf/RingTheory/QuasiFiniteLocusOpen.lean`: removed the private
`Algebra.isQuasiFiniteAtPrime_iff_fiber` declaration, added the proof-only
`import all Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization`, and replaced
both uses with the existing private `Algebra.isQuasiFiniteAtPrime_iff_isOpen_fiber`.
Lean's `import all` makes the existing private theorem available without changing
its visibility or any other module. No dependency module is edited.

The proof of `Algebra.isOpen_isQuasiFiniteAtPrime` still constructs local witnesses
using the proved finite-subalgebra-away theorem. Mathlib quasi-finite instances and
surjectivity make the localized fibre spectra discrete. The remaining private
`Algebra.isQuasiFiniteAtPrime_comap_away` restricts the localization open embedding
to the fibre and uses the imported equivalence twice. Basic opens then prove
openness. The public theorem's signature and visibility are unchanged.

Updated the item's DAG proof step 3, `proof_deps`, and `proof_origin` to record
reuse of the principal-localization module's fibre equivalence. Restored that
node as a dependency. No definitions, public imports, new nodes or interfaces
changed, and no forced adaptations or change records are necessary.

The source route remains Stacks Tag 00QA, `lemma-quasi-finite-open`, with the
localization argument from Tag 077H, `lemma-quasi-finite-local`. Read the existing
principal-localization module, its node, and `dag/units/sk-thm-p1.json` during the
repair. The item and pruned finite-ring-map node realize no unit statement or
step; the unit route is retained. The original delivery's searches through
`msearch.py` (LeanFinder, Loogle and grep) remain in `searches.jsonl`.

## Proved and sorry left

Closed the sole original hole: `Algebra.isOpen_isQuasiFiniteAtPrime`, node
`lem-weil-pbc-ring-quasi-finite-locus-open`. Closed 1 hole; added 0 holes; split off
0 statements. No `sorry` remains in the delivered module, and no new module is
added. The remaining private helper `Algebra.isQuasiFiniteAtPrime_comap_away` is
proved; the duplicate fibre helper is deleted rather than renamed or inlined.

The repaired module compiles cleanly through `lcompile.py`. The delivery dry run
checks the axioms of every added declaration. Empty spectra and zero rings need
no extra hypotheses: universal assertions over empty spectra are vacuous, and
chosen localization witnesses avoid an existing prime.

## No longer needed

Removed proof import `Sheaf.RingTheory.FiniteRingMapQuasiFinite`, node
`lem-weil-pbc-finite-ring-map-quasi-finite`. Mathlib's proved finite-algebra and
localization quasi-finite instances, `QuasiFinite.of_surjective_algHom`, and
`isOpen_discrete` give the required conclusion directly. Its node is removed
from this item's `proof_deps`.

`Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization` and its node
`lem-weil-pbc-quasi-finite-at-prime-principal-localization` are needed again:
the existing fibre equivalence is reused with `import all`. The earlier report's
claim that this module was pruned is withdrawn. Its more general public
base-and-target localization theorem is not used by this proof.

The remaining topology is supplied by Mathlib's
`PrimeSpectrum.localization_away_isOpenEmbedding`,
`PrimeSpectrum.localization_away_comap_range`, and the imported fibre equivalence.
No other imports or nodes are pruned. No project-wide unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private fibre equivalence already proved in
`Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization`. The earlier second
reading incorrectly concluded that a private theorem could not be imported for
reuse. A scratch module with `import all` and `#check` confirmed that the existing
name resolves and has the required type. Removed the duplicate, imported the
existing theorem, and restored the dependency in the DAG and pruning report.

The obsolete second-reading section is removed so the independent second reader
can review the repaired delivery afresh. No mathematical statement was changed.

## Second reading by S2

1. **Interfaces: pass.** Compared the delivered Lean file and node with the
   repository using `diff -u`. The existing declaration
   `Algebra.isOpen_isQuasiFiniteAtPrime` has a byte-for-byte identical signature,
   including both conjuncts, the finite-type hypothesis, and the universal local
   characterization. No definition or visibility changes. The only added
   declaration is the proved private contraction helper; no other module is edited.
   Read [Stacks 00QA](https://stacks.math.columbia.edu/tag/00QA) and
   [Stacks 077H](https://stacks.math.columbia.edu/tag/077H): the rings are arbitrary
   commutative rings, with only the stated finite-type assumption. The local
   witnesses in the second conjunct are precisely those constructed in 00QA's proof.

2. **Proof and trust: pass.** Compiled the entire delivered file with
   `lcompile.py`, cleanly in 3.3 seconds. A scratch copy with `#print axioms` for
   the public theorem, the private contraction helper, and the imported fibre
   equivalence reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
   No `sorry`, axiom, unsafe declaration, opaque declaration, external
   implementation, or definition is added. Read the finite-subalgebra theorem
   and its Zariski-main dependency: the witness comes from a proved theorem, so
   there is no data chosen from an unproved existence assertion.

3. **New statements: pass.** There are no split-off statements or new nodes.
   The proved private helper is a strict localization-descent step, not a renamed
   target. Its scalar-tower square identifies the two fibres; restricting the
   localization open embedding sends the open singleton to the contracted
   singleton. This requires no nonzero-ring assumption: empty spectra give
   vacuous universal claims; the local witness avoids its prime, so an element
   whose localization is the zero ring cannot be used at that point. The existing
   private fibre equivalence is reused through `import all`, not duplicated.

4. **Route and pruning: pass.** Read the two imported Sheaf proof modules and
   searched the pinned Mathlib ring-theory sources and both library roots for
   openness, quasi-finiteness, and isolated-fibre formulations; also ran
   `msearch.py ... grep "isolated fiber localization open quasi finite"`.
   The scheme openness result would require a comparison and does not shorten
   this ring proof. Module finiteness, localization, and surjectivity supply
   Mathlib's quasi-finite instances directly, with discrete fibre spectra.
   Verified the old/new `proof_deps`: the sole removed node is
   `lem-weil-pbc-finite-ring-map-quasi-finite`, already listed above. The
   principal-localization module remains needed for its private equivalence.
   Removing the proof-only `Mathlib.RingTheory.QuasiFinite.Basic` import in a
   scratch copy produces unknown quasi-finite declarations and a missing
   discrete-topology instance, confirming it is needed. The public imports
   supply the predicate and localization/finite-type data used in the signature.
   Read `dag/units/sk-thm-p1.json`: neither the item nor the pruned node occurs in
   its `realized` statement or steps; that route remains intact.

5. **DAG: pass.** The five proof steps match, respectively, the finite-subalgebra
   witness, Mathlib instance and surjectivity transfer, the imported fibre
   equivalence, the open-embedding restriction helper, and the basic-open basis
   argument. `proof_deps` is the union of their uses; `proof_origin` records the
   actual repaired route. All other node fields, including `statement`,
   `stmt_deps`, and the Lean signature record, remain identical to the repository.
   No new-node or change-record obligations arise.

**Changes by this reader:** appended this independent review and retained the
already-correct Lean proof and DAG unchanged. Confirmed 1 original hole closed,
0 holes added, 0 statements split off, and the finite-ring-map dependency pruned.
