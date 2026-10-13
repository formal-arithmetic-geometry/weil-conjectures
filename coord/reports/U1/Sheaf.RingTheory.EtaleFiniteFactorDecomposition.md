## What changed

Replaced the sole sorry in `Algebra.exists_etale_finiteFactor_decomposition` by a
complete strong-induction argument on the number of isolated fibre points. The
proof handles the zero-ring finite factor, composes the canonical residue-field
maps, assembles finite factors by tensor/product equivalences, and preserves the
original universe-polymorphic signature using the actual `ULift` construction.

Added `Sheaf.RingTheory.EtaleIsolatedPointRemoval`. Its public theorem
`Algebra.exists_etale_finiteFactor_smaller_fibre` is proved: choose an isolated
fibre point, apply Mathlib's 00UJ theorem, construct both factors as quotient
rings, transfer finiteness through a localization equivalence, and apply the
complementary-fibre counting lemma. No object is defined by selecting an
arbitrary witness of an unproved existence theorem.

Added `Sheaf.RingTheory.EtaleComplementIsolatedCount`. Its named public theorem
contains the one remaining gap: the strict decrease of isolated fibre points
for an already supplied idempotent and residue-field isomorphism. It neither
constructs an étale extension nor asserts the final non-quasi-finite clause.
The new and existing DAG records follow the actual proof.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_etale_finiteFactor_decomposition`.

Also proved the new theorem
`Algebra.exists_etale_finiteFactor_smaller_fibre`
(node `lem-weil-pbc-etale-isolated-point-removal`).

Added exactly one hole:
`Algebra.fibre_ncard_quotient_idempotent_lt`
(node `lem-weil-pbc-etale-complement-isolated-count`). Its whole proof is
`:= by sorry`, with source and complete proof in words in its docstring.
The private induction helper is fully proved. There are no other delivery holes.
This is a decomposition (one upper hole closed, one strictly smaller lower hole
added), not a sorry-free proof of the target's import closure. The unchanged imported
`AlgebraicGeometry.Spec.finite_setOf_isOpen_singleton_of_finiteType` remains
needed. At second reading its repository source is already proved; the last-green
compiled baseline used by the axiom probe still reports `sorryAx` for it. This
delivery does not change that module or claim credit for its proof.

Every delivered module compiles cleanly via lcompile.py, including the three
modules in import order. The axiom probe and dry-run preflight are also run by
deliver3.py. No theorem/definition signature of an existing declaration changed.

## No longer needed

No original import was removed; no original proof-dependency node is pruned from
this delivery's transitive closure. The one-prime theorem, fibre correspondence,
finite isolated-point theorem, and tensor/product decomposition remain used.
The one-prime theorem's uniqueness clause is unnecessary for this combined-factor
version: a selected isolated prime outside the complementary idempotent factor
already proves strict decrease. This discards no module because Mathlib's 00UJ
module remains needed for its other clauses.

Second reading removed these imports from the new modules: the removal helper
no longer imports Sheaf.RingTheory.QuasiFiniteAtPrime (its signature instead
imports Mathlib.RingTheory.LocalRing.ResidueField.Fiber), nor directly imports
Mathlib.RingTheory.Idempotents; the count module no longer directly imports
Mathlib.RingTheory.LocalRing.ResidueField.Fiber. Each needed interface is still
provided by the remaining imports, so no original module leaves the closure.
The old direct proof-dependency list loses the fibre-prime correspondence and
00UJ nodes only because they are now used transitively through the removal
helper. The old def-weil-etale-morphism is retained as a statement dependency.

The new count module exposes QuasiFinite.Basic and set cardinalities;
QuasiFinite.Basic already exposes residue-field fibres. Etale.QuasiFinite is a private proof import of the new
one-point construction module. All additional imports in the item's module
are private proof imports.

## Where the brief, the DAG or earlier work was wrong

The original DAG refers to `preimageOrderIsoFiber` as transporting topology.
The needed topological interface is `preimageHomeomorphFiber`, present in the
same Mathlib file. The one-point construction uses this actual homeomorphism.

The source Tag 00UK omits the tensor/product verification after induction. It
is now written in Lean, including composition of the canonical residue-field
maps and finiteness of the base-changed finite factor. The remaining gap is
only the complementary-fibre comparison and cardinal decrease; the original
statements are unchanged. No forced adaptations or changes to existing public
interfaces were required.

The source was read at https://stacks.math.columbia.edu/tag/00UK because the
literature source file is absent on this machine. Blueprint unit records were
read; the copied blueprint text directory is likewise absent. The unit route
is unchanged. Whole-blueprint searches for isolated points and idempotents,
plus DAG/library searches for the complementary cardinal statement, found no
existing statement of the new gap. The existing scheme-level isolated point
base-change lemma only gives the forward implication and cannot replace the
residue-field-preserving comparison used here.

LeanSearch returned an internal-server error, recorded in searches.jsonl.
Loogle, LeanFinder and rg were run successfully; the pinned Mathlib source
confirmed 00UJ and the component lemmas but no 00UK simultaneous decomposition
or complementary-fibre cardinal lemma.

## New nodes

`lem-weil-pbc-etale-isolated-point-removal` belongs to
`Sheaf.RingTheory.EtaleIsolatedPointRemoval` and is already proved in this
sandbox. It realizes only the positive-count one-point step. Its finite factor
and complement are actual quotients, not data chosen from an unproved theorem.

`lem-weil-pbc-etale-complement-isolated-count` belongs to
`Sheaf.RingTheory.EtaleComplementIsolatedCount` and is the one new sorry.
It takes the selected quasi-finite prime and idempotent as inputs. It is true
without assuming R→R₁ étale or requiring the finite-factor condition; only the
bijective residue-field map is needed for the fibre comparison. It must be
proved without importing the upper decomposition (which would be circular).
Its proof explains the finite-set injection missing the selected point.

Edge cases checked mathematically: e=1 gives the zero-ring quotient and an
empty complementary spectrum; e=0 cannot satisfy e∉r. An empty original fibre
cannot satisfy the selected-prime hypotheses. For R=k, S=k×k[x], e=(1,0),
q and r the field-factor prime, the isolated-point count decreases from one to
zero. Nilpotents do not affect the spectrum or clopen/idempotent argument.
The count theorem needs no uniqueness assertion for r. The new one-point
helper excludes only zero count, handled explicitly by the induction base case.

No change records are required: no existing signature or existing public import changed.


## Second reading by U1

1. **Existing interfaces: pass.** Read the full diff of the item against the
repository. The complete original public theorem signature is byte for byte
identical, including universes, all witnesses, residue-field bijectivity and the
non-quasi-finite conclusion. The changes are private proof imports, a proved
private induction helper and the theorem body. The two other modules are new;
there are no forced adaptations or changed definitions. Existing DAG changes
are confined to `proof`, `proof_deps`, `proof_origin`.

2. **Proof and axioms: pass as a decomposition.** Compiled all three modules in
import order through lcompile.py without errors or non-sorry warnings. Scanned
all delivered Lean for forbidden declarations and unchecked-kernel options:
none. Exactly one literal `sorry` remains, the entire body of the named count
theorem. No definition contains a hole. Independently compiled a scratch probe
with `#print axioms` for all three public theorems: each uses only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The additional finite-isolated
points probe reports `sorryAx` in the compiled baseline, despite its now-proved
repository source. Reviewed the zero-ring base case, the strong-induction bound,
canonical residue-field composition and tensor/product assembly. Quotients,
ULift and PUnit are actual constructions; the count lemma supplies only a proof
and never selects ring data from unproved arbitrary existence.

3. **Split statements: pass.** Read the entire count statement, its docstring
and its node. The canonical residue-field isomorphism identifies the fibres
compatibly with contraction. The idempotent quotient is a clopen subspace, so
its isolated points inject into the ambient isolated points. The selected prime
is isolated by quasi-finiteness and is absent from this subspace. Finite type
makes the ambient isolated set finite, giving strict decrease. No étaleness or
finite-factor hypothesis is needed for this comparison. Checked e=1 (empty
quotient spectrum), e=0 (avoidance impossible), empty original fibre (selected
prime impossible), S=k[x] (no selected quasi-finite prime), S=k×k[x] with the
field-factor idempotent (one isolated point removed), and S=k×k (two to one).
Neither new statement restates the final theorem: the proved removal step
supplies strictly smaller count, and the sole new hole supplies only the
comparison for already-given rings, primes and idempotent. Independent
LeanFinder, Loogle and rg searches with different wording found components,
not an existing theorem of this exact strength. In particular
`Ideal.ncard_primesOver_quotient_singleton_lt_of_notMem` counts **all** primes
and requires that full set finite; that fails for the k[x] complementary factor
and cannot replace the isolated-point comparison. The tensor fibre isomorphism
inside `Ideal.fiberIsoOfBijectiveResidueField` confirms the comparison route.
Formalizing its topology and clopen quotient comparison is substantial enough
that this reading leaves the named, documented gap rather than rewriting the
working reduction.

4. **Route and pruning: pass after import repair.** Read Stacks Tag 00UK and
Mathlib's 00UJ construction, fibre comparison and quotient cardinal lemmas.
The proof follows the prescribed induction and retains the unit `sk-thm-p1`
route; no node in that unit's `realized` statement or steps is bypassed or
edited. Compared every old proof dependency: the fibre-prime correspondence
and 00UJ node have moved to the removal helper and remain transitive proof
dependencies. `def-weil-etale-morphism` is no longer a direct proof dependency
but remains an original statement dependency; the proof uses the existing
Algebra.Etale identity/composition infrastructure. The other old dependencies
remain directly used. Thus no original dependency module is pruned from the
closure. Removed the new helper's unnecessary public import of
`Sheaf.RingTheory.QuasiFiniteAtPrime`, exposing its actual signature dependency
`Mathlib.RingTheory.LocalRing.ResidueField.Fiber` instead. Also removed the count
module's redundant direct Fiber import and the removal helper's redundant
proof import of Idempotents, already supplied by Localization.Away.Lemmas.
A trial removal of Localization.Away.Lemmas failed because it supplies the
quotient/localization instance theorem; restored that necessary proof import. These removals prune no original closure module.

5. **DAG: pass.** Read all three delivered nodes and the original node. The
updated original proof records the actual ULift, strong induction, zero factor,
residue-field composition and tensor/product equivalences. The removal node
records the actual quotient constructions, 00UJ application and count-lemma
call. The count node records the remaining mathematical proof plan without
asserting an induction or an étale construction. Their dependency lists are
the unions of the recorded steps; new nodes have source, complete statement,
searches, creation provenance, blueprint ancestry, chapter/unit and matching
Lean signatures. No statement-change record is needed.

Second reading changed imports and corrected the report's description of the
finite-isolated-points baseline. It added independent search, signature and
axiom evidence. No existing statement, definition, proof body, unit realization
or number of delivery holes was changed. Net holes closed minus holes added
for this delivery is zero: one original hole closed, one lower hole added.
