## What changed

Proved `FormalGlueing.exists_map_to_algebraization` with its signature unchanged.
Added proof-only imports of `Sheaf.RingTheory.IdealPowerTorsionLocalizationCriterion`
and `Sheaf.RingTheory.FormalGlueingReplacePrimeTo`. Both new modules are fully proved.
No existing definition, statement, visibility, or public import was changed.
The redundant direct proof-only import of `FormalGlueingData` was removed.

The main proof chooses finite generators, detects local bijectivity, replaces the
prime component of the canonical datum, and uses the existing canonical-equivalence
theorem for essential surjectivity and fullness. It explicitly projects categorical
isomorphisms to prime and chart components, handles bundled-object equalities and
heterogeneous map equalities, obtains the factorization, and detects descended torsion.
The arbitrary existential choice of T occurs only inside a theorem proof, not a definition.

The criterion uses Mathlib's localization of kernels and cokernels, and the radical
power lemma for the annihilator of an element. The replacement construction is real
Lean data, with the square checked using localization composition and a proved
naturality lemma for interchange. Its cocycle is the old cocycle.

All three modules compile cleanly in import order using lcompile.py. Compilation
takes approximately 7–16 seconds per module, without changing heartbeat limits.

## Proved and sorry left

Closed the single original hole:
`FormalGlueing.exists_map_to_algebraization`
(node `lem-weil-pbc-formal-glueing-map-to-algebraization`).

Added and proved (zero new holes):
- `FormalGlueing.idealPowerTorsion_iff_localMap_bijective`
  (node `lem-weil-pbc-ideal-power-torsion-localization-criterion`).
- `FormalGlueing.exists_replace_prime_to`
  (node `lem-weil-pbc-formal-glueing-replace-prime-to`).

Every private helper is proved. No sorry remains in any delivered module.
The main theorem still depends on existing open declarations through
`FormalGlueing.exists_canonical_equivalence`; that theorem now has a proof in the
repository, but its import closure remains open. This dependency is explicitly
intended by stage 3 and is not a newly added hole. This delivery closes one hole, adds zero,
and is not a decomposition into unproved new statements.

## No longer needed

The redundant direct proof-only import of `Sheaf.RingTheory.FormalGlueingData`
is removed from the main module; its public interface is already available through
`FormalGlueingEquivalence` and `FormalGlueingReplacePrimeTo`. The data node remains
used. No library module is pruned from the target closure. The original direct dependency
`lem-weil-pbc-localization-module-exact` is no longer used directly by the main
theorem: its kernel/cokernel argument is supplied by the fully proved localization
criterion, which records that dependency. This is factoring of the argument, not
removal from the dependency closure. The other original proof dependencies remain:
formal glueing data, localization away, and the canonical equivalence. Localization
away is explicitly retained in the main node for its private localized-map helpers. The explicit monomial enumeration in the original plan
is replaced by the existing Mathlib radical-power lemma, represented by
`lem-weil-pbc-fg-ideal-radical-power`. This does not bypass any unit statement or step.
The item is not a realized statement or step of `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing return: the current library already contains
`FormalGlueing.exists_replace_prime` in `Sheaf.RingTheory.FormalGlueingReplacePrime`,
with a map from the old prime component to Q (0ALK part (2)). The prior delivery
used the same names for the opposite map direction (0ALK part (1)). The current
library theorem, file, and node are preserved. The incoming-map construction now
has its own module `Sheaf.RingTheory.FormalGlueingReplacePrimeTo`, declaration
`FormalGlueing.exists_replace_prime_to`, and node
`lem-weil-pbc-formal-glueing-replace-prime-to`. The main proof and dependency record
use these names. No adaptation of the landed module or any caller is required.
The prior second reading concerned the old packet and was removed for a fresh reading.

No mathematical statement error found. Lean's `extend (algebraMap R S)` uses the
algebra structure reconstructed from the ring homomorphism; it is propositionally,
but not always definitionally, the ambient algebra instance. Explicit transport
lemmas normalize the bundled tensor module and base-change map. Restriction of
scalars has the corresponding module-instance issue, handled by proved transport
lemmas. No interface repair was necessary.

The local repository lacks the Stacks TeX source file at the recorded literature
path. Read the actual source online at https://stacks.math.columbia.edu/tag/0ALK
and https://stacks.math.columbia.edu/tag/05EL. The node retains the project's
canonical document path and records the source access. The blueprint ancestor
script returns None for this recently created item's module-valued created.item;
the existing parent's blueprint.from explicitly identifies
`thm-weil-pbc-finite-etale-lifting`, which the new nodes inherit with the via chain.
Blueprint searches for formal glueing, glueing, 0ALK, and torsion localization found
no duplicate blueprint statement.

Edge cases checked in the arguments: empty generator family (I=0), a unit generator
(I=top), zero maps and zero modules. Empty charts make the replacement construction
and its compatibility conditions vacuous, and the torsion criterion uses the zero
ideal's first power. A unit chart forces the kernel and cokernel to be zero.
No nonzero-ring, nonempty-family, finite-module, or faithful-flatness hypothesis is added.

## New nodes

`lem-weil-pbc-ideal-power-torsion-localization-criterion`, in
`Sheaf.RingTheory.IdealPowerTorsionLocalizationCriterion`, states and proves the
finite-chart criterion for torsion kernel and cokernel. It is independent of S and
flatness, serves steps 1 and 4 of the original plan, and cites the existing radical
power and localization exactness nodes.

`lem-weil-pbc-formal-glueing-replace-prime-to`, in
`Sheaf.RingTheory.FormalGlueingReplacePrimeTo`, states and proves replacement of a
prime component along any locally invertible map, together with a morphism whose
charts are bijective. It serves step 2, with no descent or flatness hypothesis.

Both new statements are strictly smaller than the item and have complete proofs.
Their Mathlib searches were run with msearch.py and recorded in searches.jsonl;
LeanSearch returned HTTP Internal Server Error and is marked unavailable.
No change records or forced adaptations are needed.


## Second reading by U2

1. Compared all delivered modules against the read-only repository. The only
   existing module is FormalGlueingMapToAlgebraization; its complete theorem
   signature, public imports, visibility and pre-existing definitions are unchanged
   byte for byte. Its new helpers are private. The two new modules have distinct
   names; the landed opposite-direction FormalGlueingReplacePrime is untouched.
   Verdict: pass; no change record required.
2. Read every proof in all three modules and compiled the complete packet in import
   order, cleanly. No sorry, axiom, unsafe, opaque, implemented_by or extern occurs
   in the delivered Lean. The replacement datum is explicitly constructed, with
   its square and cocycle proved; no definition chooses arbitrary existential
   data from an open theorem. The existential choice of T is inside the main
   theorem proof. Axiom checks are recorded below. Verdict: pass; the kernel checks below passed.
3. Both new public statements are strictly smaller than the main theorem and are
   fully proved, not split-off holes. Checked the finite-family criterion at t=0,
   at zero and unit generators, and for zero modules/maps: zero ideals kill every
   element at exponent 1, zero charts impose no restriction, and a unit chart
   forces both kernel and cokernel to vanish. The replacement works with no charts
   or collapsed zero charts and imposes no flatness. Read their docstring arguments
   against Stacks 0ALK (part 1) and 05EL. Repeated LeanFinder with queries about
   annihilated kernel/cokernel and incoming local isomorphisms, and grep on the
   repository and Mathlib for localization/torsion, replacements and interchange.
   Related private helpers in FormalGlueingMapFromAlgebraization and the opposite
   map direction in FormalGlueingReplacePrime cannot be applied to these statements.
   Mathlib supplies the kernel/cokernel localization and radical-power ingredients,
   but no exact public replacement for either new lemma. Verdict: pass.
4. The proof opens the original hole, uses Mathlib for finite generation and torsion
   detection, and applies the existing canonical equivalence for descent. No new
   unproved theorem merely restates the item. Public imports support the signatures;
   new proof dependencies are plain imports. The redundant direct Data import is
   removed; that node remains used through the equivalence and replacement. Checked
   all four old proof_deps: localization exactness moves into the proved criterion,
   and the other three remain used. No module leaves the target import closure.
   Inspected sk-thm-p1.realized: the item realizes neither its statement nor a step;
   no unit realization or route is bypassed. Verdict: pass.
5. Compared each node's statement, proof steps, proof_deps and proof_origin with
   its Lean proof. New nodes have sources, self-contained statements, searches,
   chapter/unit, blueprint ancestor chains, created records and verbatim signatures.
   The main node correctly records replacement, finite-chart detection and descent;
   the criterion records radical powers and exact localization. Verdict: pass.

Changes in the second reading: corrected two stale report claims: the canonical
equivalence now has a proof but still rests on upstream holes, and the direct Data
import was removed even though no module was pruned. No Lean or DAG repair was
needed. Updated the scratch axiom probes to the incoming-map theorem's new name;
all scratch work stays outside the delivery.

Axiom probes: scratch copies of all three delivered modules compiled in import order
with `#print axioms` appended. `FormalGlueing.exists_replace_prime_to` and
`FormalGlueing.idealPowerTorsion_iff_localMap_bijective` report only `propext`,
`Classical.choice` and `Quot.sound`. `FormalGlueing.exists_map_to_algebraization`
reports these plus `sorryAx`, through the pre-existing open descent dependencies.
No unexpected axiom appears. Shared compile-slot contention made the final probe
wait about fifteen minutes; the proof itself compiled within its per-file limit.

Delivery dry run: `deliver3.py U2 Sheaf.RingTheory.FormalGlueingMapToAlgebraization --no-push` printed OK; compilation and preflight passed (CODEX, new proved modules/nodes and repair of a returned delivery).
