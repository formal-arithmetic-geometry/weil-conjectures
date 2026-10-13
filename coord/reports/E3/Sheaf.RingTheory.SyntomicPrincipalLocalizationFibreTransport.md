## What changed

Proved `Algebra.exists_completeIntersection_fibre_transport` with its signature unchanged.
The returned delivery duplicated `Algebra.globalCI_equiv` from
`Sheaf.RingTheory.SmoothLocalCompleteIntersection`. Removed that private helper and added
`import all Sheaf.RingTheory.SmoothLocalCompleteIntersection`, a proof-only import that
makes the existing private theorem available. Both equivalence transports now use it.
The smooth-algebra theorem itself is not applied. No other module is changed.

Retained three proved private helpers for commuting principal localizations, transport
along equality of base primes, and the fibre comparison at a fixed base prime.
The comparison uses the inverse of `PrimeSpectrum.preimageEquivFiber` and Mathlib's
tensor-localization equivalence, avoiding residue-field comparisons. Updated the node's
proof, proof dependencies and proof origin to record the reused helper and its module.

## Proved and sorry left

Closed: `Algebra.exists_completeIntersection_fibre_transport`
(node `lem-weil-pbc-syntomic-principal-localization-fibre-transport`), the module's only hole.
No sorry remains in this module. No holes or new modules are added: one hole closed,
zero holes added, zero split off. All three remaining private helpers are fully proved.
The existing dependency `Algebra.isGlobalCompleteIntersection_localizationAway` still
has sorry in its own module; this delivery does not prove that dependency.

## No longer needed

Removed the original proof import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`.
Neither node `lem-weil-pbc-localization-prime-residue-field-iso` nor that module is needed
by this proof: the inverse fibre equivalence identifies the prime by contraction.
Removed the duplicate local `Algebra.globalCI_equiv` proof; its existing version is reused.
The original remaining proof dependencies are still needed. The new SmoothLocalCompleteIntersection
import is needed solely for its proved private equivalence helper. No unit statement or
realized step is bypassed; the removed residue-field comparison is below the unit level.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified a duplicate theorem. The earlier second reading wrongly
concluded that private helpers were inaccessible: Lean's `import all` permits reusing
this helper without changing its visibility or adapting its original module. The repair
removes the duplicate rather than renaming or reproving it.

The original local-ring/residue-field route is valid but unnecessary. Mathlib's canonical
fibre equivalence supplies a shorter comparison. No statement or definition was changed.
The hypothesis `hg` is redundant once the prime `q₁` and its contraction equality are
supplied; its binder remains unchanged and is explicitly referenced in the proof.

## Second reading by E3

1. Interface: PASS. Diffed the sole delivered module against the repository and
   compared the complete existing theorem signature byte for byte through `:= by`.
   All binders, universe parameters, hypotheses, fibre primes and the conclusion
   are unchanged. Both public imports remain unchanged; the new imports are
   proof-only. There are no definition changes, other delivered modules, or
   change records. The three added theorems are private and fully proved.
2. Proof: PASS, relative to the existing open principal-localization theorem.
   The delivered module compiles cleanly using lcompile.py. Regenerated a scratch
   copy from the current delivery (the old scratch still contained the removed
   duplicate) and printed axioms for the target and all private helpers.
   The reused globalCI_equiv and equality-rebase helper use only propext,
   Classical.choice and Quot.sound. The other two helpers and the target also
   use sorryAx through isGlobalCompleteIntersection_localizationAway, whose
   named hole remains upstream. There is no local sorry, axiom, unsafe, opaque,
   extern, implemented_by, definition, or arbitrary data chosen from an
   unproved existence theorem. The witness is explicitly e.symm (h/1), chosen
   from the proved implication's input hci.
3. Split statements: PASS (none). Checked the three proved private helpers
   directly: equality rebasing is substitution; the double localization
   comparison is an algebra equivalence for the same powers of a*h; the
   fixed-base comparison identifies contracted primes by injectivity of the
   inverse canonical fibre equivalence. In particular, the inverse map in
   Mathlib's preimageEquivFiber is contraction along includeRight, and the
   base-change pure-tensor formula proves the required compatibility. The
   cases g=1 and invertible h recover the original neighbourhood; g=0 or a
   zero source ring cannot supply the required prime; localizing to zero
   remains covered by the definition's zero-ring clause. No finiteness,
   nonzero-ring or extra flatness hypothesis enters the proof.
4. Route and pruning: PASS. Read the replacement sentence of Stacks
   [00SY](https://stacks.math.columbia.edu/tag/00SY) (3) implies (2), and
   principal-localization stability in
   [00SA](https://stacks.math.columbia.edu/tag/00SA) (1); the local literature
   file is absent on this machine, so read the official tag pages. Searched
   the RingTheory sources for equivalence and fibre-transport declarations
   and ran Loogle with "preimageEquivFiber": its inverse formula is the
   existing ingredient, not an exact CI transport theorem. Reuse of the
   existing globalCI_equiv avoids duplication. All five imports are needed:
   the two public ones provide signature notions; the three proof-only ones
   provide principal-localization stability, tensor base change, and the
   existing equivalence helper. The report lists the sole removed old
   dependency, LocalizationPrimeResidueFieldIso and its node. Read
   dag/units/sk-thm-p1.json: neither that removed node nor this auxiliary
   node realizes a unit statement or step, and the realized route is kept.
5. DAG: PASS. Diffed the sole node file: only proof, proof_deps and
   proof_origin change. The statement and lean.statement stay unchanged.
   The uses union equals proof_deps: tensor localization supplies the fibre
   equivalence, localization-of-localization supplies the double-localization
   comparison, and principal-localization stability supplies the remaining
   open CI fact. The SmoothLocalCompleteIntersection dependency explicitly
   records reuse of its proved private helper, not application of its smooth
   theorem. The elementary prime-comparison step is justified by the
   displayed pure-tensor calculation and the inverse equivalence. No new
   nodes require creation-field or search-log checks.

Second reading changed no delivered Lean or DAG code: the repair is correct
as written. Regenerated the stale axiom-check scratch file and added this
independent review. One existing hole closed, zero holes added, zero split
off; no claim that the target is axiom-closed while its localization
dependency remains open.
