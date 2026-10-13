## What changed

Replaced the sorry in Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization
with a complete Lean combination using IsLocalizedModule.Away.mk_of_addCommGroup.
Proved the unit field directly: RingedSpace.isUnit_res_basicOpen gives a unit after
restriction, IsUnit.smul_bijective gives bijective scalar multiplication, and
Module.End.isUnit_iff gives invertibility of the scalar endomorphism over Γ(T,W).
This proof uses the actual restriction-of-scalars module instance from the statement.

Split the two remaining cohomological steps into separate modules:
Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalDenominators and
Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalTorsion. Their statements are
respectively the image and zero-kernel assertions. Neither is the localization
statement under a new name. No existing signature, definition, or public import
changed. Both new modules retain InvertSCOhomology as the planned comparison;
the torsion module also retains CohomologyFractionEventuallyZero for the existing
proved zero criterion. Updated the parent node's proof route to the Lean proof.

Validation: lcompile.py --all compiled all three modules without errors or warnings.
The checked edge cases are a=0 (target on the empty open is zero; kernel killed by
exponent 1), unit a (restriction is an isomorphism), q=0, empty W and F=0.
The final deliver3.py --no-push run is the required delivery validation.

## Proved and sorry left

Closed the item's one hole:
AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_isLocalized_away
(lem-pc-section-cohomology-principal-localization).
No sorry remains in the item's module.

Added two holes, both named public theorems with complete proof docstrings:

- AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_pow_lifts
  (lem-pc-section-cohomology-principal-denominators).
- AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_pow_annihilates
  (lem-pc-section-cohomology-principal-torsion).

This is a decomposition, not a net hole-count improvement: one hole closed and
two added. The invertibility part is proved outright, and the algebraic combination
of the two remaining parts is proved. No hole was added inside a definition.

## No longer needed

Removed the item's direct proof import Sheaf.AlgebraicGeometry.InvertSCOhomology.
It is still required transitively by both new modules, so no claim is made that
InvertSCOhomology or its underlying proof modules leave the targets' closure.
The parent no longer directly cites lem-sc-invert-s-cohomology or
 def-pc-morphism-conventions in proof_deps; the new nodes retain them where needed.
No transitive module is pruned by this decomposition. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface change was found. The former second proof step
bundled a substantial raw resolution/tensor-unit comparison, finite denominator
normal form, and zero criterion. InvertSCOhomology supplies an additive equivalence
on a qcqs scheme, not an IsLocalizedModule instance on raw section cohomology.
The new statements isolate its image and kernel consequences with the scalar and
restriction identifications written explicitly in their proof descriptions.
Invertibility itself needs none of that comparison and follows from Mathlib.

Read the Stacks Project pages for Tags 09MR and 01E4. Searches: LeanSearch was
unavailable (Internal Server Error), so no absence verdict is claimed for it;
LeanFinder returned tilde section/localization and sheaf-cohomology infrastructure;
Loogle returned the localization predicate and generic module local properties.
Repository and Mathlib grep found no independent raw denominator or kernel theorem.
The higher-image denominator/torsion modules are about sheafified values and depend
on the present item, so using them here would introduce an import cycle.
The unit sk-thm-picard-coherence has empty realized fields; no unit statement or
step was bypassed or changed. The original localization route remains below it.

## New nodes

lem-pc-section-cohomology-principal-denominators states only that every target
class has a numerator after multiplication by a power. Its proof extracts a single
fraction from the finite sum presentation and transports the canonical equation of
09MR through the resolution section identifications of 01E4.

lem-pc-section-cohomology-principal-torsion states only that a source class with
zero restriction is killed by a power. Its proof uses injectivity in 09MR and the
existing cohomologyFraction_eventually_zero theorem. No surjectivity is asserted.
Both nodes inherit the parent's chapter, unit and blueprint ancestry, record all
three kinds of search, and include verbatim Lean signatures. No change records
are necessary because every existing statement and definition is unchanged.

## Second reading by Q2

1. Interface: PASS. Diffed the delivered parent against the repository. Its existing
   theorem signature is byte-for-byte identical, including the local restriction-of-scalars
   instance. Its docstring, definitions and public imports are unchanged. Only its proof and
   private proof imports changed. The two other modules are new; no change record is needed.
2. Proof and trust: PASS as a decomposition. Independently ran lcompile.py --all: all three
   modules compiled without warnings or errors. Scratch copies with #print axioms for all
   three declarations showed exactly propext, Classical.choice, Quot.sound and sorryAx.
   The parent still depends on the two open lower theorems; it is not axiom-free completion.
   There are exactly two textual sorries, each a named public theorem with its matching node
   and full proof docstring. No data definition, axiom, unsafe/opaque declaration or foreign
   implementation was introduced. No arbitrary object is chosen from unproved existence.
3. New statements: PASS. Read both statements, proof docstrings, nodes, invertS_cohomology
   and cohomologyFraction_eventually_zero. Verified their source against Stacks Tags 09MR
   and 01E4. Restriction of injectives to an open computes these raw section groups, and
   its degreewise pushforward identifications preserve restriction and the pulled-back
   scalar action. The fraction comparison gives the image equation; its injectivity and
   the proved zero criterion give the kernel equation. Neither statement repeats the full
   localization property. Independently checked a=0 (empty target, kernel killed by a),
   unit a (identity open and exponent zero), q=0, empty W and zero F. Fresh LeanFinder
   search for restriction of derived sections with power-torsion kernel found only
   structure-sheaf section lemmas, not a raw cohomology bridge. Fresh Loogle confirmed
   Away.mk_of_addCommGroup has exactly the three fields used. Repository/upstream and
   Mathlib searches for sectionCohomologyPresheaf, cohomology localization and power
   lifting/torsion found no usable duplicate: the higher-image versions depend on this
   item. Closing either remaining hole requires the substantial resolution/tensor-unit
   identifications, not a short application of an available theorem.
4. Route and pruning: PASS. The parent uses Mathlib directly for invertibility and the
   algebraic combination, and the planned comparison remains in the new lower modules.
   All statement imports are needed for their signatures; lower comparison imports are
   private and intentionally retained for their stated unfinished proofs. The removed
   direct InvertSCOhomology import and both old dependencies are accounted for under
   No longer needed. InvertSCOhomology remains transitively reachable; no module is
   pruned from the target closure. The unit sk-thm-picard-coherence has empty realized
   statement/step arrays; its record and its route were not altered or bypassed.
5. DAG: PASS. Parent changes only proof, proof_deps and proof_origin. Checked every
   node's Lean signature against its module verbatim, and every proof_deps against the
   union of the proof steps' uses. Both new nodes have the required source, searches,
   creation metadata, chapter/unit, blueprint ancestry and Lean records.

Second reading changed only this report: added the independent review and explicit
axiom-check evidence. No Lean or DAG repair was necessary. Counts remain one upper
hole closed and two strictly partial lower holes added (net -1, a decomposition).
