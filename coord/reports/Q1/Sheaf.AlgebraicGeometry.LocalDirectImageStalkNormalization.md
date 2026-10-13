## What changed

Completed the existing reduction of
AlgebraicGeometry.localDirectImage_stalk_cohomology_normalization without changing
its signature. The private helpers prove cohomology-map invertibility for an
isomorphism, pushforward equivalence, and invertibility of restriction to the top
open. The proof uses the local-spectrum open equality, surjectivity of restriction,
the forward class compatibility theorem, and the supplied equation for e.
Added proof-only imports LocalDirectImageStalkClassRestriction and Mathlib's
DerivedCategory.KInjective. Scoped maxHeartbeats to the normalization theorem:
its nested types exceed the default 200000 heartbeats.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.localDirectImage_stalk_cohomology_normalization.
No sorry remains in the item's module. Added one strictly lower hole:
AlgebraicGeometry.localDirectImage_stalk_class_restriction
(node lem-weil-pbc-local-direct-image-stalk-class-restriction).
This is a decomposition (one hole closed, one added), not a net hole reduction.
The forward compatibility statement has no equivalence or inverse hypothesis;
restriction invertibility and the inverse normalization are proved in this delivery.

## No longer needed

No existing import was removed. The proof does not need the planned local-spectrum
helper module Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism: Mathlib's
Scheme.range_fromSpecStalk and specialization membership prove the open equality
directly. The old proof dependencies
 def-weil-pbc-local-direct-image-stalk-class-map and
 def-weil-pbc-flat-base-change-resolution-construction are no longer used as
 direct proof steps of normalization: their compatibility work is now in
 lem-weil-pbc-local-direct-image-stalk-class-restriction. Their modules remain
 needed for the unchanged signature and the new lemma; they are not pruned from
 the target import closure. The removed dependency
 lem-weil-pbc-spec-local-ring-canonical-morphism is replaced by Mathlib's
 Scheme.range_fromSpecStalk. No module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt reported a 60-second timeout. The preserved proof instead
failed at the default deterministic heartbeat limit. Raising that limit locally
allows compilation within the required time budget; no definition change or
file splitting is needed. The forward compatibility theorem remains deferred.

## New nodes

lem-weil-pbc-local-direct-image-stalk-class-restriction records compatibility of
the forward canonical class map with restriction and the supplied target resolution.
Its source and complete natural-language proof are in its docstring and node.
The normalization node's proof and dependencies record the actual reduction.
No change record is necessary: all existing signatures and visibility are unchanged.

## Second reading by Q1

1. Compared both delivered modules with the repository. The restriction module
   is new. The normalization theorem's entire signature is byte-identical;
   its existing documentation and public imports are unchanged. No definition
   is changed and no change record is required. Verdict: pass.
2. Compiled both modules individually with lcompile.py: clean, about 2 and 21
   seconds respectively. A scratch copy with #print axioms for both public
   theorems reports only propext, Classical.choice, Quot.sound and sorryAx.
   Normalization has no local sorry; the only added hole is the named forward
   compatibility theorem listed above. No forbidden declaration, hollow
   definition or new arbitrary-witness construction occurs. Verdict: pass,
   conditional on the explicitly recorded open compatibility theorem.
3. Read the new statement against localDirectImage_stalk_class,
   RestrictedResolutionSections, resolutionSectionClass and targetClass, and
   checked Stacks Tags 01E4 and 01FB. The augmentation pins the comparison and
   the components pin the section map; no arbitrary resolution automorphism
   can alter the induced class. Degree zero uses the same augmentation square;
   zero classes map to zero, and the zero module is harmless. The lemma is
   forward compatibility, with no e or inverse hypothesis, strictly one part
   of the original argument. Searched lean/Sheaf and lean/WeilConjectures for
   targetClass, stalk_class, restriction isomorphisms and cohomology-map
   isomorphisms, and independently searched leanfinder for higher-direct-image
   germ independence and loogle for isoRightDerivedObj_inv_naturality.
   Existing results supply ingredients, not this compatibility statement.
   Its docstring gives the resolution comparison, cancellation, naturality
   and germ argument, and it has a complete matching node. Closing that
   comparison would require substantial additional formalization, not a
   short repair. Verdict: pass as a sourced decomposition, net zero holes.
4. Read the proof from its target down. The local-spectrum open equality is
   proved directly with Mathlib; restriction invertibility uses injective
   homotopy equivalence and global sections, followed by the forward lemma
   and elementary cancellation of e. Public imports are required by the
   signatures, new imports are proof-only, and no shorter ready-made route
   was found. The unit sk-thm-p1 realized fields are untouched and this
   reduction bypasses no realized unit step. Corrected No longer needed to
   name every removed old proof dependency, distinguishing relocation of
   compatibility work from module pruning. Verdict: pass.
5. Compared the normalization node's proof steps and proof_deps with the
   implemented proof, and checked the new node's statement, source, proof
   plan, dependency union, searches, provenance, blueprint and Lean record.
   They agree with the delivered declarations. Verdict: pass.

Second reading changed only this report: completed dependency-removal
accounting and added the independent review. No Lean repair was necessary.
