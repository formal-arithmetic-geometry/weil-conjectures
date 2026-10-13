## What changed

Proved `AlgebraicGeometry.exists_qc_derived_lift_of_isCompact_open` in
`Sheaf.AlgebraicGeometry.QcOpenDerivedLift` without changing its signature or visibility.
The witness is explicitly `(schemeDerivedDirectImage U.ι).obj E.obj`, equipped with
quasi-coherent cohomology by `schemeDerivedDirectImage_preserves_QCoh`.
Compactness of U and quasi-separatedness of the affine X supply quasi-compactness
of the inclusion; its quasi-separatedness is inferred for an open immersion.

The restriction isomorphism is obtained directly by deriving Mathlib's
`Scheme.Modules.restrictFunctorAdjCounitIso`, after transporting the stated over-site
restriction through `Scheme.Modules.overFunctorEquiv`. The four functor isomorphisms
are the inverse of `rightDerivedFunctorCompMapDerivedCategoryIso`,
`rightDerivedFunctorNatIso`, `rightDerivedFunctorIsoMapDerivedCategory` for the
identity, and `mapDerivedCategoryIdIso`. Their component at E.obj finishes the proof.
Replaced the proof import of `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
with `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`.
Updated the existing node's proof, proof_deps and proof_origin to this route.

Validation: the edited module compiles cleanly through lcompile.py. All existing
binders and universes are retained. The argument works for both the empty open
and the whole scheme. No new object is chosen from an unproved existence theorem.
The unit record `sk-thm-picard-duality` has no realized nodes in its statement or
step; this change is below the unit level and retains the Rj_* lifting argument.

## Proved and sorry left

Closed the sole direct hole:
`AlgebraicGeometry.exists_qc_derived_lift_of_isCompact_open`
(node `lem-sc-qc-open-derived-lift`).
No sorry remains in the item; no holes or declarations were added elsewhere.
This is a proof from existing declarations, not a decomposition into new holes.
The proof still uses the existing quasi-coherence preservation theorem and its
transitive dependencies; this report does not assert they are all axiom-free.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`.
The node `lem-pc-restrict-derived-direct-image-open` and its declaration
`AlgebraicGeometry.schemeDerivedDirectImage_openRestriction` are no longer direct
proof dependencies of this item. In particular, this route needs neither its
inverse-image-open transport nor the restriction-preserves-K-injectivity step
`lem-sc-derived-k-injective-restrict-open` / `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`.
These are route-level removals, not claims that no other target needs those modules.
Both public imports are retained because they support the unchanged statement.
The preservation-of-QCoh dependency remains required.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface fault was found. The planned general open-restriction
comparison is unnecessary for an inclusion: the proved underived open counit and
exact-postcomposition derived-functor comparison give the required isomorphism directly.
The existing docstring records the original valid plan; the proof's inline comments
and updated DAG describe its shorter implementation.

## Second reading by W4

1. Compared the entire delivered module with the repository version using `diff -u`.
   The sole declaration's signature, universes, binders, visibility and docstring are
   byte-for-byte unchanged. Only its proof and one plain proof import changed; no
   definitions, public imports, new declarations or change records were introduced.
2. Recompiled the delivered module locally through lcompile.py: clean, no warnings.
   Inspected the whole file: no sorry, axiom, unsafe, opaque, implemented_by or extern.
   A scratch copy with `#print axioms` for
   `AlgebraicGeometry.exists_qc_derived_lift_of_isCompact_open` reports exactly
   propext, Classical.choice, Quot.sound and sorryAx from existing dependencies.
   Separately checked the derived-composition isomorphism and Mathlib open counit:
   both report only the three allowed axioms. The witness is explicitly Rj_*E;
   no arbitrary data is selected from an unproved existence theorem. Verdict: pass,
   with the existing transitive sorry dependencies explicitly retained.
3. No statements were split off and no new nodes were introduced, so there are no
   new small-case obligations or duplicate split statements. Searched the local
   Sheaf and upstream AlgebraicGeometry sources for quasi-coherent lifting and
   derived extension alternatives; no matching existing lift theorem was found.
   Read Mathlib Modules/Sheaf.lean's overFunctorEquiv and
   restrictFunctorAdjCounitIso and the source right-derived/exact-postcomposition
   API. The proof applies these directly rather than restating the target.
4. Read the proof downward: compactness gives CompactSpace U; Mathlib's
   quasiCompact_of_compactSpace requires quasi-separated X, supplied by affineness;
   the inclusion is quasi-separated as an open immersion. The existing QCoh
   preservation theorem gives exactly the property of the constructed Rj_*E.
   The over-site restriction is transported to ordinary restriction, its underived
   counit is derived through exact postcomposition, and the component at E.obj
   has precisely the unchanged conclusion. This argument also applies to the empty
   and whole open and the zero object. The two public imports support the statement;
   both plain imports support the proof. The removed old proof dependency
   lem-pc-restrict-derived-direct-image-open is fully listed under No longer needed.
   Read sk-thm-picard-duality.json: its realized statement and step lists are empty;
   this node's below-unit change retains the Rj_* lifting route. Verdict: pass.
5. Compared the old and delivered node JSON. Only proof, proof_deps and proof_origin
   changed. The proof steps describe the exact constructed witness, inferred
   morphism properties and four composed isomorphisms used in Lean. proof_deps is
   exactly the remaining QCoh preservation node; generic proved API glue is named
   in the elementary restriction step. No node statement or Lean record changed.
   Verdict: pass.

Second reading changed only this report to record the independent checks; no
repair to the Lean proof or node was needed. Closed 1 existing hole, added 0 holes;
this is a proof of the item relative to existing dependencies, not a decomposition.
