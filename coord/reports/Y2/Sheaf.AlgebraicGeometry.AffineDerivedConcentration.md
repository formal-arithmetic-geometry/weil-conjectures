## What changed

Proved `AlgebraicGeometry.affine_derived_concentration` with its signature unchanged.
Both implications transfer the standard degree-zero bounds through the existing affine
t-exactness theorem, then use Mathlib's single-functor representation theorem. Two private,
fully proved helpers transport quasi-coherence from degree-zero cohomology to the
representing module. The final clause composes the existing affine cohomology comparison
with the homology of the given single-functor representation.

Added the proof import `Sheaf.AlgebraicGeometry.AffineDerivedCohomology`.
The Mathlib representation and homology isomorphism are already available through
the retained imports. Updated the existing node's
proof, proof dependencies, and proof origin to this argument. No definitions or public
signatures changed. The Picard-duality unit route is preserved.

Searches: LeanFinder for degree-zero single-functor representation found both the
representation theorem and `singleFunctorCompHomologyFunctorIso`; Loogle confirmed the
representation theorem's signature; grep confirmed both in the pinned Mathlib sources.
Local compilation passes with no warnings.

## Proved and sorry left

Proved `AlgebraicGeometry.affine_derived_concentration` (1 of 1 direct sorries).
No sorry remains in this module and no new theorem with sorry is added. The theorem uses
`AlgebraicGeometry.schemeDerivedDirectImage_tExact_and_conservative_of_affine` and
`AlgebraicGeometry.schemeHigherDirectImage_of_affine`, which remain existing proof
obligations in their own modules. This delivery proves the requested theorem from those
stated dependencies; it does not close their transitive sorries.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`.
Its node `lem-pc-affine-morphism-hi` is no longer a direct proof dependency of this item;
it remains needed through affine cohomology and t-exactness. The direct definition edge
`def-pc-derived-direct-image` is removed from proof_deps; its definitions remain needed
in stmt_deps and the public `SchemeDerivedDirectImage` import. Removed the first worker's redundant proof imports
`Mathlib.Algebra.Homology.DerivedCategory.TStructure` and
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`: the retained imports already
provide their declarations. No globally unreached
module is asserted. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The forward implication can use the same t-structure bounds
argument as the reverse implication. The degree-zero identification is already covered
by `lem-sc-affine-derived-cohomology`, so ordinary higher-direct-image vanishing need
not be applied directly in this module.


## Second reading by Y2

1. Compared the delivered module against the repository with diff and compared the
   text from `theorem affine_derived_concentration` to `:= by` byte for byte: identical.
   The scheme universes, both derived-category instances, affine hypothesis, hE,
   both quasi-coherent representation existentials and the universal degree-zero
   comparison clause are preserved. Public imports and the existing docstring are
   unchanged. No definition, target, public signature or change record is added.
   Verdict: pass.
2. The original module compiled cleanly. A scratch copy with the two redundant
   imports removed also compiled, with explicit `#print axioms` for all three
   declarations. Both private helpers use only propext, Classical.choice and
   Quot.sound. The main theorem additionally uses sorryAx from the existing
   affine t-exactness and affine cohomology obligations, as the report declares.
   There is no sorry or forbidden axiom/unsafe/opaque/implemented_by/extern
   construct in the delivered module and no new definition. The isomorphism
   H^0(E) -> F transports quasi-coherence in the correct direction; the last
   clause composes H^0(Rf_*E) -> f_*H^0(E) -> f_*F. Verdict: pass.
3. No statement is split off and no new open theorem or node is introduced.
   The private helpers are fully proved: they specialize Mathlib's heart
   representation and transport the existing quasi-coherent object property.
   Independently searched LeanFinder for an object of the heart being its
   zeroth homology in degree zero, and searched the pinned Mathlib and both
   library roots for representation and quasi-coherence transport. The search
   confirms the existing representation theorem is used, rather than duplicated.
   Identity affine maps, zero objects and empty schemes require no additional
   hypothesis; the representation lemma applies in the same arbitrary abelian
   category, and isomorphism transport handles these cases. Verdict: pass.
4. Read both imported affine theorems. The forward and reverse implications
   use respectively mp and mpr of the two bounds equivalences at zero; hpush
   supplies quasi-coherence on Y and hE supplies it on X. No separate
   conservativity argument is needed. The comparison clause uses precisely
   schemeHigherDirectImage_of_affine at zero. The node's old proof_deps minus
   the new ones is exactly lem-pc-affine-morphism-hi and
   def-pc-derived-direct-image; both are accounted for under No longer needed.
   Read dag/units/sk-thm-picard-duality.json: its realized statement and step
   lists are empty, and no realized unit node or unit route is bypassed.
   Verdict: pass after removing the two redundant Mathlib proof imports.
5. Parsed and compared the old and delivered JSON: only proof, proof_deps and
   proof_origin differ. Steps 1 and 2 cite the t-exactness node, and step 3 cites
   the cohomology node; proof_deps is exactly their union. The Lean record,
   statement, stmt_deps, source, chapter and unit are unchanged. The Mathlib
   facts described in the new proof are the ones actually applied in Lean.
   There are no new-node field obligations. Verdict: pass.

Changed only the two redundant proof imports and updated this report to reflect
that pruning and the independent checks; the proof and node argument were right
and were retained.
