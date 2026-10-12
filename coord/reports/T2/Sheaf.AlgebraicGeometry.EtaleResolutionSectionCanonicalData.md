## What changed

Proof of `AlgebraicGeometry.Etale.exists_resolutionSection_canonical_comparison`
in the assigned module. Added two proved private helpers: degree-zero injectivity of
`extMk` and a general normalized homology comparison for an additive represented
functor. The latter descends `extMk` from cycles to the cokernel of boundaries,
proves bijectivity, and transports from the explicitly indexed short complex to the
complex homology. Applied this to the global and open section representations;
composed the open result with the independently defined bijective cohomology map.
Added proof-only imports of `Mathlib.Algebra.Homology.ShortComplex.Ab` and
`Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMapBijective`. Updated the node's
proof text to follow that argument. No signatures or definitions changed.

Earlier attempts were blocked by an unpublished comparison dependency. That dependency is now available, and the delivered module compiles cleanly with lcompile.py.

## Proved and sorry left

Proved: `AlgebraicGeometry.Etale.exists_resolutionSection_canonical_comparison`
(node `lem-weil-pbc-etale-resolution-section-canonical-data`). The delivered module
compiles cleanly. No sorry remains and no new holes or intermediate theorem modules
were added. The theorem uses only propext, Classical.choice, and Quot.sound.

## No longer needed

No imports were removed. Every old proof dependency remains used:
`def-sp-injective-resolutions`, `def-weil-pbc-etale-open-comparison-data`, and
`lem-weil-pbc-etale-open-object-cohomology-map-bijective`. No nodes or modules
were pruned.

## Where the brief, the DAG or earlier work was wrong

Earlier attempts could not compile because the required comparison .olean had not
yet been published. That blockage is resolved.

## Second reading by T2

1. Interface: compared the sole delivered module with the repository version.
   The existing theorem signature is byte for byte unchanged; there are no existing
   definitions in this module. Added universes serve only the private helper;
   imports added for proofs are non-public. The retained change record documents
   these elaboration additions; no downstream interface or target is changed.
2. Proof: compiled locally through lcompile.py with no errors or warnings.
   An independent scratch copy with #print axioms of
   `AlgebraicGeometry.Etale.exists_resolutionSection_canonical_comparison`
   lists only propext, Classical.choice, and Quot.sound. Read both private helper
   proofs and the assembly of all four structure fields. No sorry or prohibited
   declaration is present. The chosen equivalences come from a fully proved
   existence statement with a prescribed value on every homology class, not an
   arbitrary witness from an unproved existence theorem.
3. Split statements: none. One existing named hole is closed, zero holes added:
   `AlgebraicGeometry.Etale.exists_resolutionSection_canonical_comparison`.
   Checked degree zero (incoming differential vanishes), positive degree
   (extMk kernel is boundaries), and the zero section group. The empty-open case
   uses the same represented evaluation and the existing localization theorem.
4. Route and pruning: read the existing comparison structure, the open-object
   bijectivity proof, and the unit sk-thm-p1 with its realized fields. This is a
   resolution-computation tool below the unit steps; no realized step is bypassed.
   Independently searched Mathlib via msearch grep for extMk injectivity and
   homology comparisons, and searched lean/Sheaf for section-resolution
   equivalences. Existing unnormalized comparison results do not supply the
   prescribed cocycle values. Retained the direct quotient argument. The one
   public import supplies the signature; both private imports supply used APIs.
   No old proof dependency is unused and no module is pruned.
5. DAG: compared the node with the repository; only proof and proof_origin
   change. The proof describes exactly the cycle map, its kernel, cokernel descent,
   bijectivity, global adjunction and open localization composite in Lean.
   proof_deps is unchanged and agrees with those uses. No new nodes exist.

Changes by this reading: corrected the theorem's proof docstring to describe the
actual descent of extMk through the homology cokernel, removed extra blank lines,
made the no-pruning report explicit, and removed an obsolete second-reading
paragraph that incorrectly called private universe additions interface-sensitive.
The proof terms and theorem signature were retained.

Change record: `coord/changes/etale-resolution-section-canonical-data.md`.
