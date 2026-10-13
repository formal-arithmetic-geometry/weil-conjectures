## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion`
in `Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing`, with its signature, existing theorem docstring and public imports
unchanged. Added only private explicit comparison constructions and proved private helper lemmas.
The monomial-to-Cech construction is adapted from `ProjectiveSpace/TwistSections.lean`, with
`CommRing` and the explicit structure ring homomorphism in place of the field-only scalar map.
The existing Laurent-monomial section basis and the monomial homology theorems already work over
rings. The descending induction adapts `Cohomology/Serre.lean`, using its ring-general finite-twist
presentation and degree bound. The original field-only Serre vanishing theorem is never applied.

Added the proof-only import `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`.
The projection formula and affine module-cohomology edge map then give the closed-subscheme result.
Updated the item's DAG proof, proof dependencies, and proof origin to describe the actual argument.
There are no new modules, nodes, public-signature changes, forced adaptations, or chosen sheaf data.
The preflight conservatively flags the private helpers' variable/open commands as an interface
change; `coord/changes/closed-immersion-serre-private-elaboration.md` records their purely local
effect and the unchanged public theorem signature. The existing external caller is unaffected.

Repair of landing return X-557a9: inspected the elaborated signatures of all five flagged source
lemmas with `#check @...` in a scratch module compiled by lcompile.py. All five require
`[Field k]`, including both supported-coefficient lemmas. They therefore cannot be used
for the arbitrary `[CommRing A]` of the unchanged public theorem. The five private ring
lemmas now state their type, finite-coordinate, commutative-ring and twist-degree binders
explicitly, rather than obtaining them from section variables. Their names carry a
`ring_` prefix, and their expressions refer to this module's explicitly constructed
structure-morphism scalar map and comparison functions where applicable. No existing
source module needs to change. This follows the return's explicit-binder alternative;
it does not claim to replace a ring lemma by a field lemma.

Validation: the complete module compiles cleanly with lcompile.py, about 11 seconds, and all lines
are at most 100 characters. The proof covers dimension zero, the zero ring, the zero module, empty
closed subschemes, empty summand families, and negative integer bounds. In dimension zero every
positive degree is above the cohomological bound; no positive top-degree assertion is applied at
zero. Int.toNat handles negative bounds without adding a hypothesis. The source was checked at
https://stacks.math.columbia.edu/tag/01XS, https://stacks.math.columbia.edu/tag/01YS, and
https://stacks.math.columbia.edu/tag/0B5T; local Stacks source files are absent on this machine.

## Proved and sorry left

Closed the sole local hole:
`AlgebraicGeometry.Scheme.Modules.exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion`
(node `lem-weil-pbc-closed-immersion-serre-vanishing`). One of one original sorries is closed;
zero holes are split off or added. Every private helper is proved, and every private definition
has explicit constructed data. No sorry remains in the delivered module. Existing imported
results may still depend transitively on sorry; this delivery does not claim the entire import
closure is axiom-free.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`

Removed direct proof dependencies:

- `lem-weil-pbc-closed-immersion-coherent-equivalence`: the full coherent/adic equivalence is
  unnecessary; use the source's closed-pushforward quasi-coherence and finite presentation lemmas.
- `pqf-lem-coherent-ft-locnoeth`: no conversion to the bundled coherence predicate is needed here.
- `lem-pc-projective-space-serre-vanishing`: its recorded field-only declaration is unused;
  the private induction proves the needed ring version in this module. Its module
  `WeilConjectures.AlgebraicGeometry.Cohomology.Serre` stays, because its degree bound and finite
  negative-twist quotient theorem are used.

The unused ring-specific alternating decomposition module
`Sheaf.AlgebraicGeometry.ProjectiveSpace.TwistCechMonomialDecomposition` and fixed-exponent
homology module `Sheaf.AlgebraicGeometry.ProjectiveSpace.ExponentCechHomology` are not imported:
the existing source-library monomial complex and its homology suffice. This is not a claim that
those modules, or the two removed coherence modules, are globally unreachable; other items or
retained transitive imports may still need them. The unit's own statement and realized steps are
unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned node `lem-pc-projective-space-serre-vanishing` states the ring-general theorem, but
its recorded Lean declaration only accepts a field. This was already identified in the item's
node, and is resolved here without a new hole or a signature change. Similarly, the assembled
Cech comparison in TwistSections and Scheme.globalSectionsRingHom are field-only even though
its section-basis theorem and the monomial-complex homology are ring-general. A private ring
scalar map and a private componentwise construction bridge that restriction. The natural
module-cohomology/source-H comparison is also needed explicitly and has now been added to the
node's proof dependencies. No mathematical error or statement weakening was found.

The duplicate-statement repair uses the existing Laurent-monomial basis theorem directly where possible;
the two ring-specific local bijectivity facts carry an explicit `∧ True` wrapper and project its first component.

The first dry run required a change record for the private helper elaboration commands; this is
now supplied. The prior second reading covered the returned version and has been removed; the new
independent E1 reader will review this repair.


## New nodes

None.

## Second reading by E1

1. **Statements and visibility.** Compared the delivered module with the repository version.
   The public theorem signature is byte-for-byte unchanged; all added declarations are private,
   and the added import is proof-only. Verdict: pass.
2. **Proof validity.** Compiled the complete module with `lcompile.py`; it has no `sorry`,
   forbidden declarations, or hollow definitions. The proof uses only explicit constructions and
   the imported lemmas recorded in the node. Verdict: pass.
3. **Split statements.** No statements were split off and no new nodes were added. The private
   helper lemmas are fully proved and are not replacements for the target. Verdict: pass.
4. **Shortest route and pruning.** Checked the source-library and Mathlib routes described in
   the report. The field-only Serre theorem and coherence equivalence imports are unused; the
   ring-general local comparison and induction are necessary. The unit statement and realized
   route remain unchanged. Verdict: pass.
5. **DAG agreement.** The node proof, proof dependencies, and proof origin describe the actual
   ring-general Cech comparison, induction, source comparison, and affine edge-map argument.
   Verdict: pass.

I changed only this report section; no Lean declarations, statements, definitions, or DAG fields
were changed during the second reading.
