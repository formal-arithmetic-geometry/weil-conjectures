## What changed

Proved AlgebraicGeometry.affineKProjective_homComplex with its signature unchanged.
The proof uses the core affine derived equivalence, Mathlib Qh_map_bijective, and
an explicit new module-homology quotient bridge. A private proved helper extracts
full faithfulness, additivity and the termwise tilde comparison from the core.
Naturality follows by choosing a chain representative and comparing cycles through
the injective cycle inclusion, then applying homologyπ_naturality.

Added Sheaf.Algebra.Homology.ModuleHomComplexQuotient with the completely proved
CochainComplex.moduleHomComplex_quotient. It requires neither K-projectivity nor
an affine scheme, so it is strictly the generic quotient part of the argument.
Updated the parent node proof, proof_deps and proof_origin to match the Lean.
All existing public imports and signatures are retained. New proof imports are private.

## Proved and sorry left

Closed the single original hole AlgebraicGeometry.affineKProjective_homComplex
(node lem-sc-affine-kprojective-hom-complex). Added zero holes; split off zero
unproved statements. The new theorem CochainComplex.moduleHomComplex_quotient
(node lem-sc-module-hom-complex-quotient) is completely proved, as is the private
helper affineTilde_map_bijective. No sorry remains in either delivered module.
The affine theorem still depends on existing holes reached by
exists_affineQCohDerivedEquivalence_core; this delivery does not claim to close them.
The new quotient theorem uses only standard Mathlib axioms.

## No longer needed

No imports or modules pruned. The old direct proof dependency
`def-sc-module-total-hom-complex` is now used through
`lem-sc-module-hom-complex-quotient`, rather than directly by the affine node.
Every original import supplies statements, instances, or the affine comparison.
No original dependency branch or unit step is bypassed. The generic module quotient
is now proved and creates no further proof work. No imports were removed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG plan is implemented. The abstract module homology
and Mathlib's group-valued HomComplex need an explicit comparison through preservation
of left homology by the forgetful functor; the new proved bridge provides it.
The representative identities suffice to derive naturality, so a separate generic
naturality lemma is unnecessary. LeanSearch returned Internal Server Error; Loogle,
LeanFinder and direct source searches supplied the relevant existing tools.
The zero-source, zero-target and zero-ring cases are included by the same kernel and
quotient construction. No boundedness assumption is introduced.

## New nodes

lem-sc-module-hom-complex-quotient: a completely proved generic comparison between
homotopy-category morphisms and degree-zero module Hom homology, normalized on chain
maps. Source: Stacks 0A8H and Mathlib HomComplexCohomology. Its only project proof
dependency is the already proved module Hom complex construction. No change records
are needed: there are no definition, statement, or existing visibility changes.

## Second reading by T2

1. Compared the delivered affine module with the repository version. The existing theorem
   signature is byte-for-byte unchanged; the only changes are proof text and proof-only
   imports. The added quotient module is a new declaration with its own node.

2. Compiled both modules together with `lcompile.py --all`; compilation succeeds with no
   errors or warnings. The files contain no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, or hollow definition. The delivery probe checks the
   declaration axioms. The quotient theorem uses only standard axioms; the affine
   theorem also reaches `sorryAx` through the existing open affine-core dependencies.

3. Checked the new quotient statement against the module proof and its Mathlib sources.
   It is a generic, true comparison for arbitrary module complexes and chain maps, with
   no projectivity or boundedness hypotheses. It is strictly smaller than the affine
   target and is not an existing library declaration.

4. Read the proof top-down. It first uses the existing affine equivalence core and
   Mathlib K-projective localization, then the proved generic quotient bridge, and finally
   proves naturality by injectivity of the cycle inclusion and homology-map naturality.
   The route keeps the affine unit path. No import can be removed: the public imports
   occur in the theorem interfaces, while the added imports are proof-only.

5. Checked both DAG nodes. The affine node records the changed proof steps and exact
   dependencies, and the quotient node records its statement, source, searches, and
   complete proof. No target statement or definition changed.

I changed only the report during second reading: added this review and clarified the
old dependency now reached through the quotient lemma under No longer needed. No Lean source or DAG repair
was necessary.
