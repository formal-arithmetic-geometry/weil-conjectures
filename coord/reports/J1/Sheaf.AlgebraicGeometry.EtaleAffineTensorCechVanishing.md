## What changed

Proved `AlgebraicGeometry.Scheme.isZero_etaleTensorSectionsSheaf_ulift_cech`
in `Sheaf.AlgebraicGeometry.EtaleAffineTensorCechVanishing` from a geometric complex
comparison and the existing, proved `Module.FaithfullyFlat.exact_amitsurComplex`.
The proof writes p as q+1, maps exactness through forgetting scalars and ULift,
transports exactness across the comparison isomorphism, and concludes zero homology.
The original declaration and public imports are unchanged. The DAG now follows this proof.

The new comparison uses the actual ring A = Gamma(U, O_U) and actual coefficient
module M = Gamma(U, U.hom*F). Its conclusion is a complex isomorphism and faithful
flatness; it asserts no exactness or homology vanishing. Thus the remaining statement
is the geometric part of the argument, rather than the original vanishing under a
new name. All original geometric steps and the unit route are retained in its node.

## Proved and sorry left

Decomposition: one original hole closed and one new hole added; net hole reduction zero.
The original theorem is not yet axiom-clean.

Proved (relative to the geometric comparison):
`AlgebraicGeometry.Scheme.isZero_etaleTensorSectionsSheaf_ulift_cech`
(node `new-etale-affine-tensor-cech-vanishing`). No sorry remains in the item's module.

One new sorry remains:
`AlgebraicGeometry.Scheme.exists_etaleTensorSectionsSheaf_ulift_cech_amitsur_iso`
in `Sheaf.AlgebraicGeometry.EtaleAffineTensorCechAmitsurComparison`
(node `new-etale-affine-tensor-cech-amitsur-comparison`). Its proof is exactly
`by sorry`, with source and a full proof in words in its docstring and DAG node.
The original theorem therefore still transitively depends on sorry.

Both modules compile locally. The exactness transport uses Mathlib's preservation
of homology, including the actual forgetful and ULift instances; it introduces
no further assumption. Edge cases checked mathematically: p=1 is q=0; a single
cover has the usual Amitsur comparison; the empty covering forces empty U and
zero section module; zero F gives zero complexes. X itself need not be affine.

## No longer needed

Removed these direct proof imports from the item's module:
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Paper.EtaleStandardCoverCech`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.RingTheory.FaithfullyFlat.Amitsur`
- `Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent`

They are replaced by the proof import of the new comparison. Amitsur is exposed
by that comparison because its definition occurs in the comparison's statement.
The geometric nodes remain proof dependencies of the new comparison: none is
claimed mathematically unnecessary or globally pruned. Descent and tensor pullback
are also already available through the existing tensor-section sheaf import.
No original public import was removed. No unit statement or proof step was bypassed.

All original proof dependencies moved off the item remain in the comparison:
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-pc-module-pullback-identity-composition`, `def-sc-etale-qcoherent-module`,
`lem-sc-etale-qcoherent-descent`, `lem-sc-etale-standard-cover-cech`,
`lem-weil-pbc-fibre-product-affine-spectra`, and
`lem-weil-pbc-module-pullback-affine-sections`.
`lem-pc-cech-exact` remains a direct dependency. No module is globally pruned.
Removed the unused public ConcreteCoefficients import from the new comparison.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The listed dependencies do not themselves supply
the complex comparison: the standard-cover theorem uses SiteCechComplex, a small
index type and a base literally Spec A; the target uses Mathlib cechComplexFunctor,
a larger finite index type, and an over category. The new comparison records
those changes of presentation, the affine tensor identification, and compatibility
of all face maps explicitly. Existing pullback quasi-coherence concerns abstract
pullback; tensor pullback is compared using uniqueness of its adjunction.

The local checkout omits the literature source files; the cited Stacks proofs
were read directly at https://stacks.math.columbia.edu/tag/03OZ and
https://stacks.math.columbia.edu/tag/03P2. LeanSearch returned Internal Server Error;
LeanFinder, Loogle and the actual Mathlib grep searches were performed and recorded.

## New nodes

`new-etale-affine-tensor-cech-amitsur-comparison`, in
`dag/nodes/sec-curve-estimates/new-etale-affine-tensor-cech-amitsur-comparison.json`,
states the geometric complex comparison for the actual section ring and module.
Its source is the affine identification in Stacks 03P2 after the 03OZ comparison.
It retains the original geometric proof dependencies and does not use Amitsur
exactness. Blueprint searches for Amitsur and 03P2 found no duplicate geometric
comparison (the Amitsur match is the existing algebraic exactness theorem).
No statement or definition changed, so there is no change record.

## Second reading by J1

1. PASS: diff against the repository shows the existing theorem signature and
   docstring byte-for-byte unchanged. No existing definition or statement changed;
   no change record is needed. The only new declaration is the comparison theorem.
2. PASS: both modules compile through lcompile.py in dependency order. Scratch
   copies with #print axioms show only propext, Classical.choice, Quot.sound and
   sorryAx. The comparison is the only direct sorry, exactly a named public theorem
   with whole proof `by sorry`; no hollow definition or forbidden primitive.
   The target still depends on this sorry and is not an axiom-clean completed proof.
3. PASS: the comparison separates geometric identification from algebraic exactness,
   asserts neither exactness nor vanishing, and is a proper part of the argument.
   Checked singleton identity/general singleton covers, repeated members, zero F,
   empty index over empty U, and nonaffine X with affine U. Finite disjoint unions
   give a ring in universe u after reindexing; ULift gives the required u+1 complex.
   The coefficient module and base ring are actual sections, not arbitrary substitutes.
   Read Stacks https://stacks.math.columbia.edu/tag/03OZ and the affine argument of
   https://stacks.math.columbia.edu/tag/03P2. Independent LeanFinder, Loogle, Mathlib
   grep and repository searches found no complete existing comparison. Repository
   search found nonempty_etale_siteCech_complex_iso: the plan now explicitly reuses it.
4. PASS after repair: the Lean proof applies proved Amitsur exactness, maps exactness
   through scalar forgetting and ULift, and transports it through the isomorphism.
   Degree one is included (q=0), degree zero correctly excluded. The geometric
   comparison cannot be closed in a few minutes from the existing declarations.
   No globally pruned module is claimed. Unit sk-prop-h2 has empty realized lists;
   its Kummer route is untouched. The parent affine route still uses the disjoint
   union comparison and Amitsur exactness.
5. PASS after repair: node Lean signatures match the files verbatim, and proof_deps
   is the union of step uses in both nodes. The item's plan follows its implemented
   exactness transport. The new node has source, complete proof in words, searches,
   provenance, blueprint ancestry, chapter/unit, creation and Lean records. Added
   the existing product-cone comparison to its dependencies and independent searches.

Changed: removed the unused public ConcreteCoefficients import from the new module;
added plain proof-plan imports for affine sections, standard covers, the existing
product-cone comparison and quasi-coherent pullback; made the docstring and node
reuse that comparison; clarified that this is a one-for-one decomposition.
The target proof is unchanged.
