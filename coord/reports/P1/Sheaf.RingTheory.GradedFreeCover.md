## What changed

Proved `MvPolynomial.exists_graded_free_cover` by constructing the shifted grading on the finite free module from coefficient supports, proving its internal direct-sum decomposition, scalar compatibility, basis degrees, degree preservation of the generator map, and surjectivity. Added proof-only imports for `Finsupp.VectorSpace` and `Finsupp.Supported`.

## Proved and sorry left

Closed one hole: `MvPolynomial.exists_graded_free_cover` (one of one original holes). Added zero holes and split off zero statements. No sorry remains in the delivered module. The scratch axiom check reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` inherited from the compiled `exists_finite_homogeneous_generators` dependency; the explicit grading definitions and all five private helper theorems use only the three permitted axioms.

## No longer needed

None. The finite homogeneous generator theorem remains the sole DAG proof dependency.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omitted the explicit coefficient-support construction needed to make internality and shifted degrees available in Lean; this delivery supplies that construction directly.


## Second reading by P1

1. Compared the complete module and node against the repository. The field, arbitrary target universe, finite-generation assumption, internal grading and scalar-compatibility hypotheses, and all five conclusion clauses agree with the original signature and node statement. Restored an extra space before `:=` so the existing signature is byte-for-byte identical. No existing definition or visible import changed; the two added imports are proof-only.
2. Compiled the module locally without errors or warnings. A scratch copy with `#print axioms` for the cover, both private definitions and all five private helper theorems compiled cleanly. The helpers use only the permitted axioms. The cover also uses `sorryAx` through the existing compiled generator dependency, which remains open in that build. There is no local sorry, forbidden declaration, hollow definition, or data extracted into a definition from an unproved existence theorem. `flatten` is an explicit coefficient equivalence, and `shiftedGrade` is the explicit comap of a support submodule. The generator witness is used inside an existential theorem proof, not to define a library object.
3. No statements were split off. Checked the private helpers: empty rank gives the zero Finsupp module and vacuous basis clause; arbitrary negative shifts merely relabel the support fibers; zero coefficients are handled separately before selecting a monomial, so negative polynomial degrees are never fabricated. Homogeneous multiplication gives degree `n + m`, and the shift identity gives `n + j`. The support fibers partition every coefficient index, giving both independence and spanning without any nonzero assumption.
4. Read the finite homogeneous generator declaration and proof, searched `lean/Sheaf`, `lean/WeilConjectures` and upstream/Mathlib with support-decomposition and graded-free terminology, and ran LeanFinder for internal decomposition by degree fibers and Loogle for `Finsupp.supported, Disjoint`. The latter confirms the exact Mathlib disjointness lemma already used. LeanFinder's `AddMonoidAlgebra.gradeBy.isInternal` needs an additive grading map and does not directly accommodate arbitrary basis shifts; no shorter replacement was found. Both new imports supply used declarations (`basisSingleOne` and support submodules). The sole old proof dependency is actually used, so `No longer needed: None` is complete. Read `dag/units/sk-thm-picard-duality.json`: this item is below the unit, its `realized` fields are unchanged, and the generator/free-cover route remains intact.
5. Read the full node. Its three proof steps match the Lean: generator surjection, transported support-fiber internality, then scalar compatibility, signed basis degrees and graded map. `proof_deps` is exactly the used finite homogeneous generator node, and `proof_origin` names the explicit construction. No new nodes or statement-change records are needed. The blueprint source file is not present in this local read-only checkout; the source identification and unchanged mathematical statement were checked against the node and existing declaration docstring.

Second-reading changes: restored signature whitespace, wrapped the private internality signature to the 100-character convention, removed a duplicate blank line, and expanded this report with the exact hole accounting, searches, edge cases and axiom dependency. The mathematical proof was retained.
