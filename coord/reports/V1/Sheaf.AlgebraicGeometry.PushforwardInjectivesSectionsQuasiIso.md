## What changed

Proved AlgebraicGeometry.Scheme.Modules.quasiIso_globalSections_pushforward_injectives with its exact existing signature. Installed enough injectives, translated the zero-term bounds, used the acyclicity conjunct of module_pushforward_injective_acyclic, and applied Functor.quasiIso_map_of_rightAcyclic. The abelian-group conjunct follows from the exact forgetful functor and Mathlib's quasiIso_map_iff_of_preservesHomology. Added the proof-only import Mathlib.Algebra.Homology.ShortComplex.ModuleCat. Updated the node proof to describe the Lean argument. The unit route is unchanged: this node is below the unit's realized statements and steps.

Validation: the module compiles without warnings using lcompile.py. LeanFinder found only exact-functor preservation results, while the existing source library has the precisely applicable Leray acyclicity theorem. Loogle confirmed the forgetful-functor comparison lemma. No signatures, definitions, or public imports changed.

## Proved and sorry left

Closed the sole original hole: AlgebraicGeometry.Scheme.Modules.quasiIso_globalSections_pushforward_injectives (lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso). No sorry remains in the delivered module. No holes added or split off. This is a proof from existing named dependencies, whose transitive remaining holes are unchanged.

## No longer needed

Removed proof imports Sheaf.AlgebraicGeometry.TensorPullback and Sheaf.Paper.PQFCohomology. Their directly associated proof-dependency nodes def-pc-module-pullback and pqf-def-cohomology are unnecessary for this proof: Mathlib already defines the pushforward appearing in the statement, and the pushforward acyclicity theorem directly gives rightAcyclic. Removed def-weil-abstract-derived-category from proof_deps: the proof works entirely with complexes and QuasiIso and never constructs a derived category. Its associated module Mathlib.Algebra.Homology.DerivedCategory.Basic need not be directly imported here. These dependencies may remain needed by other declarations or transitively by retained imports; no claim is made that they disappear from the whole target closure. All other stated proof dependencies remain.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The plan's cohomology-to-rightAcyclic comparison is already supplied by the second conjunct of module_pushforward_injective_acyclic, so PQFCohomology is unnecessary as a direct dependency. SheafOfModules.evaluation does not directly infer Additive in this environment; writing its definition as forget composed with presheaf evaluation permits inference without altering the statement. Its equality with evaluation, and the equality of iterated mapping with mapping the composite functor, are definitional.

## Second reading by V1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only the permitted existing axioms through its dependencies. Verdict: pass.
3. Checked the proof against the existing library and DAG. No new theorem statements or split-off holes were added, and the argument uses the existing right-acyclicity and quasi-isomorphism lemmas. Verdict: pass.
4. Reviewed the route from the target downward. The proof applies `Functor.quasiIso_map_of_rightAcyclic`, derives source acyclicity from `module_pushforward_injective_acyclic`, derives target acyclicity from injectivity, and transfers the result through the exact forgetful functor. Removed proof-only imports are recorded above; the unit route remains unchanged. Verdict: pass.
5. Checked the node metadata against the Lean proof. The theorem, proof dependencies, and proof origin agree; no new nodes require review. Verdict: pass.

Changed only the proof and proof-only imports, and updated the node proof metadata as described above. No mathematical or interface changes were needed.
