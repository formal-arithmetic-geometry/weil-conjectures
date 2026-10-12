## What changed

Proved `CategoryTheory.Functor.kInjective_computes` in
`Sheaf.CategoryTheory.KInjectiveComputes`, with its signature unchanged.
Added the proof-only import
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` for
`HomologicalComplex.mapExtendIso`. Added three proved private helpers for
unique lifting, comparison of resolutions, and the mapped comparison isomorphism.
Updated the existing node's proof steps to describe the actual Lean assembly.

The proof constructs the functor for arbitrary prescribed resolution choices,
including its identity and composition laws. It compares object-level cohomology
with an ordinary injective resolution and constructs the shift isomorphism.
No definitions or statements used by other modules changed.

## Proved and sorry left

Proved the module's single original sorry:
`CategoryTheory.Functor.kInjective_computes`
(node `lem-sp-kinjective-computes`). All six conjuncts are proved.
No sorry remains in this module; no new sorry or node was introduced.
The proof uses the existing theorem
`CochainComplex.IsKInjective.precomp_bijective_of_quasiIso`
(node `lem-sp-kinjective-comparison-principle`), whose proof remains sorry
in its existing dependency module; that module was not changed.

Validation: the prescribed local compile completes without errors or warnings.
The server compile, axiom probe, and preflight are checked by the prescribed dry run.

## No longer needed

None. No existing import or proof dependency was removed. The comparison,
bounded-below injectivity, ordinary injective resolution, additive homotopy,
enough-injectives, and shift ingredients of the planned route are all used.
The unit record has no realized statement or step at this node, and its route
was not changed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. Two API bridges needed explicit Lean code:
`CochainComplex.Plus.ι.commShiftIso` identifies the underlying shifted complex,
and `HomologicalComplex.mapExtendIso` commutes extension with termwise F.
The ordinary cohomology comparison also uses `extendHomologyIso` and
`InjectiveResolution.isoRightDerivedObj`, rather than treating that comparison
as definitional equality. These details are now recorded in the proof steps.
The blueprint source file named by the node is not present in this local clone;
the node's complete proof text and the locally available Mathlib/source-library
implementations supplied the argument.

## Second reading by N1

1. Compared the delivered module with the repository version. The theorem
   signature and all existing declaration signatures are unchanged; only the
   proof, its proof-only import, and the node's proof metadata differ.
2. Compiled the module with the prescribed lcompile command. It succeeds with
   no errors or warnings; the module contains no `sorry`, axiom, unsafe, opaque,
   extern, or implemented_by declaration. The proof uses only the permitted
   imported results (the comparison principle remains an existing open
   dependency).
3. No statement was split off and no new node was introduced. The existing
   theorem is the exact target statement, and its six conjuncts are discharged
   directly. Small edge cases are covered by the identity resolution and
   identity/shift morphism constructions in the proof.
4. The shortest available route was used: Mathlib homotopy-category,
   injective-resolution, shift, and homology APIs are applied directly, with
   three private helpers only for repeated comparison constructions. The added
   `ExtendMap` import is proof-only and required by `mapExtendIso`; no old proof
   dependency or import became unnecessary, and the unit route is unchanged.
5. The node proof steps, dependencies, and origin were checked against the
   Lean proof. The updated steps describe the explicit comparison, injective
   resolution, and shift constructions, and retain every dependency actually
   used.

Changed only the proof implementation, the proof-only import, corresponding
node proof metadata, and this second-reading record.
