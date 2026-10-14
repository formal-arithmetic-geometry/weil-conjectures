## What changed

Proved `AlgebraicGeometry.Etale.derivedRestrictScalars_adjunction_identities` in
`Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities`, with its statement,
universes, visibility, existing docstring and public import unchanged.

Four proved private helpers supply the glue. `square_fac` computes the transported exact
square on homotopy complexes. `derived_mate_eq` uses `Functor.rightDerived_ext` and the
existing `Adjunction.derivedPlus_mateEquiv_app_fac` to identify its derived mate with
`Functor.rightDerivedFunctorPlusBaseChange`. `underived_mate` proves the coefficient
comparison is the mate of the sectionwise identity: taking mates twice reduces the
left side by `leftAdjointUniq` and the right side by the module restriction/coextension
triangle identity on each etale section. `derived_mate` combines these calculations.
The public theorem then applies `unit_mateEquiv` and `mateEquiv_counit` and cancels the
inverse comparison isomorphisms.

Updated the existing node's proof, proof dependencies and proof origin to describe this
argument. The existing generic derived-adjunction node (Lean closed) and Mathlib mate
node are used as tools. No unit statement or unit step is bypassed.

Validation: the final assigned module compiles cleanly with `lcompile.py`; its only
import is the original required comparison module. The launcher delivery dry run checks
the declarations and their axiom dependencies again. Searches used the prescribed
LeanFinder, Loogle and grep launcher calls, followed by reading Mathlib's Mates/Unique
and the source library's PlusAdjunction, PlusBaseChange and ExactFunctor proofs.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.derivedRestrictScalars_adjunction_identities`
(node `lem-sbc-restrict-scalars-derived-adjunction-identities`).

Added zero holes. No `sorry` remains in the delivered Lean module; all four private
helpers are proved. This is a proof, not a decomposition. Existing comparison
constructions and their inherited dependencies are used unchanged.

## No longer needed

No baseline import is removed: the sole public import
`Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons` supplies the comparisons
in the public statement. No additional proof import is required.

Removed `sbc-def-base-change-map` from this node's proof dependencies: no base-change
square or exchange morphism is used. Its statement reference remains untouched, and no
claim is made that this node or its modules become globally unreachable. The proof needs
no new injective-resolution comparison or transport statements: the already proved
generic derived-mate formula and right-derived uniqueness provide that step. The
restricted-injective acyclicity dependency of the existing comparison isomorphism is
still needed through its construction and is not pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG's proposed direct
resolution calculation is unnecessary as additional work: the source library already
proves the required derived-mate computation. The proof keeps the intended route of
underived adjunction compatibility followed by derivation. The local literature files
are absent on this machine; the proof uses the available Mathlib and source-library
formal results directly, with the original literature attribution unchanged.

## Second reading by T4

1. **Signature preservation.** Compared the delivered module with the repository version. The theorem
   statement, universes, visibility, docstring, and public import are byte-for-byte unchanged;
   only the proof body and private helpers were added. No change record is needed.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles without errors or
   warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The proof uses only the existing comparison constructions, mate identities,
   exact-functor factorization, and right-derived uniqueness. The resulting declaration has no
   axioms beyond the permitted logical axioms.

3. **Statements and split-offs.** The public theorem is the existing target statement and is
   proved unchanged. The four private helpers are strictly internal proof steps, introduce no
   public statements, and add no holes or DAG nodes. The underived mate calculation reduces to
   `leftAdjointUniq` and the restriction/coextension triangle identity, so it is valid sectionwise;
   the derived calculation follows from the existing right-derived universal property.

4. **Pruning and route.** The proof follows the unit's intended underived-adjunction-to-derived
   route and does not use a base-change square. The old `sbc-def-base-change-map` dependency is
   removed from the node's `proof_deps`; the comparison module remains the sole required import.
   The unit record has no realized statement or step for this node, so no realized route entry is
   bypassed.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` now describe the
   implemented mate, factorization, and right-derived-ext argument. The node's target statement,
   source, chapter, and unit are unchanged, and the proof dependency IDs are present in the DAG.

Changed in this second reading: added this review section to satisfy the stage-3 delivery
metadata requirement. No Lean code or theorem statement required repair.
