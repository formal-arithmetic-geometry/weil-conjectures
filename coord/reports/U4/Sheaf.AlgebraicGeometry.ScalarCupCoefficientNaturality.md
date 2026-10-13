## What changed

Completed `Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality` without changing its public theorem signature or definitions. The earlier sandbox contained three private helper attempts; repaired Ext cup reassociation, supplied the Mathlib Grothendieck enough-injectives instance, and completed the main proof through `scalarCohomologyExtEquiv_map` and the tensor-coefficient square. All helper theorems and instances are private; instances are local. Transparency options are scoped to individual proofs.

Added proof-only imports of `Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality`, `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`, `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, and `Mathlib.Algebra.Category.ModuleCat.AB`. Updated the existing node proof and dependencies to describe the compiled argument. The cube unit has no realized nodes assigned to this local step; its route is preserved.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.scalarCup_coefficient_naturality` (node `lem-sc-scalar-cup-coefficient-naturality`). Added zero holes; no sorry remains in the delivered module. The private helpers `ext_map_naturality`, `extCup_naturality`, and `tensorCoefficient_naturality` are proved in full. This is a proof from existing library statements, not a decomposition into new obligations. Existing open obligations in imported cohomology constructions remain outside this delivery.

The module compiles with no errors or warnings. The unchanged statement covers arbitrary module coefficients, all natural degrees including zero, zero maps, and the empty scheme. The proof assumes no quasi-coherence or cover hypothesis.

## No longer needed

None. No original import or DAG proof dependency is removed. No new intermediate module or node is needed: the existing coefficient comparison handles the first step, and Mathlib Ext composition, exact-sequence and monoidal laws prove the private glue.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox was unfinished: the generic Ext naturality helper required enough injectives for scalar sheaves, the Ext cup helper lacked the final reassociation, and the main theorem was still sorry. These are now repaired. The original mathematical statement and plan are sound. The coefficient comparison previously described inline is now available as the proved `scalarCohomologyExtEquiv_map`, so it is imported and recorded explicitly in the DAG.

## Second reading by U4

1. Compared the complete module and node against the repository with `diff`.
   The signature and existing docstring of `scalarCup_coefficient_naturality`
   are byte-for-byte unchanged (also checked programmatically). No existing
   definition changes. The only added declarations are private proof helpers
   and private local instances. Every added import is proof-only. Verdict: pass.
2. Independently compiled the delivered module with `lcompile.py`: clean,
   28.8 seconds. Scanned the complete file: no sorry, axiom, unsafe, opaque,
   implemented_by or extern, and no data chosen from an unproved existence
   theorem. The injective presentation in the induction is supplied by Mathlib's
   proved EnoughInjectives instance. A scratch copy with `#print axioms` shows
   only propext, Classical.choice and Quot.sound for all three private helpers.
   The main theorem additionally has sorryAx from the existing imported open
   cohomology constructions; this delivery closes its body, not those upstream
   holes. Verdict: pass under the permitted open-dependency rule.
3. No statements were split off, no new public statement or node was added,
   and no hole was relocated. Read the helper statements and their proofs:
   degree zero is ordinary naturality; the successor case uses an injective
   presentation and the exact Ext sequence, with naturality of extClass.
   Tensor naturality reduces sectionwise to tensorHom_app_tmulSection.
   No nonzero, positive-degree, quasi-coherent or nonempty-scheme condition
   enters these arguments. Verdict: pass; one hole closed, zero added.
4. Read scalarExtCup, scalarTensorCoefficient and scalarCohomologyCup in
   FieldLinearModuleCohomologyOperations, the coefficient comparison proof,
   and the cube unit's statement, step and empty realized arrays. The final
   proof transports through the injective comparison, uses Ext cup naturality,
   then the tensor coefficient square. It bypasses no realized unit step.
   Searched both Lean roots for Ext and tensor naturality and inspected the
   nearby StructureSheafCohomologyPullbackIdentity and MayerVietoris Ext-square
   proofs: the former has only a private identity-target helper, the latter
   requires a natural isomorphism, so neither replaces this helper.
   A fresh Loogle search for
   `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp`
   found a newer Mathlib result, but `#print` confirms it is an unknown constant
   in this pinned compiled library, and rg finds no declaration in its source.
   Thus it cannot replace the present proof. The three Mathlib imports supply
   Grothendieck sheaves, the ModuleCat Grothendieck instance, and enough
   injectives; the comparison import supplies scalarCohomologyExtEquiv_map.
   The original public import supplies the signature and constructions.
   No old dependency is unused, so No longer needed is complete. Verdict: pass.
5. Read the existing node and delivered node: only proof, proof_deps and
   proof_origin change. The four steps match coefficient comparison, generic
   Ext induction/cup reassociation, the sheafification tensor square, and
   transport back to cohomology. The dependency union is exactly the original
   operations node plus the coefficient-comparison node. No new nodes require
   metadata. Read Stacks Tags 01F7, 07MB and 0FKV online because the literature
   checkout is absent here: these give cohomology functoriality and the signed
   tensor/cup comparison; this Lean proof uses the existing Ext-defined cup
   directly. Verdict: pass.

Second reading changed this report only: added the independent checks and
clarified the permitted upstream sorryAx dependency and the unavailable newer
Mathlib shortcut. No Lean or node repair was necessary.
