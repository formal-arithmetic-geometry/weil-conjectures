## What changed

Proved AlgebraicGeometry.Etale.subsingleton_H_underlying_of_injective_module in
Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology, with its signature unchanged.
Added proof-only imports of InjectiveModuleCechAcyclic, EtaleCechVanishingCriterion,
EtaleSiteCechComplexComparison, EtaleSheafHExtDerivedComparison and the source
RightDerivedFunctor.PlusCompatibility. The proof explicitly combines constant-ring
encoding, generic injective Cech acyclicity, Cech comparison, derived evaluation
vanishing, terminal evaluation/global sections, and Ext/derived cohomology comparison.
Updated the item's node proof, proof_deps and proof_origin to match the Lean argument.
The unit's realized statement and steps are unchanged.

The generic ringed-site Cech acyclicity node
lem-weil-pbc-ringed-site-injective-module-cech-acyclic (unit sk-prop-cd) is used as a
tool: it handles arbitrary ring sheaves and the required value universe. The older
etale-specialized nodes in this unit restrict coefficients to lifted smaller rings;
using the generic tool avoids changing any statement or creating a duplicate lemma.

## Proved and sorry left

Proved AlgebraicGeometry.Etale.subsingleton_H_underlying_of_injective_module
(lem-weil-pbc-injective-module-sheaf-H-acyclic), 1 of 1 original sorries.
No sorry remains in the delivered module; no new declarations or sorries were added.
The imported equivalence, generic Cech acyclicity, Cech comparison and Cech criterion
remain existing proof obligations in their own modules. Local lcompile succeeds.

## No longer needed

No original import was removed. No new unused import remains.
The direct dependencies def-weil-pbc-abelian-etale-sheaves,
def-weil-pbc-cech-complex, def-weil-pbc-etale-cohomology,
def-weil-pbc-etale-sheaves, def-weil-pbc-etale-site,
def-weil-presheaf-modules-sheafification,
lem-weil-pbc-free-cech-complex-exact and
lem-weil-pbc-injective-module-injective-presheaf are removed from this node's
proof_deps: their needed mathematical content is supplied through the retained
generic Cech lemma and comparison interfaces. They are not asserted to be globally
unreachable, since retained dependencies may still use them.
No separate specialized free-Cech or injective-presheaf module is imported here.

## Where the brief, the DAG or earlier work was wrong

The original plan's mathematical route is valid; the generic ringed-site Cech lemma
provides its first two Cech steps directly. The existing
Scheme.isZero_rightDerived_etale_toSheaf_of_injective only accepts R : Type u
and modules over its ULift constant ring sheaf, so it cannot handle arbitrary
Lambda : Type (u+1) in this target. Likewise the candidate generic
CategoryTheory.injective_module_abelian_acyclic uses Sheaf.H', whose abelian-value
universe is tied to the site's morphism universe, so it does not typecheck for the
present larger-universe abelian sheaves. The delivered proof instead uses the
universe-correct derived-evaluation criterion and retains the original target.
Searches via leanfinder, loogle and grep found no direct Mathlib theorem.

## Second reading by G1

1. Compared the delivered Lean module with the repository version. The theorem signature is byte-for-byte unchanged; only proof imports and the proof body changed.
2. Compiled the module with lcompile successfully. There are no `sorry` declarations in the delivered module and no forbidden declarations. A scratch `#print axioms` reports only the permitted axioms plus `sorryAx` from imported open obligations.
3. Checked the proof route and dependency declarations against the node. The proof uses the constant-ring equivalence, generic injective Cech acyclicity, etale Cech comparison, Cech vanishing criterion, derived-functor single identification, and sheaf-H/Ext-derived comparison exactly as recorded. No new statement was introduced.
4. Checked pruning and imports. All added imports are proof-only and are used by the proof; the report records the direct dependencies no longer needed. The route retains the unit's realized statement and steps.
5. Checked the DAG node and unit metadata. The node statement and theorem declaration agree, proof/proof_deps/proof_origin match the Lean proof, and the unit realized fields are unchanged. Verdict: pass.

No further changes were required in the second reading.
