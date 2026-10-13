## What changed

Replaced the sorry in Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality
with a complete Lean reduction through scalar Ext. Existing signatures and public
imports are unchanged. Added proof-only imports of ScalarAbelianPullbackSquare,
ScalarCohomologyExtCoefficientNaturality and Cohomology.MayerVietorisExtFunctorSquare.

Two new modules isolate strict parts of the original argument:
ScalarAbelianExtFactorization identifies the explicit comparison on one scheme;
ScalarAbelianPullbackSquare states a natural isomorphism and its degree-zero unit
and sheaf-morphism coefficient equations. These are combined by the existing
proved mapExactFunctor_square, coefficient naturality, cancellation of an additive
Ext equivalence, and associativity of Yoneda composition. No positive-degree
pullback equality is assumed in the new square statement.

Constructed the forgetful functor, its exactness instances, the integer-unit class,
and the scalar-to-abelian Ext map without holes. Exactness of forgetting uses the
restriction/coextension adjunction and the equivalence of integer modules with
abelian groups. Also proved a definitional helper for structure-sheaf pullback.
Each new module contains one public intermediate theorem left sorry. Added their
DAG records and updated the assigned node's proof route. Read Stacks Tags 03FD,
01F7 and 0096, and searched the pinned Mathlib and library before splitting.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.Scheme.scalar_unit_cohomology_pullback_naturality
(new-sc-scalar-unit-pullback-naturality).

Added two holes, each in its own new module:
- AlgebraicGeometry.Scheme.scalar_unit_abelian_ext_factorization
  (new-sc-scalar-abelian-ext-factorization).
- AlgebraicGeometry.Scheme.scalar_abelian_pullback_square
  (new-sc-scalar-abelian-pullback-square).

This is a decomposition: one upper hole closed, two strictly smaller holes added;
it is not a complete axiom-free proof of the mathematical result. The imported
scalarCohomologyExtEquiv_map is now proved in the library; this delivery does not change it. All definitions and exactness instances introduced
here are proved or constructed, with no sorry. The assigned theorem compiles with
no sorry in its body and no signature change. It needs a declaration-local
800000 heartbeat limit for comparing independent Ext instances; the proof-local
option of the earlier attempt did not cover declaration elaboration. Compilation
completed within the 60-second limit (46.9 seconds in the first successful check).

## No longer needed

Removed no original public imports: both are required by the unchanged statement.
The parent node no longer lists these old direct proof dependencies:
new-sc-scalar-unit-comparison-family,
lem-sc-injective-module-abelian-acyclic-zariski, and
lem-weil-pbc-module-pullback-structure-sheaf. The first and third still supply
definitions used in the unchanged statement and remain imported; their results
are used inside the new intermediate route rather than as direct proof steps. Its module
Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic is not imported by this
proof, but remains transitively imported by ScalarUnitCohomologyComparisonFamily;
no claim is made that it has left the targets' import closure.

No resolution-lifting, common-resolution comparison or injective-acyclicity lemma
is needed by the Lean assembly. The corresponding common-resolution route in the
parent plan is replaced by exact-functor Ext calculus. The single-scheme
factorization also does not need scalar_unit_abelian_comparison_bijective.

## Where the brief, the DAG or earlier work was wrong

The earlier missing-artifact blocker cleared after a two-minute refresh interval:
ScalarUnitCohomologyComparisonFamily.olean became available and the original
module compiled. No missing dependency was rebuilt or duplicated.

The existing plan's dependencies define the comparison and operations but do not
state the needed single-scheme factorization or coherent underlying abelian
pullback square. These gaps are isolated in the two new modules. The online Loogle
index returns newer Ext composition lemmas absent from pinned Mathlib; this
proof instead uses the proved library mapExactFunctor_square, which supports
independent Ext universes. Scalar-sheaf Ext uses u+1; abelian cohomology uses u.

The blueprint ancestor helper cannot follow created.item through the existing
module-valued creation record. The new nodes record the theorem-of-cube ancestor
explicitly from the parent's earlier scalar-unit comparison ancestor record.
The unit record sk-prop-av-cube has empty realized lists; no unit statement or
step is bypassed or changed. Edge cases of empty schemes and zero classes are
covered by the additive construction and the adjunction identities, and the new
square is an equation of sheaf maps even before higher cohomology is considered.

## New nodes

new-sc-scalar-abelian-ext-factorization: the explicit module comparison factors
through the constructed forgotten scalar Ext map on one scheme. This has no
scheme morphism or pullback in its statement. Module:
Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization.

new-sc-scalar-abelian-pullback-square: a natural isomorphism of exact functors,
its integer-unit equation in degree zero, and its structure coefficient equation
as sheaf morphisms. It has no positive-degree class, resolution, or module Ext
comparison in its statement. Module:
Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare.

Both nodes include complete proofs in words, sources, three kinds of search,
verbatim Lean statements and creation records. There are no interface changes
or forced adaptations, and no change records.

## Second reading by X3

1. Compared all delivered modules with the repository. Only the assigned module
existed there; its theorem signature is byte for byte unchanged. Its two public
imports are unchanged. The other two modules and their declarations are new.
No target, existing definition, or other module is modified; no change record is
needed. The updated docstring describes the new reduction.

2. Compiled all three modules in import order with lcompile.py: 22.6, 34.6,
and 47.8 seconds, respectively, with no errors or warnings. Inspected every
new definition and instance: all data are explicitly constructed, and no data
are chosen from either new open theorem. The only textual holes are the two
public named intermediate theorems listed above. No forbidden declaration or
kernel-check bypass occurs. The delivery probe checks every new constant;
the separate scratch axiom check showed only propext, Classical.choice,
Quot.sound and sorryAx for the three theorem statements, and only the three
permitted axioms for scalarAbelianForget, scalarAbelianUnitClass,
scalarAbelianExtComparison and scalarAbelianStructurePullback_apply.

3. Read both split statements and their proofs in words against the definitions
of scalarCohomologyExtEquiv, scalarUnitAbelianComparison, scalarInverseUnitIso,
scalarPullbackCoefficient, and tensorPullbackObjUnitToUnit. Both are true strict
parts of the argument: single-scheme factorization, and a functor square with
only degree-zero and sheaf-morphism equations. Neither restates positive-degree
pullback naturality. Zero classes and the empty scheme satisfy the formulas;
for the identity scheme map the square is the canonical identity comparison.
The tensor coefficient equation follows from the second conjunct of
tensorPullbackObjUnitToUnit_isIso and the specified scalar adjunct, rather than
from isomorphism alone. The underlying inverse-image comparison is canonical:
forgetting scalar modules commutes with filtered colimits, so its stalk maps
are identities. Reviewed Stacks Tags 03FD, 01F7 and 0096. Fresh leanfinder
search for forgetting module structure and inverse image, Loogle search for Ext
transport, and grep for constant-sheaf adjunction/composite pullback found only
generic ingredients, not either split statement. Also inspected the existing
exactFunctorCompositionComparison: its common Ext universe does not replace
the independent-universe square used here. Neither remaining hole has a short
proof from the currently available specialized declarations.

4. Followed the assembly from the top: factorization, coefficient naturality,
cancellation of the AddEquiv, the already proved exact-functor square, and
Yoneda associativity. The proof-only imports supply the three used results;
public imports supply unchanged signatures or new exposed definitions.
No imported theorem is introduced merely to rename the original hole.
Checked sk-prop-av-cube.json: its realized lists are empty and unchanged;
this is a reduction below the unit level. Completed No longer needed to name
all three removed old direct proof dependencies. No module leaves the import
closure, and this remains a one-to-two decomposition, not net proof progress.

5. Compared the three node statements and Lean records with their declarations.
The new nodes have source, full proof steps, search records, creation records,
blueprint ancestry, chapter and unit. The parent proof and proof_deps match the
two-stage Lean assembly; the new proof plans describe the remaining lower
obligations. Existing statement and statement-dependency fields are unchanged
as JSON values. No node or unit route is silently weakened.

Second-reading changes: completed the pruning report and added this review;
no Lean proof or statement needed repair.
