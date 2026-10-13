## What changed

Constructed the natural transformation scalarForgetPullbackComparison as the abelian adjunct
of the forgotten scalar inverse-image unit, proved its naturality and its adjunct formula,
and proved invertibility by uniqueness of composite left adjoints. Scalar forgetting has a
right adjoint by restriction/coextension along integers and the equivalence between integer
modules and abelian groups. The coefficient adjunction restricts to sheaves and its right
adjoint commutes pointwise with pushforward.

The original theorem now inverts this explicit comparison, uses its adjunct formula, and
obtains the integer-unit equation by composing the integer-unit comparison with the inverse.
The existing signature and visibility are unchanged. Added two proof modules and their nodes.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.scalar_forget_pullback_adjunction (the item's sole hole).
Proved new: scalarForgetPullbackComparison_adjunct and scalarForgetPullbackComparison_isIso.
Proved new: scalarForgetPullbackComparison_integerUnit, including both private section
evaluation lemmas. Holes added: none. Every delivered Lean file is free of sorry.
The second reading axiom audit of the comparison definition, its adjunct formula,
invertibility, integer-unit equation, and original theorem shows exactly propext,
Classical.choice, and Quot.sound. This closes the item independently of the other
obligations in its imported modules; it does not claim that the project targets are closed.

## No longer needed

No existing import was removed. Removed the trial proof import
Mathlib.CategoryTheory.Sites.Adjunction from the new comparison module; its
adjunction restriction uses the API already available from the statement imports. The original statement needs ScalarAbelianExtFactorization
and FieldLinearModuleCohomologyOperations. Neither original dependency module is pruned. The old proof_deps nodes
new-sc-scalar-abelian-ext-factorization and
def-sc-field-linear-module-cohomology-operations remain needed for their definitions;
the original theorem now obtains the proof through the two new nodes, whose
proof_deps retain those old nodes. Thus no old dependency node is no longer needed.
The stalk and filtered-colimit proof proposed in the original node is unnecessary:
invertibility follows from uniqueness of left adjoints and a pointwise right-adjoint square.
No separate stalk comparison module or node is imported or required.
The blueprint unit and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies provide definitions but no theorem about the forgetful
inverse-image comparison or its integer-unit compatibility. The new nodes record these
strict parts explicitly. The stalk argument is replaceable by the adjunction argument above.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, and local searches
were used. No interface changes or forced adaptations.

## New nodes

new-sc-scalar-forget-pullback-comparison-isIso: defines the comparison by adjunction and proves
its adjunct formula and invertibility. Source: Stacks 0096 and categorical uniqueness of
left adjoints, implemented using Mathlib's restriction and composite adjunction API.

new-sc-scalar-forget-pullback-integer-unit: the single integer-unit compatibility equation
for the explicitly constructed comparison. Source: [Stacks 0096](https://stacks.math.columbia.edu/tag/0096) and
[01F7](https://stacks.math.columbia.edu/tag/01F7), using constant-sheaf
adjunction uniqueness and the generator formula for degree-zero sheaf cohomology.
The comparison applies to arbitrary sheaves, including zero sheaves. Both unit identities apply to the empty scheme, zero sheaves, and all field characteristics.

## Second reading by D2

1. Compared all three delivered modules with the repository: only the item's module
   exists there. Its theorem signature is byte for byte identical, including every
   universe, hypothesis, equation and visibility. Its only changes are one private
   proof import and replacement of the proof. No existing definition changes and no
   forced adaptations or change records are needed. Verdict: pass.
2. Compiled the three files in import order with lcompile.py: no errors or warnings.
   Scanned for sorry and forbidden declarations: none. A scratch copy with #print
   axioms shows only propext, Classical.choice and Quot.sound for the new comparison
   definition, adjunct formula, isIso theorem, integer-unit theorem, and original
   theorem. The private coefficient adjunction uses the proved restriction/coextension
   adjunction, and the comparison is an explicit homEquiv inverse, not an arbitrary
   existence witness. Verdict: pass.
3. No statements are left split off with sorry. Read both new nodes against their
   Lean: the first establishes invertibility of the explicit adjunct comparison; the
   second establishes its integer-unit equation before inversion. Their proofs are
   complete, distinct parts of the argument. Naturality of homEquiv proves the
   adjunct formula; coefficient-adjunction unit naturality identifies the comparison
   with leftAdjointUniq; constant-sheaf adjunction uniqueness and equality on the
   integer generator prove the unit equation. Checked zero sheaves, empty schemes,
   identity morphisms and arbitrary characteristic: no nonemptiness or division is
   used. Independent LeanFinder search for commuting coefficient and direct-image
   adjoints, Loogle search for homEquiv_leftAdjointUniq_hom_app, and rg searches in
   Sheaf, WeilConjectures and the Mathlib sites API found no exact replacement. The
   private homEquiv_unique pattern already occurs elsewhere and uses the same
   Mathlib uniqueness lemma; it creates no duplicate public result. Verdict: pass.
4. The shorter adjunction argument replaces the proposed stalk/filtered-colimit
   argument below the unit level. All public imports supply definitions in signatures;
   ChangeOfRings and the item's IntegerUnit import are proof-only imports. No original
   import or dependency module can be pruned: their explicit definitions occur in
   the signatures. Read dag/units/sk-prop-av-cube.json: its statement, step and realized
   record are unchanged, and this argument still supplies the same comparison node
   within that route. Verdict: pass.
5. Compared the existing DAG node: only proof, proof_deps and proof_origin changed.
   Its new step exactly describes inversion, adjunct compatibility and cancellation
   in the Lean proof. Checked both new nodes' Lean signatures verbatim, dependency
   unions, source, blueprint ancestry, chapter/unit and creation records. Their proof
   steps match the coefficient and constant-sheaf adjunction arguments. Verdict: pass.

Second-reading changes: clarified U_X, U_Y, L_k and L_ab and the full adjunct equation
in the new comparison node's natural-language statement; corrected the report's
axiom qualification and explicitly accounted for both retained old dependencies.
Lean code unchanged. Closed holes: scalar_forget_pullback_adjunction (1 of 1).
Added holes: none. Pruned modules: none.
