## What changed

Proved all five previously holed theorems in
`Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift`, with every existing signature,
definition and public import unchanged. Two fully proved private helpers establish
identity and composition for the induced closed-lift algebra maps by colimit
hom-extensionality and the existing `Algebra.ClosedLift.ι_map` theorem. The site
functor laws then follow by applying contravariant `Spec`.

Updated the existing node `def-exc-closed-site-lift` in its proof, proof_deps and
proof_origin fields to describe the implemented argument. No new modules, nodes,
statements, definitions or axioms. All edits are in the sandbox; no scratch Lean
files were needed.

## Proved and sorry left

Closed five holes, all in namespace `AlgebraicGeometry.Scheme.AffineProEt`:

- `closedSiteCoordinates_commutes`: apply global sections to the over-category
  commuting triangle and evaluate after the structural map from A.
- `closedSiteLift_mem`: the existing `Algebra.ClosedLift.indEtale` instance,
  `RingHom.IndEtale.algebraMap_iff`, and `proAffineEtale_Spec_iff`.
- `closedSiteLiftMap_over`: `AlgHom.commutes` and `Spec.map_comp`.
- `closedSiteLiftMap_id`: colimit structure maps determine the algebra map;
  the coordinate identity and `Spec.map_id` give the site identity.
- `closedSiteLiftMap_comp`: compare on colimit structure maps; the coordinate
  and spectrum contravariance give the site composition law.

No sorry remains in the delivered module, and no holes were added or split off.
The result uses the existing imported obligations
`Algebra.ClosedLift.isFiltered_index` (node `lem-exc-closed-lift-filtered`) and
`Algebra.ClosedLift.ι_map` (node `def-exc-ind-etale-closed-lift`); their existing
proofs were not changed. This is a proof from the existing dependency interfaces,
not a claim that the transitive library closure is sorry-free.

The complete module compiles cleanly with lcompile.py. The argument assumes no
nonzero ring, proper ideal, connectedness or nonempty spectrum, so the zero-ring
and unit-ideal cases stay included. No interface adaptations are necessary.

## No longer needed

Removed the proof-only import `Sheaf.RingTheory.IndEtaleStability`. In particular,
this proof does not invoke `RingHom.indEtale_principalZariski_stability` or its
node `lem-weil-pbc-ind-etale-stability`: the closed-lift instance already supplies
the precise filtered etale presentation required for basis membership, and the
source library already supplies proAffineEtale pullback stability. The node's
unchanged statement still names the general stability fact conceptually; it is
not a direct proof dependency of the implementation. No claim of global
unreachability of that module is made. All other original imports are needed.
No unit statement or step is bypassed; there are no further pruned nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The module docstring's plan for basis
membership invokes general filtered-colimit stability, but the existing
`Algebra.ClosedLift.indEtale` instance already performs that construction directly.
The item node previously had an empty proof list because it records a definition;
its well-definedness and functor-law proofs are now recorded explicitly.
The three required searches (LeanFinder, Loogle, grep), supplemented by repository
and Mathlib searches, found colimit hom-extensionality and the existing closed-lift
instance rather than a duplicate site-lift functor.

## Second reading by C4

1. **Interfaces — pass.** Read the whole delivered module and its diff against
   the repository version. All eleven existing public declarations retain their
   signatures, universes, visibility and definition bodies; the five changes to
   theorem bodies replace their original holes. The only added declarations are
   the two fully proved private helpers. Both public imports are unchanged and
   needed by definitions or signatures. No change record or forced adaptation is
   required.

2. **Proofs and axioms — pass.** Recompiled the delivered file with lcompile.py,
   cleanly in 2.4 seconds. Compiled a scratch copy with `#print axioms` for all
   eleven public declarations and both private helpers. Every list contains only
   `propext`, `Classical.choice`, `Quot.sound`, and, for the lift construction,
   `sorryAx` from existing imported obligations. In particular the coordinate
   commutation theorem and coordinate map have no `sorryAx`. There is no local
   `sorry`, forbidden declaration, or data chosen from an unproved existence
   theorem. The closed-lift object is the existing categorical colimit and its
   map is the uniquely determined colimit descent. The upstream
   `postcomp_compatible` proof is also part of that existing map construction;
   it was neither changed nor added by this delivery.

3. **Split statements — pass (none).** No holes were split off or added. Checked
   the private helpers against the explicit `ClosedLift.postcomp`, `diagram`
   and `map` definitions: their identity/composition claims hold for arbitrary
   commutative A-algebras, with no quotient, ind-etaleness, nonzero-ring or proper
   ideal assumptions. For composition, `ι_map` for the composite is compared to
   `ι_map` for each factor; the double-postcomposition index object is
   definitionally the same. This argument also includes zero rings and I = top.

4. **Route and pruning — pass.** The coordinate proof applies global sections
   to exactly the over-category triangle, with the correct contravariance. Basis
   membership uses `ClosedLift.indEtale` and `proAffineEtale_Spec_iff`; the
   over-map proof uses `AlgHom.commutes`, and Spec reverses composition back to
   the required site direction. Independent LeanFinder and Loogle searches for
   colimit uniqueness/descent, plus grep of Mathlib and the project, confirmed
   the existing colimit-extensionality route. The compound still-holed theorem
   in `ClosedLiftAdjunction` contains restricted functor laws, but using it would
   add a stronger open dependency and extra algebra hypotheses. Retained the
   current short proofs. The removed proof-only `IndEtaleStability` import is
   unnecessary: inspected the source `proAffineEtale` base-change instance and
   the explicit filtered etale presentation. The old node's `proof_deps` was
   empty; the report lists the one removed import and its unused theorem/node.
   Read `dag/units/sk-prop-sf-open-closed-triangle.json`: its statement and single
   geometric-stalk step are unchanged; its `realized` entries are already empty
   in the baseline. No unit realization or route is removed by this delivery.

5. **DAG agreement — pass.** Read the item and all four original dependency
   records, and the relevant Lean implementations. Only `proof`, `proof_deps`
   and `proof_origin` differ in the delivered node. The union of the steps'
   `uses` is exactly `proof_deps`: the affine basis, closed-lift construction and
   filteredness. Each is used by the code or its displayed ind-etale instance.
   The immutable node statement and its conceptual stability citation remain
   unchanged. There are no new nodes to validate.

**Changes made in second reading:** appended this review and recorded independent
searches; no Lean or DAG repair was needed. The scratch axiom-check copy stays
outside the delivered `lean/` tree. Five existing holes are closed, zero holes
are added, and zero are split off; transitive upstream holes remain as reported.
