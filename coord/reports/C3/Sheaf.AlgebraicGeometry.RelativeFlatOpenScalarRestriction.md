## What changed

Proved `AlgebraicGeometry.Scheme.relativeFlat_open_scalarRestriction` with its statement and
public imports unchanged. Added two proved support modules:
`Sheaf.AlgebraicGeometry.InverseImageStructureStalkIso` and
`Sheaf.AlgebraicGeometry.OpenScalarRestrictionStalkCriterion`.

The inverse-image stalk isomorphism is transported between the two sheaf pullback
constructions by uniqueness of left adjoints. Its compatibility with `f.stalkMap`
is proved on germs using the adjunction unit identities. The main theorem applies
`relative_flat_module_stalk`, proves the scalar-tower law explicitly, and transports
flatness across the inverse stalk-ring isomorphism.

The open-site criterion uses exact extension by zero of an arbitrary localized short
complex. Tensor exactness holds on stalks inside U by flatness, and outside U because
the extended middle term is zero. Exact restriction, the natural tensor-restriction
comparison and the invertible extension/restriction unit return exactness to the
localized site. Private proved helpers identify scalar-restricted stalk actions on
common-neighborhood germs and perform this short-complex argument. This retains
the original unit route and handles empty opens and zero modules.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.relativeFlat_open_scalarRestriction`
(`lem-pc-relative-flat-open-scalar-restriction`).

Also proved both new support declarations:
`AlgebraicGeometry.Scheme.exists_inverseImageStructure_stalk_iso`
(`lem-pc-inverse-image-structure-stalk-iso`) and
`AlgebraicGeometry.RingedSpace.isFlat_open_scalarRestriction_of_stalks`
(`lem-pc-open-scalar-restriction-stalk-criterion`).

No sorry remains in any delivered module; no new hole is added. This is a proof
from existing library declarations, including the still-deferred
`SheafOfModules.exists_open_localized_tensor_natural`
(`lem-pc-open-localized-tensor-natural`), rather than an assertion that every
transitive dependency is now sorry-free. All three modules compiled together
locally. The delivery dry run performs the additional declaration and axiom probe.

## No longer needed

Removed the item's direct proof imports of `Sheaf.Topology.InverseImageStalk`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor`, and
`Sheaf.Algebra.Homology.ModuleStalkExact`; they remain needed through the new
proved support modules. No public import of the existing item was removed and no module is claimed
as globally pruned. All the original mathematical ingredients remain needed.
The old proof-dependency alias `lem-weil-pbc-module-stalk-tensor` is replaced
by `lem-pc-ringed-space-module-stalk-tensor`, which records the same module's
actual `stalkTensorIso` declaration. The subspace-equivalence/open-restriction
stalk route is unnecessary: the proof uses extension by zero instead.
In particular `Sheaf.AlgebraicGeometry.ModuleRestrictionStalkIso` is not imported.

The old parent proof_deps entries no longer directly used are
`lem-weil-pbc-topological-inverse-image-stalk`, `lem-weil-pbc-module-stalk-tensor`,
`lem-weil-pbc-module-stalk-exact`, and `def-pc-flat-sheaf-modules`. The support nodes
retain their ingredients transitively; the flatness definition remains in the statement.
The second reading also removed redundant public imports
`Mathlib.Topology.Sheaves.Stalks` and `Mathlib.Topology.Sheaves.Module` from the new
support modules, without removing any transitively required module.

## Where the brief, the DAG or earlier work was wrong

No false statement, changed interface or forced adaptation was needed. The DAG
plan omitted the concrete comparisons between the two inverse-image constructions
and between the open-site tensor functors. The first is now proved by adjunction
uniqueness; the second is supplied by the existing natural tensor-restriction
statement. Rather than transporting a monoidal structure across the subspace site
equivalence, the open-site proof uses exact extension by zero and its invertible unit.

The local literature checkout contains citation lists but not the Stacks source text.
Read the authoritative online Tags 05NE, 0098 and 01CB to check the stalk-flatness,
pullback and tensor claims. The library's existing extension-by-zero declarations
supply the open-site argument. Mathlib searches via msearch (leanfinder, loogle,
grep) and local rg found the existing stalk, flatness and open-site ingredients;
LeanSearch returned Internal Server Error and is recorded as unavailable.

## New nodes

`lem-pc-inverse-image-structure-stalk-iso`: a proved ring-stalk isomorphism and
compatibility equation, with no module or flatness hypothesis. This is only the
structure-map comparison used in the parent scalar-tower argument.

`lem-pc-open-scalar-restriction-stalk-criterion`: a proved general ringed-space
criterion, taking flatness of the scalar-restricted stalks on U as hypothesis.
It does not assume or establish affine-local relative flatness; the parent supplies
that hypothesis with the existing relative-stalk theorem. Its proof is the
extension-by-zero short-complex argument described above. No change record is needed.

## Second reading by C3

1. Compared the sole existing module with the repository using diff. Its entire
   declaration signature and public imports are byte for byte unchanged; only the
   proof and proof imports differ. The other two modules are new proved support
   statements. No definition, target, or existing interface changes. Verdict: pass.
2. Read all three proofs and checked for sorry, axiom, unsafe, opaque, extern and
   implemented_by: none. Compiled the delivery in import order. The explicit
   #print axioms check and delivery probe verify the permitted axiom boundary;
   sorryAx from existing deferred dependencies is distinguished from a new hole.
   The inverse-image support theorem has exactly propext, Classical.choice and
   Quot.sound; the parent and open criterion additionally have sorryAx from existing
   dependencies. All module objects are concrete constructions. The chosen tensor comparisons
   and adjunction are used only inside theorem proofs, not as new public data.
   MonoidalPreadditive is a Prop class. Verdict: pass.
3. No statement is split off with sorry. Read both proved support statements and
   their complete docstrings: the first compares ring stalks without flatness; the
   second reduces flatness on an open to scalar-restricted stalk flatness. Neither
   restates the parent. Checked the empty carrier/open, U equal to X, zero module
   and zero coefficient ring: the proofs impose no nonzero assumption. Independent
   msearch loogle/leanfinder/grep and local rg found the ingredients already used,
   including rTensor_shortComplex_exact and left-adjoint uniqueness, but no shorter
   public theorem with either support statement. Verdict: pass.
4. Read from the parent downward through the support modules. The scalar-tower
   comparison and extension-by-zero short-complex argument are real reductions.
   Removed redundant public imports Mathlib.Topology.Sheaves.Stalks from the
   inverse-image module and Mathlib.Topology.Sheaves.Module from the open criterion;
   their required declarations are already available through the public statement
   imports. All other public imports supply statement notions. The old direct
   proof dependencies no longer listed in the parent's proof_deps are
   lem-weil-pbc-topological-inverse-image-stalk, lem-weil-pbc-module-stalk-tensor,
   lem-weil-pbc-module-stalk-exact, and def-pc-flat-sheaf-modules. Their ingredients
   remain used below the support nodes (the tensor alias is corrected as reported),
   so no globally pruned module is claimed. Read sk-thm-picard-semicon's realized
   record: it is empty, and this subordinate local flatness proof changes no unit
   statement or realization and bypasses no realized step. Verdict: pass.
5. Checked all node statement records against their Lean signatures and every
   proof-dependency list against the written argument and the union of step uses.
   New nodes include source, searches, created, blueprint, chapter, unit and Lean
   records. The original node's statement and interface record are preserved.
   Verdict: pass.

Second reading changed only redundant imports, search documentation, and this
review/report clarification. No mathematical proof repair was needed. One original
hole is closed, zero new holes are added; both new support declarations are proved.
