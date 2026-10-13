## What changed

Closed three of the six existing proof holes in
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
`scalarFunctor_preservesFiniteColimits`, `scalarCohomologyExtMap_add`, and
`exists_scalarPullbackCoefficient`. Every existing signature, visibility, definition body,
and global attribute is unchanged. Added two fully proved private helpers:
`scalarForget_preservesFiniteColimits` and `scalarMap_pullback`.

Added plain proof-only imports of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` and
`Mathlib.CategoryTheory.Sites.PreservesSheafification`. The former supplies the proved
colimit preservation of the underlying abelian sheaf; the latter supplies the canonical
sheafification/forgetting comparison. Updated the node's proof and proof_origin and the
closed declarations' proof descriptions. No new public theorem or new node is introduced.

Colimit preservation follows through the conservative forgetful functor on scalar sheaves;
this avoids any new stalk theory. Additivity is the composition of three existing additive
maps. The coefficient map is explicitly transposed from the existing tensor-pullback unit,
whose scalar compatibility follows from the commutative triangle over Spec k.

The complete edited module compiled with lcompile.py without errors or warnings in
57.2 seconds. Separate sandbox experiments checked all three proofs while resolving
elaboration issues. No compile limit, kernel setting, or definition was changed. The
original module also compiled unchanged in 50.4 seconds. Empty schemes, empty opens, zero
coefficients, degree zero, and identity morphisms require no additional hypotheses.

## Proved and sorry left

Closed (3):
- `AlgebraicGeometry.Scheme.Modules.scalarFunctor_preservesFiniteColimits`.
- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_add`.
- `AlgebraicGeometry.Scheme.Modules.exists_scalarPullbackCoefficient`.

Added holes: none. Split-off statements: none. This is a partial proof delivery, not a
new decomposition. Additivity still depends on the original comparison existence theorem;
the pullback construction uses the existing tensor-pullback adjunction.

The three original whole-proof holes left, all on node
`def-sc-field-linear-module-cohomology-operations`, are:
- `AlgebraicGeometry.Scheme.Modules.exists_moduleExtEquiv`.
- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul`.
- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_bijective`.

Their existing signatures, source references, and complete proof docstrings are retained.
There is no sorry in a definition or in a private helper.

## No longer needed

None. No existing imports were removed; every original import serves existing definitions,
statements, or already completed proofs. The original node has no proof dependencies to
prune. No node or module becomes unnecessary through these three proofs. The colimit proof
uses the already proved upstream forgetful-functor result directly, without importing its
separate Sheaf statement module or adding a new obligation.

## Where the brief, the DAG or earlier work was wrong

The node records historical partial deliveries with larger remaining-hole counts; there
were six holes at the start of this item and three now remain. The preceding H3 report
recorded unsuccessful additivity attempts due to elaboration cost. This delivery closes
that hole with explicit intermediate equalities and fully specified Ext lemma arguments.
The finite-colimit docstring previously described a stalk argument; it now describes the
shorter implemented sheafification-and-reflection proof.

Read `dag/units/sk-prop-av-cube.json`: this node realizes no unit statement or proof step,
and no unit route changes. No mathematical statement error, interface repair, arbitrary
existence-witness construction, or forced adaptation is part of this delivery.


## Second reading by D2

1. **Interfaces — PASS.** Read the complete delivered module and its raw diff against
   the repository. All existing declaration signatures, visibility, definition bodies,
   and global attributes are unchanged. The declaration comparison also reports no
   signature, definition-body, or interface changes. The only additions are two proved
   private helpers and two plain proof-only imports. There are no change records or
   forced adaptations.
2. **Proofs and axioms — PASS.** Independently compiled the repaired complete module
   with lcompile.py, without errors or warnings, in 51.9 seconds. Checked the whole
   file for forbidden declarations and kernel bypasses: none. Exactly the three named
   original theorem holes listed above remain; no definition or private helper contains
   sorry. Checked every named declaration, including the private helpers, by appending
   #print axioms commands to a full scratch copy. All axioms are among propext,
   Classical.choice, Quot.sound, and sorryAx from existing open dependencies.
   The full axiom scratch copy compiled in 49.9 seconds. Both new helpers, the
   finite-colimit theorem, and the pullback-coefficient theorem have no sorryAx;
   additivity depends on the original exists_moduleExtEquiv hole.
   The moduleExtEquiv characterization determines its map on every homology class;
   the normalized tensor-pullback adjunction specifies its unit on all sections.
   The scalar coefficient is specified on all sections under a bijective adjunction.
   Thus the existing choices are determined constructions, not arbitrary witnesses
   of unproved existence.
3. **Split statements — PASS (none).** No new sorry or split-off statement is added.
   Read both private helpers: one transports colimits through sheafification, and the
   other is the structure-map naturality equality. They require no extra hypotheses
   in empty opens or schemes, zero coefficients, or identity morphisms. The remaining
   original holes retain their source references and natural-language proofs; none
   has a quick replacement among the searched upstream and Sheaf declarations.
4. **Route, searches, and pruning — PASS.** The colimit proof uses the already proved
   upstream SheafOfModules.toSheaf colimit instance, reflected through forgetting
   k-modules. The coefficient proof explicitly constructs the k-linear unit and
   transposes it. The additive proof uses Mathlib's mapExactFunctor_add and comp_add;
   independent Lean Finder and Loogle/grep searches found no shorter missing result
   or general sheafCompose colimit theorem. Both new imports are needed only by
   proofs and are plain imports. Existing imports support the public constructions,
   their required category instances, or existing proofs. The node's old proof_deps
   is empty, so there are no old dependency nodes omitted from No longer needed.
   Read dag/units/sk-prop-av-cube.json and searched all unit records: this node realizes
   no unit statement or step, and no unit route is bypassed.
5. **DAG — PASS.** Compared the delivered JSON against the repository: only proof and
   proof_origin change, describing the three actual reductions. proof_deps remains
   empty, consistently with the direct use of proved library/Mathlib declarations.
   No new nodes, altered mathematical statements, or unsupported dependency removals
   occur. Historical earlier proof entries are retained; the new entry states the
   current three remaining obligations.

**Second-reader repair.** Initial independent compilations hit the unchanged 60-second
limit. Timing a full scratch copy identified expensive elaboration around the Ext
comparison. Replaced the additivity proof's intermediate rewrite by congrArg applied
directly to scalarExtMap, and enabled transparency-respecting backward elaboration
only inside that proof. The same three additive equalities prove the same statement;
no data definition, global option, compile limit, or kernel check changes. The repaired
complete module compiled successfully. No additional holes were closed or added by
this repair: this delivery still closes three of six original holes, with no split-offs
and no pruning.
