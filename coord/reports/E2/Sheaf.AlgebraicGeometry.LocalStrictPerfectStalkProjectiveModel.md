## What changed

Proved `AlgebraicGeometry.Scheme.exists_localStrictPerfect_stalk_projective_model`
without changing its signature. Construct the model by the existing
`AlgebraicGeometry.openModuleStalkFunctor`. A proved private helper
`AlgebraicGeometry.Scheme.openStalk_free_finite` obtains finite generation from
finite coproducts and the unit-stalk isomorphism. Each strict-perfect retraction
then gives finite generation and projectivity. Exact derived functors transport
the local comparison; the existing restriction-stalk extension isomorphism and
invertible scalar-extension adjunction unit identify the resulting complex with
the ambient stalk complex. The two derived morphism universes remain independent.

Added proof imports of OpenModuleStalkFreeProjective,
Modules.RestrictionStalkExtensionIso, IdealModuleProductStalk,
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf,
Mathlib.Algebra.Category.ModuleCat.Biproducts. Updated the item's DAG proof
and proof dependencies to reflect these arguments.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_localStrictPerfect_stalk_projective_model`
(node `lem-sc-local-strict-perfect-stalk-projective-model`).
No `sorry` remains in the item; no holes were added and nothing was split off.
The private finite-generation helper is fully proved. Compilation passed without
warnings. The zero-rank case is handled by the finite empty product, and no
boundedness or projectivity of the arbitrary global representative G is used.

## No longer needed

Removed the original proof import `Sheaf.Algebra.Homology.ModuleStalkExact`
and direct dependency `lem-weil-pbc-module-stalk-exact`: exactness is supplied by
OpenModuleStalkFunctor. Removed direct proof dependencies
`def-weil-pbc-free-module`, `def-weil-finitely-generated-module` and
`def-weil-pbc-projective-module`; the finite-product and retraction calculations
use Mathlib directly. Their statement dependencies are preserved unchanged.
No other module is claimed to leave the target closure: shared dependencies may
still be needed elsewhere. Temporary exploratory imports of
WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk and
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor were removed.

Removed the redundant proof import
`Mathlib.CategoryTheory.Adjunction.FullyFaithful` during the second reading.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt had no proof changes. The DAG's germ and localization
steps were mathematically sound but omitted the usable existing open-stalk,
free-projectivity and restriction-stalk interface nodes. Those existing proved
tools suffice; no new mathematical statement is needed. The unit route is
preserved: this is the same strictly-perfect stalk construction, not a replacement
of any unit step. The tools from the picard-framework and proper-base-change
units are generic stalk interfaces; they do not bypass the cube unit's route.

## Second reading by E2

1. **Unchanged interface: pass.** Diffed the sole delivered Lean module against
   the repository. The complete signature of
   `AlgebraicGeometry.Scheme.exists_localStrictPerfect_stalk_projective_model`
   is byte-for-byte identical, including all three derived-category instance
   assumptions, the independent universes `v` and `w`, arbitrary `G`, and all
   three conclusion clauses. There are no definitions or forced adaptations.
   The only added declaration is a fully proved private finite-generation helper.
2. **Proof and axioms: pass.** Compiled the module cleanly through `lcompile.py`.
   A scratch copy with `#print axioms` for the public theorem reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no `sorry` or forbidden declaration in the delivery. The actual
   witness is the explicit functor applied termwise to `P`, not data selected
   from an unproved existence theorem. The unit-stalk isomorphism extracted from
   `ideal_module_product_stalk` is from a proved theorem, and its germ equation
   determines the identification; the imported restriction comparison is also
   proved. The retraction equation proves the required surjectivity explicitly.
3. **Split statements and edge cases: pass.** Nothing is split off and there are
   no new nodes or new holes. Read the private helper: the unit-stalk comparison,
   finite coproduct preservation, reindexing to `Fin m`, and `biproductIsoPi`
   prove exactly its finite-generation assertion. Checked `m = 0`, zero terms,
   arbitrary unbounded `G`, and the absence of any `a ≤ b` requirement. An empty
   scheme has no input point. Searched the open-stalk modules, upstream modules,
   and Mathlib module-sheaf files for finite-stalk/free-stalk results; found no
   existing finite-generation declaration replacing this calculation. An
   additional Loogle search `Module.Finite (_ → _)` returned no hits.
4. **Route and pruning: pass, one redundant import repaired.** Read
   `IsStrictlyPerfect`, `openModuleStalkFunctor`, `openModuleStalk_free_projective`,
   `ideal_module_product_stalk`, `nonempty_restriction_stalk_extension_iso`, and
   `Modules.overEquivFunctorObjUnitIso`. The proof uses their statements directly:
   bounds are preserved by the functor; retractions give finite projective terms;
   exact derived functors carry `eP` and `eG`; `overFunctorEquiv`, scalar
   restriction of the extension comparison, and the invertible adjunction unit
   give a chain isomorphism to the specified ambient stalk complex. No global
   finiteness of `G` is assumed. Read the sources
   [08C4](https://stacks.math.columbia.edu/tag/08C4),
   [08CM](https://stacks.math.columbia.edu/tag/08CM),
   [01AG](https://stacks.math.columbia.edu/tag/01AG), and
   [00A0(3)](https://stacks.math.columbia.edu/tag/00A0): strict perfectness,
   local representation, exact stalks, and open restriction agree with this
   argument. Checked `dag/units/sk-prop-av-cube.json`: this auxiliary stalk
   construction leaves the cube theorem's route and `realized` record unchanged.
   The imported nodes from other units are generic stalk tools. Tested removal
   of each of the six new proof imports in separate scratch copies: five fail
   with missing declarations or instances, while removing
   `Mathlib.CategoryTheory.Adjunction.FullyFaithful` compiles cleanly. Removed
   that redundant import. `No longer needed` names every old direct dependency
   absent from the new proof; no whole module is claimed unreachable.
5. **DAG agreement: pass.** JSON comparison shows only `proof`, `proof_deps`, and
   `proof_origin` changed. The four steps describe the explicit construction,
   finite-product calculation, retractions, and derived/chain comparisons in
   the Lean code. The dependency list is exactly the union of their `uses`.
   Read the statements of the four imported stalk interface nodes; they supply
   the properties used. The original statement, statement dependencies,
   blueprint, unit, and Lean signature record are unchanged.

Second-reading changes: removed the redundant FullyFaithful proof import,
added a source and proof docstring to the private finite-generation helper,
and recorded this review. No mathematical proof or public interface was changed.
