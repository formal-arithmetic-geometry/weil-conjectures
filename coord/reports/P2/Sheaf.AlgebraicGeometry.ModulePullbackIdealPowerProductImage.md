## What changed

Proved `AlgebraicGeometry.modulePullbackIdealPowerProductImage` with its signature unchanged.
Only the item module and its existing node are changed. All original public imports stay.

Repair of the duplicate-theorem return: removed the local private declarations
`AlgebraicGeometry.hom_zero_of_affine` and
`AlgebraicGeometry.subobject_le_of_affine_range`. Added the proof-only
`import all Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerImage` and applied the existing
private `AlgebraicGeometry.Scheme.subobject_le_of_affine_range` twice in the recursive-power
comparison. Lean's `import all` allows reuse of private declarations without changing their
visibility or modifying their module. Its existing zero-detection helper is reused transitively.
The import-cycle check accepts this dependency.

The three remaining private helpers prove monicity of recursive power inclusions, identify
these powers with `(J ^ n).toModules` over the structure sheaf using affine section ranges,
and transfer that isomorphism to ideal-module product inclusions. The main theorem applies
`AlgebraicGeometry.modulePullbackIdealProductImage` to `J ^ n`, uses the proved upstream
`Scheme.IdealSheafData.comap_pow`, and transports both image subobjects through the commuting
product isomorphisms. The proof covers exponent zero as well as positive exponents.

Other proof-only imports added are
`Sheaf.AlgebraicGeometry.ModulePullbackIdealProductImage`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
The node's proof, proof dependencies, and proof origin record the repaired route.
The unit `sk-thm-p1` does not realize this tool node as a step; its route is preserved.

Validation: `lcompile.py` compiles the repaired module without errors or warnings.
The delivery dry run performs the final checks. No definitions or existing signatures change,
and no other module is adapted.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.modulePullbackIdealPowerProductImage`
(node `lem-weil-pbc-module-pullback-ideal-power-product-image`).

No `sorry` remains in the delivered module. Zero holes are added and zero are split off.
The proof uses existing open dependencies, including
`AlgebraicGeometry.Scheme.Modules.ideal_times_quasiCoherent_affine_sections` and
`AlgebraicGeometry.modulePullbackIdealProductImage`; their import closure is not claimed
sorry-free. The reused affine-range helper is already proved.

## No longer needed

Removed these original direct proof imports:

- `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`.
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.

The route no longer directly invokes these planned nodes:

- `lem-weil-pbc-module-pullback-ideal-quotient`: upstream `comap_pow` suffices.
- `def-weil-pbc-coherent-formal-module`: its definitions remain statement dependencies.
- `lem-weil-pbc-module-pullback-affine-sections`.
- `lem-weil-pbc-module-pullback-quasi-coherent`.
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`.

These are removed direct imports and proof dependencies, not claims of pruning the entire
transitive target closure. In particular, the newly reused closed-immersion module imports
some of this theory for its own proofs. No public import is removed.

The repair also removes both duplicated private helpers, reusing the existing affine-range
comparison and its zero-detection proof rather than proving those facts again.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery and second reading incorrectly concluded that the existing private
helpers were unavailable. Lean's module system supports `import all`, already used elsewhere
in this library, so both duplicated proofs can and now do reuse the existing theory.
This repairs the landing refusal for both named duplicate declarations without changing
any statement, altering another group's module, or adding a theorem under a different name.

The original affine tensor-generator route can be shortened through the existing one-power
image theorem after comparing recursive powers to ideal-data powers. The local literature
checkout lacks `literature/stacks-project/coherent.tex`; the previous work read Tag 0887
at https://stacks.math.columbia.edu/tag/0887. The source and statement stay unchanged.

## Second reading by P2

1. Interface: PASS. Compared the sole delivered Lean module against the repository with
   `diff -u`. The existing theorem signature and docstring are byte-for-byte unchanged;
   all five public imports are unchanged. The additions are three private proved helpers
   and proof-only imports. No definition, target, or other module is changed, and no
   change record is required. Compared the node JSON as well: only `proof`, `proof_deps`
   and `proof_origin` differ.
2. Proof and axioms: PASS. Compiled the delivered file with `lcompile.py` without errors
   or warnings. Regenerated the stale scratch axiom-check copy from the actual repaired
   module, removing the obsolete duplicated helper proofs from that scratch copy.
   `#print axioms` for `power_mono` and `product_iso` shows only `propext`,
   `Classical.choice`, and `Quot.sound`; for `power_subobject_eq` and
   `modulePullbackIdealPowerProductImage` it additionally shows `sorryAx`, as expected
   from the existing open affine-sections and one-power image statements. The delivered
   module contains no `sorry`, forbidden declaration, or definition choosing data from
   an unproved existence theorem. The isomorphisms are proved existential witnesses
   used inside proofs, constructed from equality of subobjects.
3. Split statements and edge cases: PASS. There are no split-off statements or new nodes.
   Read all three private helper proofs and the reused affine-range comparison. The power
   comparison treats zero separately and positive exponents by the exact affine range
   formula; monicity covers zero and one explicitly. Product transport needs only an
   isomorphism commuting with the structure-sheaf maps, so adds no flatness assumption.
   Zero/unit ideals, zero modules, empty opens, and exponent zero satisfy the same
   identities. Independent Lean Finder search for tensor-product multiplication images
   returned module-level range formulas, not a replacement for this sheaf-power reduction;
   Loogle found `imageSubobject_iso_comp`, which the proof already uses. Independent
   `rg` searches of both library roots and Mathlib found no existing recursive-power
   comparison or power-monicity theorem that replaces these helpers. The former duplicate
   affine-range and zero-detection helpers are absent from the delivered module.
4. Route and pruning: PASS. Checked the existing one-power image theorem, the affine
   recursive-power statement, the proved upstream `comap_pow`, and the reused private
   helper in `ClosedImmersionIdealPowerImage`. The proof uses their exact conclusions
   and then transports image subobjects by isomorphisms. Checked the quotient computation
   in [Stacks Tag 0887](https://stacks.math.columbia.edu/tag/0887). All new imports are
   proof-only and supply a used theorem, helper, or quasi-coherence instance. Every old
   proof dependency absent from the new list appears under `## No longer needed`.
   The five removed imports are direct pruning only; no transitive closure pruning is
   claimed. Read `dag/units/sk-thm-p1.json`: neither this tool node nor any removed
   dependency is a realized statement or step of that unit, and the unit record stays
   unchanged. The route is a real reduction, not a restatement of the original hole.
5. DAG: PASS. The four recorded proof steps match monicity/affine-power comparison,
   product transport, the one-power theorem and `comap_pow`, and final image transport.
   `proof_deps` is exactly the union of the steps' `uses`; the closed-immersion node
   records the module supplying the reused helper rather than claiming that its main
   theorem is applied. The original node statement and Lean record remain unchanged.

Second reading changed no delivered Lean proof or node: they passed as written. Added
this independent review and refreshed the scratch axiom check. Confirmed one original
hole closed (`AlgebraicGeometry.modulePullbackIdealPowerProductImage`), zero holes added,
and zero statements split off; existing dependency holes remain explicitly acknowledged.
