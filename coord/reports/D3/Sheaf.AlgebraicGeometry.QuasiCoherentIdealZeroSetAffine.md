## What changed

Proved `AlgebraicGeometry.Scheme.quasi_coherent_ideal_zero_set_affine`, all five clauses,
without changing its statement, universes, or public imports. Added the proved private
helper `stalk_surjective_iff_not_mem_support` to identify stalk surjectivity with the
complement of Mathlib's existing ideal-sheaf support. The argument lifts the germ of 1
and shrinks to an affine neighborhood in one direction; in the other direction it
lifts every restricted representative on an affine neighborhood off the support.
The affine formula, closedness, and closed-immersion range then follow from Mathlib.
Updated the declaration's proof docstring and the node's proof route and dependencies.
Added the proof-only import `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
for its already proved `ideal_eq_top_of_disjoint_support`.

Read the official Stacks sources [01HM](https://stacks.math.columbia.edu/tag/01HM),
[01HP](https://stacks.math.columbia.edu/tag/01HP), and
[01IN](https://stacks.math.columbia.edu/tag/01IN). The direct germ calculation is written
by D3; Mathlib supplies representation of germs, equality on smaller neighborhoods,
affine support formulas, and closedness. No unit statement or realized step is bypassed:
the item is below the realized nodes of `dag/units/sk-thm-p1.json`.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.quasi_coherent_ideal_zero_set_affine`
(node `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`). All five conjuncts are proved.
The private helper `stalk_surjective_iff_not_mem_support` is also proved in full.
No sorries remain in the item and no holes were added or split off.
The local single-file compile passes without warnings.

The proof covers the empty scheme (pointwise clauses vacuous), zero and unit ideals,
and arbitrary nonreduced schemes. It uses no domain, Noetherian, finite-generation,
or nonempty hypothesis. For the unit ideal the support is empty and every stalk map
is surjective; for the zero ideal every point lies in the support and no stalk inclusion
is surjective. No new unproved statement or chosen construction was introduced.

## No longer needed

Removed proof-only imports:

- `Sheaf.Algebra.Homology.ModuleStalkExact`.
- `Sheaf.AlgebraicGeometry.Coherent`.
- `Sheaf.Topology.PresheafModuleStalkFunctor`.

Removed from this node's proof dependencies:

- `lem-weil-pbc-module-restriction-open-immersion-colimits`
  (`Mathlib.AlgebraicGeometry.Modules.Sheaf`: no restriction transport is needed).
- `pqf-def-coherent` (`Sheaf.AlgebraicGeometry.Coherent`: no coherence predicate is used).
- `def-weil-pbc-module-stalk` (`Sheaf.Topology.PresheafModuleStalkFunctor`: the general
  presheaf-module functor is unnecessary; the underlying Mathlib germ API is used through
  the already public `Sheaf.Algebra.Homology.ModuleStalkFunctor`).
- `lem-weil-pbc-module-stalk-exact` (`Sheaf.Algebra.Homology.ModuleStalkExact`: only
  injectivity is needed and Mathlib directly proves it for the underlying stalk map).
- `lem-weil-pbc-spec-domain-stalks-function-field`
  (`Mathlib.AlgebraicGeometry.StructureSheaf`: no stalk-ring localization computation).
- `lem-weil-pbc-spec-module-tilde-sections`
  (`Mathlib.AlgebraicGeometry.Modules.Tilde`: no tilde calculation).
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
  (`Mathlib.AlgebraicGeometry.Modules.Tilde`: no counit or adjunction).
- `lem-weil-pbc-spec-tilde-stalk-localization`
  (`Mathlib.AlgebraicGeometry.Modules.Tilde`: no localized module).
- `lem-weil-pbc-quasi-coherent-ideal-closed-subscheme`
  (`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: no separate existence argument).

The last node's construction is still used inside the existing definition `K.toModules`;
its module stays available through the unchanged public ideal-module import. Likewise
Mathlib modules above may remain transitively imported for existing definitions.
These are removals from this item's direct proof route, not claims that no other target
needs them. Kept the affine-point and closed-immersion zero-locus nodes, using their
Mathlib matches. Added the existing `lemma-nagata-ideal-unit-off-support` dependency.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and unchanged. The old proof plan and docstring required
unnecessary transport, tilde adjunction, and stalk localization calculations.
Mathlib's affine-local support plus the library's section-image description of
`K.toModulesι` permit the shorter complete germ proof. The former full exactness
import is unnecessary for sectionwise inclusions. The local `literature/stacks-project`
checkout described by the DAG is absent on this machine, so the official tag pages
were read instead. No definitions, target statements, or unit routes were changed.

## Second reading by D3

1. Compared the delivered Lean module with the repository version. The theorem signature and all existing declaration statements are byte-for-byte unchanged; only proof text, imports, and the proof route metadata changed.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no `sorry`s, axioms, unsafe declarations, or hollow definitions in the delivered module. The helper and target use only the permitted standard axioms through Mathlib.
3. Checked the direct germ helper and the five conjuncts against the existing Mathlib APIs and edge cases (empty, zero, and unit ideals). No new statement was split off, and the helper is private and fully proved.
4. Verified the shorter route uses the existing affine support and ideal-unit-off-support results, while preserving the unit's realized route. The removed imports and proof dependencies are listed above and are not used by the proof.
5. Compared the node's Lean declaration and proof metadata with the module. The target statement is unchanged and the node records the D3 route and dependencies; no definition or target review is reopened.

Changed only the report by adding this second-reading record; no Lean declarations or node statements were changed during this review.
