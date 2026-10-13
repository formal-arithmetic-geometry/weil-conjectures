## What changed

Proved `AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_zero_globalSections`
in `Sheaf.AlgebraicGeometry.ScalarPullbackZeroGlobalSections`, with its signature and
existing docstring unchanged. Added five proved private helpers, with no new imports:
`section_representative`, `extMk_augmentation`, `scalar_ext_section`,
`scalar_ext_evaluation`, and `homEquiv_unique`. Two private local instances provide
the recorded scalar-sheaf monoidal and Ext structures. Elaboration options are scoped
to individual declarations; the interface checker reports no interface change.

The proof follows the node's existing route. Extend a top section by restriction and
use `SheafOfModules.unitHomEquiv` to represent it by a module morphism from the structure
sheaf. The defining cocycle formula in `exists_moduleExtEquiv`, applied to the
augmentation of an injective resolution, identifies the degree-zero class with
`Ext.mk₀` of that morphism. Restrict scalars and compose with `scalarUnitMorphism`.
The constant-sheaf adjunction then evaluates the scalar Ext representative to the
original section. Expand the cohomology pullback; exact inverse image preserves mk₀,
and degree-zero Yoneda composition is morphism composition. Unfold the normalized
constant-unit isomorphism and use uniqueness of left adjoints to identify the target
constant adjunction with the composite adjunction. Finally,
`exists_scalarPullbackCoefficient` identifies its top component with the tensor-pullback
unit, and the restriction in `tensorPullbackTopSection` is the identity on the top open.

The private `extMk_augmentation` proof is adapted from the proved private helper of the
same name in `Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonNormalization`;
its basis is Mathlib's `InjectiveResolution.extMk_hom`. The private adjunction helper
uses Mathlib's `Adjunction.homEquiv_leftAdjointUniq_hom_app`, as in the existing proof
in `ScalarUnitClassPullback`. Neither module is imported.

Searches: Lean Finder found the generic degree-zero Ext/Hom equivalences and injective
resolution cohomology-class equivalences; Loogle found `Ext.mk₀_comp_mk₀`; grep and rg
found the generic unit-section evaluation and right-derived-zero identities, but no
complete existing scalar pullback/global-sections compatibility theorem. The existing
class-of-one formula would provide an alternative reduction, but its module was absent
from the compiled snapshot; the direct cocycle argument needs no such dependency.

Validation: the complete module compiles without errors or warnings using `lcompile.py`
(33.6 seconds). All lines are at most 100 characters. The proof works for arbitrary
module coefficients, zero sections, and empty schemes; it assumes neither quasi-coherence
nor nonemptiness. The unit record `sk-prop-av-cube` has no realized node for this lower
comparison, and its statement and route are unchanged. The original two proof dependencies
are exactly the ones used, so no DAG route edit is needed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_zero_globalSections`
(node `lem-sc-scalar-pullback-zero-global-sections`).

No `sorry` remains in the delivered module. No holes or new nodes were added.
This is a proof from the existing comparison specifications, not a decomposition into
new unproved statements. Existing upstream holes are unchanged.

## No longer needed

None. The original public import
`Sheaf.AlgebraicGeometry.ScalarGlobalSectionsComparison` is needed by the statement.
Both original DAG proof dependencies remain used:
`def-sc-scalar-global-sections-comparison` and
`def-sc-field-linear-module-cohomology-operations`.
No module or node is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The plan was sufficient as written.
The first dry run classified file-level elaboration commands as an interface change;
these were replaced by declaration-scoped options and private local instances. The
interface checker now reports an empty list of changes.
The local checkout does not contain the recorded literature files, so source references
were checked at the official Stacks pages: [01DZ](https://stacks.math.columbia.edu/tag/01DZ),
[0FKV](https://stacks.math.columbia.edu/tag/0FKV), and
[0096](https://stacks.math.columbia.edu/tag/0096). Tag 01DZ supplies the injective-resolution
definition of module cohomology, and 0096 supplies the module pullback/pushforward adjunction. Tag 0FKV
concerns cup/Čech compatibility rather than this stand-alone degree-zero pullback identity;
no use of that additional compatibility is needed in this proof.


## Second reading by Q3

1. Compared the sole delivered Lean module with the repository version. The existing
   theorem signature and docstring are byte-for-byte identical. The sole public import
   is unchanged; the added helpers and local instances are private. There are no
   delivered definition changes, change records, or adapted consumer modules. Verdict: pass.
2. Independently compiled the entire module through `lcompile.py`, without errors or
   warnings (36.7 seconds). Checked the source for holes and forbidden declarations.
   The five helpers have complete proofs; no `sorry`, axiom, unsafe declaration, opaque
   declaration, external implementation, or hollow definition was added. Also compiled
   a scratch copy with `#print axioms` for the main theorem: `propext`,
   `Classical.choice`, `Quot.sound`, and inherited `sorryAx` from open dependencies.
   This closes the local hole, not the remaining upstream proof obligations.
   The resolution and section representatives are real constructions. The chosen
   comparison equivalence is fixed on all cocycles by its specification; the chosen
   coefficient morphism is fixed by its adjoint on every section. No arbitrary witness
   of an unproved mere existence assertion is introduced. Verdict: pass.
3. No statements were split off and no holes were added. Read each private helper:
   restriction constructs the section representative, the augmentation computes mk-zero,
   the cocycle equation identifies the scalar representative, and the constant adjunction
   evaluates it. These work for zero coefficients and sections and empty schemes; no
   nonemptiness or quasi-coherence enters. Independent Lean Finder and Loogle searches
   for the augmentation formula found generic `extMk_hom` and Ext composition lemmas,
   not a public replacement. The matching project augmentation helper is private;
   importing its Cech normalization module would add an unrelated dependency. Verdict: pass.
4. Read the main proof from the final comparison back to the representative. It uses
   exact inverse image of mk-zero, ordinary degree-zero composition, uniqueness of
   left adjoints, and the specified tensor-pullback unit. Searched the project for
   degree-zero scalar and coefficient naturality results; no shorter complete theorem
   replaces this direct calculation without additional imports. The existing import
   supplies types and maps in the theorem's signature, so it must remain public.
   Both original proof-dependency nodes are used; the No longer needed section is
   complete. Inspected `sk-prop-av-cube.json`: this lower comparison realizes neither
   its statement nor a step, and no unit route or realization was changed. Verdict: pass.
5. Read `lem-sc-scalar-pullback-zero-global-sections.json` and its two dependency
   specifications. Its proof, proof_deps and agent proof_origin already describe the
   cocycle, scalar adjunction and tensor-unit calculation actually used here. The Lean
   statement matches its recorded declaration. There are no new nodes to validate.
   Verdict: pass.

Changes by the second reader: appended this independent review and verification evidence;
no Lean or DAG repair was needed.
